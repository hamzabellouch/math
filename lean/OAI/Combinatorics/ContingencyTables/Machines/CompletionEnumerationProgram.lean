import OAI.Combinatorics.ContingencyTables.Transport.BoxCompletion
import OAI.Combinatorics.ContingencyTables.Transport.FiniteGridWords
import OAI.Combinatorics.ContingencyTables.Dense.DenseCanonicalProgram

namespace OAI

/-! # Explicit free-box enumeration with binary completion tests -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open scoped BigOperators Classical

abbrev CompletionMargins := List ℕ×List ℕ

def completionEnumerationData (z : CompletionMargins) : GridEnumerationData :=
  ((zeroGrid z).map (fun _ => false),z.1.sum+1)

def completionEnumerationDataRealizer : Realizer completionEnumerationData := by
  let dims := composition zeroGridRealizer (map (constant false))
  let base : Realizer (fun z : CompletionMargins => z.1.sum+1) :=
    composition (composition first listSum) successor
  exact pair dims base

lemma polynomial_completionEnumerationData : PolynomialTime completionEnumerationDataRealizer := by
  unfold completionEnumerationDataRealizer
  exact polynomial_pair (polynomial_composition polynomial_zeroGrid
    (polynomial_map (polynomial_constant false)))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_listSum)
      polynomial_successor)

def completionCandidate (z : CompletionMargins×List ℕ) : Option MatrixCode :=
  acceptCompletion (z.1,unflattenGrid z)

def completionCandidateRealizer : Realizer completionCandidate :=
  composition (pair first unflattenGridRealizer) acceptCompletionRealizer

lemma polynomial_completionCandidate : PolynomialTime completionCandidateRealizer :=
  polynomial_composition (polynomial_pair polynomial_first polynomial_unflattenGrid)
    polynomial_acceptCompletion

/-- Rejected candidates remain as `none`, allowing later integer sums
to ignore them without adding a second enumeration or an ordering oracle. -/
def completionCandidates (z : CompletionMargins) : List (Option MatrixCode) :=
  (gridWords (completionEnumerationData z)).map (fun v => completionCandidate (z,v))

def completionCandidatesRealizer : Realizer completionCandidates :=
  composition (pair identity (composition completionEnumerationDataRealizer gridWordsRealizer))
    (mapWith completionCandidateRealizer)

def completionEnumerationMeasure (z : CompletionMargins) : ℕ :=
  gridStateCount (completionEnumerationData z)+weight z

theorem work_completionCandidates :
    WorkBound completionCandidatesRealizer completionEnumerationMeasure := by
  have hp : WorkBound completionEnumerationDataRealizer completionEnumerationMeasure :=
    work_of_polynomial polynomial_completionEnumerationData Polynomial.X (fun z => by
      simp only [completionEnumerationMeasure,Polynomial.eval_X]; omega)
  obtain ⟨p,hp'⟩ := hp
  have hg : WorkBound (composition completionEnumerationDataRealizer gridWordsRealizer)
      completionEnumerationMeasure := by
    apply work_composition ⟨p,hp'⟩ work_gridWords (Polynomial.X+p)
    intro z
    have hw := hp' z
    simp only [completionEnumerationMeasure,Polynomial.eval_add,Polynomial.eval_X]
    change gridStateCount (completionEnumerationData z)+weight (completionEnumerationData z)≤_
    change _≤p.eval (completionEnumerationMeasure z) at hw
    unfold completionEnumerationMeasure at hw
    omega
  unfold completionCandidatesRealizer
  apply work_then_polynomial _ (polynomial_mapWith polynomial_completionCandidate)
  exact work_pair (work_of_polynomial polynomial_identity Polynomial.X (fun z => by
    simp only [completionEnumerationMeasure,Polynomial.eval_X]; omega)) hg Polynomial.X
    (fun z => by simp only [completionEnumerationMeasure,Polynomial.eval_X]; omega)

lemma gridWords_finFunctions (xs : List Bool) (N q : ℕ) (hq : xs.length=q) :
    gridWords (xs,N+1)=List.ofFn (fun k : Fin ((N+1)^q) =>
      List.ofFn (fun i : Fin q => ((finFunctionFinEquiv.symm k) i).val)) := by
  rw [gridWords_eq_length xs (N+1) q hq]
  rfl

theorem completionCandidates_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j) :
    completionCandidates (marginCode R,marginCode P)=
      List.ofFn (fun k : Fin (((∑ i,R i)+1)^(m*n)) =>
        (BoxCompletion.decode R P htotal (∑ i,R i) (finFunctionFinEquiv.symm k)).map tableOutput) := by
  have hsum : (marginCode R).sum=∑ i,R i := by
    simp only [marginCode,List.sum_cons,List.sum_ofFn,Fintype.sum_option]
  have hlen : ((zeroGrid (marginCode R,marginCode P)).map (fun _ => false)).length=m*n := by
    simp only [zeroGrid,List.length_map,cellPairs,List.length_range,marginCode,
      List.tail_cons,List.length_ofFn]
  unfold completionCandidates completionEnumerationData
  rw [hsum,gridWords_finFunctions _ (∑ i,R i) (m*n) hlen,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_apply,completionCandidate]
  rw [unflattenGrid_code]
  exact BoxCompletion.acceptCompletion_eq R P htotal (finFunctionFinEquiv.symm k)

end ContingencyTables.DensePrograms

end OAI
