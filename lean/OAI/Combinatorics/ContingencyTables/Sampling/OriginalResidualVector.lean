import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableCardinality
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalBoxLaw
import OAI.Combinatorics.ContingencyTables.Machines.ResidualWeightProgram
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLawEmbedding

namespace OAI

/-! # Explicit integer correction weights on the original-table box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

/-- Candidate matrices, ordinary numerators, denominator/branch size, and table count. -/
abbrev ResidualVectorCache := (List (Option MatrixCode)×List ℕ)×((ℕ×ℕ)×ℕ)

def residualVectorEntry (z : ResidualVectorCache×ℕ) : ℕ :=
  if (z.1.1.1.getD z.2 none).isSome then
    ResidualWeightPrograms.count (z.1.2.1,(z.1.2.2,z.1.1.2.getD z.2 0)) else 0

def residualVectorEntryRealizer : Realizer residualVectorEntry := by
  let candidate : Realizer (fun z : ResidualVectorCache×ℕ => z.1.1.1.getD z.2 none) :=
    composition (pair (composition (composition first first) first) second) (getDFast none)
  let numerator : Realizer (fun z : ResidualVectorCache×ℕ => z.1.1.2.getD z.2 0) :=
    composition (pair (composition (composition first first) second) second) (getDFast 0)
  let input : Realizer (fun z : ResidualVectorCache×ℕ =>
      (z.1.2.1,(z.1.2.2,z.1.1.2.getD z.2 0))) :=
    pair (composition (composition first second) first)
      (pair (composition (composition first second) second) numerator)
  exact choose (composition candidate FirstSuccessProgram.isSomeRealizer)
    (composition input ResidualWeightPrograms.countRealizer) (constant 0)

lemma polynomial_residualVectorEntry : PolynomialTime residualVectorEntryRealizer := by
  unfold residualVectorEntryRealizer
  exact polynomial_choose
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_second) (polynomial_getDFast none)) FirstSuccessProgram.polynomial_isSome)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
        (polynomial_composition (polynomial_pair
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
          polynomial_second) (polynomial_getDFast 0)))) ResidualWeightPrograms.polynomial_count)
    (polynomial_constant 0)

def residualVectorIndices (z : ResidualVectorCache) : List ℕ := List.range z.1.1.length

def residualVectorIndicesRealizer : Realizer residualVectorIndices :=
  composition (composition (composition first first) listLength) range

lemma polynomial_residualVectorIndices : PolynomialTime residualVectorIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition (polynomial_composition
    polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

def residualVector (z : ResidualVectorCache) : List ℕ :=
  (residualVectorIndices z).map (fun k => residualVectorEntry (z,k))

def residualVectorRealizer : Realizer residualVector :=
  composition (pair identity residualVectorIndicesRealizer) (mapWith residualVectorEntryRealizer)

lemma polynomial_residualVector : PolynomialTime residualVectorRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_residualVectorIndices)
    (polynomial_mapWith polynomial_residualVectorEntry)

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.ProfilePrograms
open DensePrograms
open scoped BigOperators Classical

lemma residualVector_ofFn {K : ℕ} (candidates : Fin K → Option MatrixCode)
    (counts : Fin K → ℕ) (Q T N : ℕ) :
    residualVector ((List.ofFn candidates,List.ofFn counts),((Q,T),N))=
      List.ofFn (fun k => if (candidates k).isSome then
        ResidualWeightPrograms.count ((Q,T),(N,counts k)) else 0) := by
  unfold residualVector residualVectorIndices
  rw [List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro k hk _
    have hK : k<K := by simpa only [List.length_map,List.length_range] using hk
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,residualVectorEntry,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,hK,dite_true,Option.getD_some]

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.OriginalBoxLaw
open ProfilePrograms DensePrograms OriginalTableBox
open scoped BigOperators Classical
noncomputable section

variable {m n Q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma index_injective : Function.Injective (index r c (le_refl (∑ i,r i))) := by
  intro X Y h
  exact (index_eq_iff r c _ X Y).mp h

/-- Invalid candidates carry zero; every feasible candidate carries exactly
its signed residual numerator after the proved nonnegative truncation. -/
lemma residualVector_actual (p : IntegerLaw (Table r c) Q) (fallback : Table r c)
    (T : ℕ) (hT : 0<T) :
    let _ : Nonempty (Table r c) := ⟨fallback⟩
    residualVector ((originalCandidates (List.ofFn r,List.ofFn c),
        List.ofFn ((p.push (index r c le_rfl)).count)),
        ((Q,T),originalCardinality (List.ofFn r,List.ofFn c)))=
      List.ofFn (fun k : Index m n (∑ i,r i) =>
        (tableAt r c k).elim 0 (fun X => IntegerResidualCorrection.count p T X)) := by
  let : Nonempty (Table r c) := ⟨fallback⟩
  dsimp only
  rw [candidates_code,originalCardinality_actual,residualVector_ofFn]
  apply congrArg List.ofFn
  funext k
  cases hk : tableAt r c k with
  | none => rfl
  | some X =>
    simp only [Option.map_some,Option.isSome_some,ite_true,Option.elim_some]
    have hindex := (tableAt_eq_some r c le_rfl k X).mp hk
    rw [←hindex,IntegerLaw.push_count_injective p _ (index_injective r c)]
    exact ResidualWeightPrograms.count_actual p T hT X

end
end ContingencyTables.OriginalBoxLaw

end OAI
