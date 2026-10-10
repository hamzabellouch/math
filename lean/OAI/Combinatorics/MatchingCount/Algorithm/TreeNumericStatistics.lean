import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeNumericMarking
import OAI.Combinatorics.MatchingCount.Algorithm.TreeStageStatisticsCorrect

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {E A : Type} [Fintype E] [LinearOrder E]
def extend (d : A) (f : E→A) (i : ℕ) : A :=
  if h:i<Fintype.card E then f (UnitRefresh.orderedEnum E ⟨i,h⟩) else d
lemma extend_index (d : A) (f : E→A) (e : E) : extend d f (index e)=f e := by
  unfold extend index
  rw [dite_eq_left ((UnitRefresh.orderedEnum E).symm e).isLt]
  exact congrArg f ((UnitRefresh.orderedEnum E).apply_symm_apply e)
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics

variable {E : Type} [Fintype E] [LinearOrder E]
lemma numericMarks_eq (s : Finset E) (m : E→Fin 3) :
    numericMarks s m=marksRep (Numbered.set s) (extend 0 m) := by
  simp only [numericMarks,marksRep,sort_set,List.map_map,Function.comp_def,extend_index]

lemma zero_numbered (s : Finset E) (m : E→Fin 3) :
    (∀ a∈Numbered.set s,extend 0 m a=0) ↔ ∀ e∈s,m e=0 := by
  constructor
  · intro h e he
    have hh:=h (index e) (Finset.mem_map.mpr ⟨e,he,rfl⟩)
    simpa only [extend_index] using hh
  · intro h a ha
    obtain ⟨e,he,rfl⟩:=Finset.mem_map.mp ha
    exact (extend_index 0 m e).trans (h e he)
lemma scalarA_numbered {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3) (i : Fin S) :
    scalarA (fun j=>Numbered.set (s j)) (fun j=>extend 0 (m j)) i=scalarA s m i := by
  by_cases h : ∀ e∈s i,m i e=0
  · have hh := (zero_numbered (s i) (m i)).mpr h
    simp only [scalarA,ite_eq_left h,ite_eq_left hh]
  · have hh : ¬∀e∈Numbered.set (s i),extend 0 (m i) e=0 := fun hh=>h ((zero_numbered _ _).mp hh)
    simp only [scalarA,ite_eq_right h,ite_eq_right hh]

lemma scalarD_numbered {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3) (r : E→ℚ) (i : Fin S) :
    scalarD (fun j=>Numbered.set (s j)) (fun j=>extend 0 (m j)) (extend 1 r) i=scalarD s m r i := by
  by_cases h : ∀ e∈s i,m i e=0
  · have hh := (zero_numbered (s i) (m i)).mpr h
    simp only [scalarD,ite_eq_left h,ite_eq_left hh]
    simp only [Numbered.set,Finset.prod_map,Numbered.embedding,Function.Embedding.coeFn_mk,extend_index]
  · have hh : ¬∀e∈Numbered.set (s i),extend 0 (m i) e=0 := fun hh=>h ((zero_numbered _ _).mp hh)
    simp only [scalarD,ite_eq_right h,ite_eq_right hh]

abbrev Reweights := List (ℕ×Fraction)
def reweight (x : Reweights×ℕ) : Fraction := ExecutableLadder.lookup (1,1) x
def reweightRealizer : Realizer reweight := ExecutableLadder.lookupRealizer (1,1) natEqual
lemma polynomial_reweight : PolynomialTime reweightRealizer := ExecutableLadder.polynomial_lookup (1,1) polynomial_natEqual
abbrev Inputs := (Reweights×(ℕ×List ℕ))×List (Marks ℕ)
def statistics (x : Inputs) : Fraction×List (ℕ×Fraction) := estimates reweight x
def statisticsRealizer : Realizer statistics := estimatesRealizer reweightRealizer natEqual
lemma polynomial_statistics : PolynomialTime statisticsRealizer := polynomial_estimates polynomial_reweight polynomial_natEqual

theorem statistics_post : ∃ p : Polynomial ℕ,∀ x : Inputs,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine statisticsRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine statisticsRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (statistics x)) :=
  TreePost.polynomial_compiles statisticsRealizer polynomial_statistics
end MatchingFPRAS.NumericMarking

end OAI
