import OAI.Analysis.SeparableQuotients.Positive.ComplexSubspaces
import OAI.Analysis.SeparableQuotients.Positive.DualKernels
import OAI.Analysis.SeparableQuotients.Positive.ScalarBasis

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.ComplexTransfer
open Set TopologicalSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
local instance sequenceRealDualSubmoduleNormedGroup (space : Submodule ℝ (StrongDual ℂ X)) :
    NormedAddCommGroup space := Submodule.normedAddCommGroup space
local instance sequenceRealDualSubmoduleNormedSpace (space : Submodule ℝ (StrongDual ℂ X)) :
    NormedSpace ℝ space := Submodule.normedSpace space



theorem exists_near_unit_annihilating
    (E : Submodule ℝ (StrongDual ℂ X)) (hEcl : IsClosed (E : Set (StrongDual ℂ X)))
    (hEinf : ¬ FiniteDimensional ℝ E) (hE : ¬ HasSeparatedInfiniteSubspace E)
    (D : Finset X) {ε : ℝ} (hε : 0 < ε) :
    ∃ f g : E, ‖f‖ = 1 ∧ (∀ d ∈ D, (f : StrongDual ℂ X) d = 0) ∧
      ‖(g : StrongDual ℂ X) - Complex.I • (f : StrongDual ℂ X)‖ < ε := by
  let B : StrongDual ℂ X →L[ℝ] (D → ℂ) := ContinuousLinearMap.pi
    (fun d => (ContinuousLinearMap.restrictScalarsL ℂ X ℂ ℝ ℝ).flip d.val)
  let T := B.comp E.subtypeL
  let M : Submodule ℝ (StrongDual ℂ X) := E ⊓ B.ker
  have hME : M ≤ E := inf_le_left
  have hMcl : IsClosed (M : Set (StrongDual ℂ X)) := hEcl.inter B.isClosed_ker
  have hTinf := infiniteDimensional_ker_to_finite T hEinf
  have hMinf : ¬ FiniteDimensional ℝ M := by
    intro hh
    let := hh
    let J : T.ker →ₗ[ℝ] M :=
      { toFun := fun f => ⟨f.val.val, f.val.property, f.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    apply hTinf
    apply FiniteDimensional.of_injective (V₂ := M) J
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : M => (y : StrongDual ℂ X)) h
  obtain ⟨f, hf, g, hfg⟩ := exists_near_rotation_of_not_separated E hE M hME hMcl hMinf hε
  refine ⟨⟨f.val, hME f.property⟩, g, hf, ?_, hfg⟩
  intro d hd
  exact congrFun f.property.2 (⟨d, hd⟩ : D)

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.ComplexTransfer
open Set TopologicalSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
attribute [local instance] sequenceRealDualSubmoduleNormedGroup sequenceRealDualSubmoduleNormedSpace
variable (E : Submodule ℝ (StrongDual ℂ X)) (hEcl : IsClosed (E : Set (StrongDual ℂ X)))
    (hEinf : ¬ FiniteDimensional ℝ E) (hE : ¬ HasSeparatedInfiniteSubspace E)

def chooseNearPair (n : ℕ) (D : Finset X) : E × E := by
  let h := exists_near_unit_annihilating E hEcl hEinf hE D
    (show (0 : ℝ) < (1/2)^n by positivity)
  exact (h.choose, h.choose_spec.choose)

lemma chooseNearPair_spec (n : ℕ) (D : Finset X) :
    ‖(chooseNearPair E hEcl hEinf hE n D).1‖ = 1 ∧
    (∀ d ∈ D, ((chooseNearPair E hEcl hEinf hE n D).1 : StrongDual ℂ X) d = 0) ∧
    ‖((chooseNearPair E hEcl hEinf hE n D).2 : StrongDual ℂ X) -
      Complex.I • ((chooseNearPair E hEcl hEinf hE n D).1 : StrongDual ℂ X)‖ < (1/2:ℝ)^n := by
  exact (exists_near_unit_annihilating E hEcl hEinf hE D
    (show (0 : ℝ) < (1/2)^n by positivity)).choose_spec.choose_spec

def nearState : ℕ → (ℕ → E) × Finset X
  | 0 => (fun _ => 0, chosenPrefixNormers (fun _ => (0 : StrongDual ℂ X)) 0)
  | n+1 =>
    let s := nearState n
    let v := (chooseNearPair E hEcl hEinf hE n s.2).1
    let f := Function.update s.1 n v
    (f, s.2 ∪ chosenPrefixNormers (fun m => (f m : StrongDual ℂ X)) (n+1))

def nearPair (n : ℕ) : E × E :=
  chooseNearPair E hEcl hEinf hE n (nearState E hEcl hEinf hE n).2

def nearNormers (m : ℕ) : Finset X :=
  chosenPrefixNormers (fun n => ((nearState E hEcl hEinf hE m).1 n : StrongDual ℂ X)) m

lemma nearState_value (n m : ℕ) (hn : n < m) :
    (nearState E hEcl hEinf hE m).1 n = (nearPair E hEcl hEinf hE n).1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hnm : n = m
    · subst n
      simp only [nearState, nearPair, Function.update_self]
    · have hnm' : n < m := by omega
      simpa only [nearState, Function.update_of_ne hnm] using ih hnm'

lemma nearState_mono : Monotone (fun n => (nearState E hEcl hEinf hE n).2) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_union_left

lemma nearNormers_subset (m : ℕ) :
    nearNormers E hEcl hEinf hE m ⊆ (nearState E hEcl hEinf hE m).2 := by
  cases m with
  | zero => exact Finset.Subset.refl _
  | succ m => exact Finset.subset_union_right

include hEcl hEinf hE



theorem exists_near_prefix_sequence :
    ∃ (f g : ℕ → E) (D : ℕ → Finset X),
      (∀ n, ‖f n‖ = 1) ∧ (∀ m d, d ∈ D m → ‖d‖ ≤ 1) ∧
      (∀ m (v : StrongDual ℂ X),
        v ∈ Submodule.span ℂ ((fun n => (f n : StrongDual ℂ X)) '' (Finset.range m : Set ℕ)) →
          ∃ d ∈ D m, ‖v‖ ≤ 2 * ‖v d‖) ∧
      (∀ m n, m ≤ n → ∀ d ∈ D m, (f n : StrongDual ℂ X) d = 0) ∧
      (∀ n, ‖(g n : StrongDual ℂ X) - Complex.I • (f n : StrongDual ℂ X)‖ < (1/2:ℝ)^n) := by
  refine ⟨fun n => (nearPair E hEcl hEinf hE n).1,
    fun n => (nearPair E hEcl hEinf hE n).2, nearNormers E hEcl hEinf hE,
    fun n => (chooseNearPair_spec E hEcl hEinf hE n _).1, ?_, ?_, ?_,
    fun n => (chooseNearPair_spec E hEcl hEinf hE n _).2.2⟩
  · intro m d hd
    exact (chosenPrefixNormers_spec _ m).1 d hd
  · intro m v hv
    apply (chosenPrefixNormers_spec _ m).2 v
    apply Submodule.span_mono (t :=
      (fun n => ((nearState E hEcl hEinf hE m).1 n : StrongDual ℂ X)) '' (Finset.range m : Set ℕ)) _ hv
    rintro w ⟨n, hn, rfl⟩
    exact ⟨n, hn, congrArg Subtype.val (nearState_value E hEcl hEinf hE n m (Finset.mem_range.mp hn))⟩
  · intro m n hmn d hd
    apply (chooseNearPair_spec E hEcl hEinf hE n _).2.1
    exact nearState_mono E hEcl hEinf hE hmn (nearNormers_subset E hEcl hEinf hE m hd)

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

end

end OAI
