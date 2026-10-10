import OAI.Analysis.SeparableQuotients.Positive.DualKernels
import OAI.Analysis.SeparableQuotients.Positive.ScalarBasis

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields
attribute [local instance] scalarDualSubmoduleNormedGroup scalarDualSubmoduleNormedSpace
variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def chooseUnitVector (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (D : Finset X) : F :=
  (exists_unit_annihilating_finite F hF D).choose

lemma chooseUnitVector_spec (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (D : Finset X) :
    ‖chooseUnitVector F hF D‖ = 1 ∧
      ∀ d ∈ D, (chooseUnitVector F hF D : StrongDual 𝕜 X) d = 0 :=
  (exists_unit_annihilating_finite F hF D).choose_spec


def normerState (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) : ℕ → (ℕ → F) × Finset X
  | 0 => (fun _ => 0, chosenPrefixNormers (fun _ => (0 : StrongDual 𝕜 X)) 0)
  | n+1 =>
    let s := normerState F hF x n
    let v := chooseUnitVector F hF (insert (x n) s.2)
    let f := Function.update s.1 n v
    (f, s.2 ∪ insert (x n) (chosenPrefixNormers (fun m => (f m : StrongDual 𝕜 X)) (n+1)))

def selectedVector (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) (n : ℕ) : F :=
  chooseUnitVector F hF (insert (x n) (normerState F hF x n).2)

def selectedNormers (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) (m : ℕ) : Finset X :=
  chosenPrefixNormers (fun n => ((normerState F hF x m).1 n : StrongDual 𝕜 X)) m

lemma normerState_value (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) (n m : ℕ) (hn : n < m) :
    (normerState F hF x m).1 n = selectedVector F hF x n := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hnm : n = m
    · subst n
      simp only [normerState, selectedVector, Function.update_self]
    · have hnm' : n < m := by omega
      simpa only [normerState, Function.update_of_ne hnm] using ih hnm'

lemma normerState_mono (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) :
    Monotone (fun n => (normerState F hF x n).2) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_union_left

lemma selectedNormers_subset_state (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) (m : ℕ) :
    selectedNormers F hF x m ⊆ (normerState F hF x m).2 := by
  cases m with
  | zero => exact Finset.Subset.refl _
  | succ m =>
    exact (Finset.subset_insert _ _).trans Finset.subset_union_right

lemma selectedVector_norm (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) (n : ℕ) :
    ‖selectedVector F hF x n‖ = 1 :=
  (chooseUnitVector_spec F hF _).1

lemma selectedVector_ann_test (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) (n j : ℕ) (hj : j ≤ n) :
    (selectedVector F hF x n : StrongDual 𝕜 X) (x j) = 0 := by
  apply (chooseUnitVector_spec F hF _).2
  by_cases hnj : j = n
  · subst j; exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply normerState_mono F hF x (show j+1 ≤ n by omega)
    exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)

lemma selectedVector_ann_normers (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) (m n : ℕ) (hmn : m ≤ n)
    (d : X) (hd : d ∈ selectedNormers F hF x m) :
    (selectedVector F hF x n : StrongDual 𝕜 X) d = 0 := by
  apply (chooseUnitVector_spec F hF _).2
  exact Finset.mem_insert_of_mem ((normerState_mono F hF x hmn)
    (selectedNormers_subset_state F hF x m hd))



theorem exists_normed_prefix_sequence
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : ¬ FiniteDimensional 𝕜 F) (x : ℕ → X) :
    ∃ (f : ℕ → F) (D : ℕ → Finset X),
      (∀ n, ‖f n‖ = 1) ∧ (∀ m d, d ∈ D m → ‖d‖ ≤ 1) ∧
      (∀ m (v : StrongDual 𝕜 X),
        v ∈ Submodule.span 𝕜 ((fun n => (f n : StrongDual 𝕜 X)) '' (Finset.range m : Set ℕ)) →
          ∃ d ∈ D m, ‖v‖ ≤ 2 * ‖v d‖) ∧
      (∀ m n, m ≤ n → ∀ d ∈ D m, (f n : StrongDual 𝕜 X) d = 0) ∧
      (∀ n j, j ≤ n → (f n : StrongDual 𝕜 X) (x j) = 0) := by
  refine ⟨selectedVector F hF x, selectedNormers F hF x, selectedVector_norm F hF x, ?_, ?_,
    selectedVector_ann_normers F hF x, selectedVector_ann_test F hF x⟩
  · intro m d hd
    exact (chosenPrefixNormers_spec _ m).1 d hd
  · intro m v hv
    apply (chosenPrefixNormers_spec _ m).2 v
    apply Submodule.span_mono (t :=
      (fun n => ((normerState F hF x m).1 n : StrongDual 𝕜 X)) '' (Finset.range m : Set ℕ)) _ hv
    rintro w ⟨n, hn, rfl⟩
    exact ⟨n, hn, congrArg Subtype.val (normerState_value F hF x n m (Finset.mem_range.mp hn))⟩
end SeparableQuotient.Positive.Fields

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields
universe u
def HasSeparableQuotient (𝕜 : Type) [RCLike 𝕜] (X : Type u)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∃ (Y : Type u) (g : NormedAddCommGroup Y),
    letI := g
    ∃ s : NormedSpace 𝕜 Y,
      letI := s
      CompleteSpace Y ∧ SeparableSpace Y ∧ ¬ FiniteDimensional 𝕜 Y ∧
        ∃ T : X →L[𝕜] Y, Function.Surjective T

end SeparableQuotient.Positive.Fields

end

end

end OAI
