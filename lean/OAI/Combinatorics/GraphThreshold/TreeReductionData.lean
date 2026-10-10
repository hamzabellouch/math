import OAI.Combinatorics.GraphThreshold.ProbabilityTree
import OAI.Combinatorics.GraphThreshold.ResamplingEvents

namespace OAI

/-! Fixed-input local masses and the deterministic good-node predicate. -/

noncomputable section
open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

section LocalMasses

variable {X B : Type*} [DecidableEq X] [Fintype B]

def successfulTargetMass (μ : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (b : B) : ℝ :=
  ∑ c, if LocalSuccess μ A ρ m W c b then resamplingWeight μ A ρ W (c, b) else 0

def localFailureMass (μ : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) : ℝ :=
  ∑ b, ∑ c, if LocalFailure μ A ρ m W c b then resamplingWeight μ A ρ W (c, b) else 0

theorem successfulTargetMass_nonneg (μ : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) (W : Finset X) (b : B) :
    0 ≤ successfulTargetMass μ A ρ m W b := by
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact resamplingWeight_nonneg μ A hρ W (c, b)
  · exact le_rfl

theorem localFailureMass_nonneg (μ : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) (W : Finset X) :
    0 ≤ localFailureMass μ A ρ m W := by
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact resamplingWeight_nonneg μ A hρ W (c, b)
  · exact le_rfl

theorem localFailureMass_add_successfulTargetMass (μ : FiniteLaw B)
    (A : B → Finset X) {ρ : ℝ} (hμ : μ.IsPositive) (hρ : 0 < ρ)
    (m : ℕ) (W : Finset X) :
    localFailureMass μ A ρ m W + ∑ b, successfulTargetMass μ A ρ m W b = 1 := by
  classical
  calc
    _ = ∑ b, ∑ c, resamplingWeight μ A ρ W (c, b) := by
      unfold localFailureMass successfulTargetMass LocalFailure
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : LocalSuccess μ A ρ m W c b <;> simp [h]
    _ = ∑ c, ∑ b, resamplingWeight μ A ρ W (c, b) := Finset.sum_comm
    _ = 1 := by
      simp_rw [resampling_source_marginal μ A hμ hρ W]
      exact μ.total

theorem localFailureMass_eq_prob (μ : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hμ : μ.IsPositive) (hρ : 0 < ρ) (m : ℕ) (W : Finset X) :
    localFailureMass μ A ρ m W =
      (resamplingLaw μ A ρ W hμ hρ).prob (fun cb => LocalFailure μ A ρ m W cb.1 cb.2) := by
  classical
  unfold localFailureMass FiniteLaw.prob
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rfl

theorem successfulTargetMass_pos_capacity (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) (W : Finset X) (b : B)
    (hb : 0 < successfulTargetMass μ A ρ m W b) : (A b \ W).card ≤ m / 2 := by
  by_contra hcap
  have hfail (c : B) : ¬LocalSuccess μ A ρ m W c b := fun h => hcap h.2
  simp [successfulTargetMass, hfail] at hb

theorem resamplingZ_congr_fragments (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) {W V : Finset X}
    (hWV : ∀ b, resamplingFragment A W b = resamplingFragment A V b) (c : B) :
    resamplingZ μ A ρ (W ∪ A c) = resamplingZ μ A ρ (V ∪ A c) := by
  unfold resamplingZ
  apply Finset.sum_congr rfl
  intro b _
  have hsub : A b ⊆ resamplingY A W c ↔ A b ⊆ resamplingY A V c := by
    rw [resampling_target_subset_iff_fragment, resampling_target_subset_iff_fragment, hWV]
  unfold resamplingNumerator
  exact if_congr hsub rfl rfl

theorem localSuccess_congr_fragments (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) {W V : Finset X}
    (hWV : ∀ b, resamplingFragment A W b = resamplingFragment A V b) (c b : B) :
    LocalSuccess μ A ρ m W c b ↔ LocalSuccess μ A ρ m V c b := by
  unfold LocalSuccess
  rw [resamplingZ_congr_fragments μ A ρ hWV c]
  change (_ ∧ (resamplingFragment A W b).card ≤ m / 2) ↔
    (_ ∧ (resamplingFragment A V b).card ≤ m / 2)
  rw [hWV b]

theorem successfulTargetMass_congr_fragments (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) {W V : Finset X}
    (hWV : ∀ b, resamplingFragment A W b = resamplingFragment A V b) (b : B) :
    successfulTargetMass μ A ρ m W b = successfulTargetMass μ A ρ m V b := by
  unfold successfulTargetMass
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : LocalSuccess μ A ρ m W c b
  · have hv := (localSuccess_congr_fragments μ A ρ m hWV c b).mp h
    simp [h, hv, resamplingWeight_congr_fragments μ A ρ hWV]
  · have hv : ¬LocalSuccess μ A ρ m V c b :=
      fun hv => h ((localSuccess_congr_fragments μ A ρ m hWV c b).mpr hv)
    simp [h, hv]

theorem localFailureMass_congr_fragments (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) {W V : Finset X}
    (hWV : ∀ b, resamplingFragment A W b = resamplingFragment A V b) :
    localFailureMass μ A ρ m W = localFailureMass μ A ρ m V := by
  unfold localFailureMass LocalFailure
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : LocalSuccess μ A ρ m W c b
  · have hv := (localSuccess_congr_fragments μ A ρ m hWV c b).mp h
    simp [h, hv]
  · have hv : ¬LocalSuccess μ A ρ m V c b :=
      fun hv => h ((localSuccess_congr_fragments μ A ρ m hWV c b).mpr hv)
    simp [h, hv, resamplingWeight_congr_fragments μ A ρ hWV]

theorem fragments_eq_of_inter_label_union_eq (A : B → Finset X) {W V : Finset X}
    (hWV : W ∩ Finset.univ.biUnion A = V ∩ Finset.univ.biUnion A) (b : B) :
    resamplingFragment A W b = resamplingFragment A V b := by
  apply Finset.ext
  intro x
  by_cases hx : x ∈ A b
  · have hxU : x ∈ Finset.univ.biUnion A :=
      Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hx⟩
    have hmem : x ∈ W ↔ x ∈ V := by
      simpa only [Finset.mem_inter, hxU, and_true] using Finset.ext_iff.mp hWV x
    simp [resamplingFragment, hx, hmem]
  · simp [resamplingFragment, hx]

theorem successfulTargetMass_dependsOnlyOn (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) (b : B) :
    DependsOnlyOn (Finset.univ.biUnion A) (fun W => successfulTargetMass μ A ρ m W b) := by
  intro W V hWV
  exact successfulTargetMass_congr_fragments μ A ρ m
    (fragments_eq_of_inter_label_union_eq A hWV) b

theorem localFailureMass_dependsOnlyOn (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) :
    DependsOnlyOn (Finset.univ.biUnion A) (fun W => localFailureMass μ A ρ m W) := by
  intro W V hWV
  exact localFailureMass_congr_fragments μ A ρ m
    (fragments_eq_of_inter_label_union_eq A hWV)

end LocalMasses

variable {X : Type} [DecidableEq X]

/-- Goodness is evaluated on the fixed input tree, using local nonfailure
target masses before any pruning or reweighting. -/
def Good (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ} (T : ProbabilityTree X d) : Prop :=
  match T with
  | .leaf => True
  | @ProbabilityTree.node _ _ B inst μ _hμ A child =>
      1 - Real.exp (-(m 0 : ℝ)) ≤
        ∑ b, if Good ρ (fun j => m (j + 1)) W (child b) then
          successfulTargetMass μ A ρ (m 0) W b else 0
termination_by d

end LeanBlast.SecondKahnKalai

end

end OAI
