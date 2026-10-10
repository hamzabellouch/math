import OAI.Combinatorics.GraphThreshold.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

namespace OAI

noncomputable section
open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

def resamplingY (A : B → Finset X) (W : Finset X) (c : B) : Finset X := W ∪ A c

def resamplingNumerator (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (Y : Finset X) (b : B) : ℝ :=
  if A b ⊆ Y then ν.weight b * (ρ⁻¹) ^ (A b).card else 0

/-- The actual normalizing density `Z(Y)`. -/
def resamplingZ (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (Y : Finset X) : ℝ :=
  ∑ b, resamplingNumerator ν A ρ Y b

def resamplingTargetWeight (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (c b : B) : ℝ :=
  resamplingNumerator ν A ρ (resamplingY A W c) b /
    resamplingZ ν A ρ (resamplingY A W c)

def resamplingWeight (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (cb : B × B) : ℝ :=
  ν.weight cb.1 * resamplingTargetWeight ν A ρ W cb.1 cb.2

/-- The retained target fragment; no quotienting of the label indices occurs. -/
def resamplingFragment (A : B → Finset X) (W : Finset X) (b : B) : Finset X :=
  A b \ W

theorem resamplingNumerator_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (Y : Finset X) (b : B) :
    0 ≤ resamplingNumerator ν A ρ Y b := by
  unfold resamplingNumerator
  split_ifs
  · exact mul_nonneg (ν.nonneg b) (pow_nonneg (inv_nonneg.mpr hρ) _)
  · exact le_rfl

theorem resamplingZ_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (Y : Finset X) : 0 ≤ resamplingZ ν A ρ Y := by
  exact Finset.sum_nonneg fun b _ => resamplingNumerator_nonneg ν A hρ Y b

theorem resamplingZ_pos (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (c : B) :
    0 < resamplingZ ν A ρ (resamplingY A W c) := by
  classical
  have hc : 0 < resamplingNumerator ν A ρ (resamplingY A W c) c := by
    rw [resamplingNumerator, resamplingY, ite_eq_left Finset.subset_union_right]
    exact mul_pos (hν c) (pow_pos (inv_pos.mpr hρ) _)
  exact lt_of_lt_of_le hc (Finset.single_le_sum
    (fun b _ => resamplingNumerator_nonneg ν A hρ.le (resamplingY A W c) b)
    (Finset.mem_univ c))

theorem resamplingTargetWeight_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (W : Finset X) (c b : B) :
    0 ≤ resamplingTargetWeight ν A ρ W c b :=
  div_nonneg (resamplingNumerator_nonneg ν A hρ _ _)
    (resamplingZ_nonneg ν A hρ _)

theorem resamplingWeight_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (W : Finset X) (cb : B × B) :
    0 ≤ resamplingWeight ν A ρ W cb :=
  mul_nonneg (ν.nonneg _) (resamplingTargetWeight_nonneg ν A hρ W _ _)

theorem resamplingTargetWeight_total (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (c : B) :
    (∑ b, resamplingTargetWeight ν A ρ W c b) = 1 := by
  simp only [resamplingTargetWeight, ← Finset.sum_div]
  exact div_self (resamplingZ_pos ν A hν hρ W c).ne'

theorem resampling_source_marginal (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (c : B) :
    (∑ b, resamplingWeight ν A ρ W (c, b)) = ν.weight c := by
  simp only [resamplingWeight, ← Finset.mul_sum,
    resamplingTargetWeight_total ν A hν hρ W c, mul_one]

theorem resamplingWeight_total (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) :
    (∑ cb : B × B, resamplingWeight ν A ρ W cb) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [resampling_source_marginal ν A hν hρ W]
  exact ν.total

def resamplingTargetLaw (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (c : B) (hν : ν.IsPositive) (hρ : 0 < ρ) : FiniteLaw B where
  weight := resamplingTargetWeight ν A ρ W c
  nonneg := resamplingTargetWeight_nonneg ν A hρ.le W c
  total := resamplingTargetWeight_total ν A hν hρ W c

def resamplingLaw (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (hν : ν.IsPositive) (hρ : 0 < ρ) : FiniteLaw (B × B) where
  weight := resamplingWeight ν A ρ W
  nonneg := resamplingWeight_nonneg ν A hρ.le W
  total := resamplingWeight_total ν A hν hρ W

@[simp] theorem resamplingLaw_weight (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (hν : ν.IsPositive) (hρ : 0 < ρ) (cb : B × B) :
    (resamplingLaw ν A ρ W hν hρ).weight cb = resamplingWeight ν A ρ W cb := rfl

theorem resampling_expectation_source (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (f : B → ℝ) :
    (resamplingLaw ν A ρ W hν hρ).expectation (fun cb => f cb.1) = ν.expectation f := by
  simp only [FiniteLaw.expectation, resamplingLaw_weight, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_mul, resampling_source_marginal ν A hν hρ W c]

theorem resampling_prob_source (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (P : B → Prop) :
    (resamplingLaw ν A ρ W hν hρ).prob (fun cb => P cb.1) = ν.prob P := by
  classical
  simp only [FiniteLaw.prob, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : P c
  · simp only [ite_eq_left hc, resamplingLaw_weight, resampling_source_marginal ν A hν hρ W c]
  · simp only [ite_eq_right hc, Finset.sum_const_zero]

theorem resamplingWeight_eq_zero_of_not_subset (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (W : Finset X) (c b : B) (hb : ¬A b ⊆ resamplingY A W c) :
    resamplingWeight ν A ρ W (c, b) = 0 := by
  simp [resamplingWeight, resamplingTargetWeight, resamplingNumerator, hb]

theorem resampling_target_subset_of_pos (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (W : Finset X) (c b : B)
    (hcb : 0 < resamplingWeight ν A ρ W (c, b)) : A b ⊆ resamplingY A W c := by
  by_contra hb
  rw [resamplingWeight_eq_zero_of_not_subset ν A ρ W c b hb] at hcb
  exact (lt_irrefl 0) hcb

omit [Fintype B] in
theorem resamplingFragment_subset_target (A : B → Finset X) (W : Finset X) (b : B) :
    resamplingFragment A W b ⊆ A b := Finset.sdiff_subset

theorem resamplingFragment_subset_source (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (W : Finset X) (c b : B)
    (hcb : 0 < resamplingWeight ν A ρ W (c, b)) :
    resamplingFragment A W b ⊆ A c := by
  intro x hx
  have hx' := Finset.mem_sdiff.mp hx
  rcases Finset.mem_union.mp (resampling_target_subset_of_pos ν A ρ W c b hcb hx'.1) with hW | hc
  · exact (hx'.2 hW).elim
  · exact hc

theorem resamplingFragment_subset_inter (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (W : Finset X) (c b : B)
    (hcb : 0 < resamplingWeight ν A ρ W (c, b)) :
    resamplingFragment A W b ⊆ A c ∩ A b :=
  Finset.subset_inter (resamplingFragment_subset_source ν A ρ W c b hcb)
    (resamplingFragment_subset_target A W b)

omit [Fintype B] in
/-- Every target label is recovered by adjoining its retained fragment to W. -/
theorem resamplingFragment_recovery (A : B → Finset X) (W : Finset X) (b : B) :
    A b ⊆ W ∪ resamplingFragment A W b := by
  intro x hx
  by_cases hW : x ∈ W
  · exact Finset.mem_union.mpr (Or.inl hW)
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hW⟩))

omit [Fintype B] in
theorem resampling_target_subset_iff_fragment (A : B → Finset X)
    (W : Finset X) (c b : B) :
    A b ⊆ resamplingY A W c ↔ resamplingFragment A W b ⊆ A c := by
  constructor
  · intro h x hx
    have hx' := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp (h hx'.1) with hW | hc
    · exact (hx'.2 hW).elim
    · exact hc
  · intro h x hx
    by_cases hW : x ∈ W
    · exact Finset.mem_union.mpr (Or.inl hW)
    · exact Finset.mem_union.mpr (Or.inr (h (Finset.mem_sdiff.mpr ⟨hx, hW⟩)))

/-- The transition depends on W only through its intersections with the
labels, expressed equivalently by their retained fragments. -/
theorem resamplingWeight_congr_fragments (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) {W W' : Finset X}
    (hW : ∀ b, resamplingFragment A W b = resamplingFragment A W' b) (cb : B × B) :
    resamplingWeight ν A ρ W cb = resamplingWeight ν A ρ W' cb := by
  have hsub (c b : B) : A b ⊆ resamplingY A W c ↔ A b ⊆ resamplingY A W' c := by
    rw [resampling_target_subset_iff_fragment, resampling_target_subset_iff_fragment, hW]
  have hn (c b : B) :
      resamplingNumerator ν A ρ (resamplingY A W c) b =
        resamplingNumerator ν A ρ (resamplingY A W' c) b := by
    simp only [resamplingNumerator, hsub]
  simp only [resamplingWeight, resamplingTargetWeight, resamplingZ, hn]

end LeanBlast.SecondKahnKalai

end

end OAI
