import OAI.NumberTheory.SiegelZeros.Selection.EventuallyPivots

namespace OAI

section

open Filter
open scoped BigOperators

namespace SiegelZeros.W49

open Result.Workers.W33 WeightedTorusJets.W48

noncomputable def fixedPivotCoefficient (H : ℕ) : ℝ :=
  (H : ℝ) ^ (2 / 3 : ℝ) / (4 * 97 ^ 2)

theorem fixedPivotCoefficient_pos {H : ℕ} (hH : 0 < H) :
    0 < fixedPivotCoefficient H := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  unfold fixedPivotCoefficient
  positivity

theorem transverseOrder_nonneg (P : Finset SiegelZerosAwei.W31.MultiIndex) :
    0 ≤ transverseOrder P := by
  unfold transverseOrder
  exact Finset.sum_nonneg fun a ha => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem eventual_error_inputs {ι : Type*} {l : Filter ι} {q : ι → ℕ}
    (P : ι → Finset SiegelZerosAwei.W31.MultiIndex) (H : ℕ) (hH : 86713344 ≤ H)
    {γ : ℝ} (hγ : 0 < γ) (hq : Tendsto q l atTop)
    (hcard : ∀ᶠ i in l, (P i).card = auxiliaryN γ (q i) ^ 4)
    (hcut : ∀ᶠ i in l, ∀ a ∈ P i, SiegelZerosAwei.W31.weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * auxiliaryU γ (q i)) :
    ∀ᶠ i in l,
      0 < (auxiliaryN γ (q i) : ℝ) ^ (4 : ℕ) ∧
      0 < firstOrder (P i) ∧
      0 < Real.log (auxiliaryU γ (q i)) ∧
      fixedPivotCoefficient H * (auxiliaryN γ (q i) : ℝ) ^ (4 : ℕ) *
        auxiliaryU γ (q i) ≤ firstOrder (P i) ∧
      0 ≤ transverseOrder (P i) / firstOrder (P i) ∧
      transverseOrder (P i) / firstOrder (P i) ≤ (1 / 12 : ℝ) := by
  have hb := eventual_pivot_bounds P H (by omega) hγ hq hcard hcut
  have hr := eventual_pivot_ratio_le_twelfth P H hH hγ hq hcard hcut
  have hu := (natural_conductor_limits hγ hq).2.1
  filter_upwards [hb, hr, hu.eventually_gt_atTop 1] with i hi hir hiu
  have hn : (0 : ℝ) < auxiliaryN γ (q i) := by
    exact_mod_cast (show 0 < auxiliaryN γ (q i) by omega)
  refine ⟨by positivity, hi.2.2.1, Real.log_pos hiu, ?_,
    div_nonneg (transverseOrder_nonneg _) hi.2.2.1.le, hir.2⟩
  calc
    _ = (auxiliaryN γ (q i) : ℝ) ^ (4 : ℕ) * (H : ℝ) ^ (2 / 3 : ℝ) *
        auxiliaryU γ (q i) / (4 * 97 ^ 2) := by
      unfold fixedPivotCoefficient
      ring
    _ ≤ firstOrder (P i) := hi.2.2.2.1

end SiegelZeros.W49

end

end OAI
