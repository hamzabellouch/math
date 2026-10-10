import OAI.NumberTheory.TotientAsymptotic.SimplexScaling
import OAI.NumberTheory.TotientAsymptotic.CubeBoundary

namespace OAI

/-! Unit boxes around a simplex prefix, without coordinate-band hypotheses. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def prefixCubeCost (N : ℕ) : ℝ :=
  (N:ℝ)^2 + ∑ i : Fin N, g (i.val+1)*((N-i.val:ℕ):ℝ)^2

lemma prefixCubeCost_nonneg (N : ℕ) : 0 ≤ prefixCubeCost N := by
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (g_pos _).le (sq_nonneg _)))

lemma prefixRegion_unit_cube {N : ℕ} {B : ℝ} {u v : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (hd : ∀ i, |u i-v i| ≤ 1) :
    v ∈ prefixRegion N (B+(N:ℝ)^2) 0
      (fun i => -((N-i.val:ℕ):ℝ)^2) := by
  refine ⟨fun i => ?_, ?_⟩
  · have hh := (le_abs_self _).trans (prefixLinear_cube_error u v hd i)
    have hi := hu.1 i
    change 0 ≤ prefixLinear N u i at hi
    linarith
  · have hh := (neg_le_abs _).trans (prefixBudget_cube_error u v hd)
    have hi := hu.2
    simp only [sub_zero] at hi ⊢
    linarith

lemma simplexScale_unit_distance {N : ℕ} {κ u v : Fin N → ℝ}
    (hκ : ∀ i, 1 ≤ κ i) (hd : ∀ i, |u i-v i| ≤ 1) :
    ∀ i, |simplexScale κ u i-simplexScale κ v i| ≤ 1 := by
  intro i
  simp only [simplexScale_apply, ← sub_div, abs_div, abs_of_pos (zero_lt_one.trans_le (hκ i))]
  exact (div_le_iff₀ (zero_lt_one.trans_le (hκ i))).mpr (by
    simpa only [one_mul] using (hd i).trans (hκ i))

/-- Diagonal normalization followed by additive cube error does not require
lower coordinate bands. The error is the exact renewal-weighted sum. -/
theorem unbanded_grid_volume_bound {N : ℕ} (hN : 0 < N)
    (B β₀ : ℝ) (β κ : Fin N → ℝ) (K : Finset (Fin N → ℕ))
    (hB : 0 ≤ B) (hβ₀ : 0 < β₀) (hβ : ∀ i, 0 < β i)
    (hκ : ∀ i, 1 ≤ κ i) (htop : ∀ i, β₀ ≤ κ i)
    (hstep : ∀ i j, i < j → β i*κ i ≤ κ j)
    (hK : ∀ b ∈ K, ∃ u ∈ unitGridCell b, u ∈ enlargedSimplex N B β₀ β) :
    (K.card:ℝ) ≤ (∏ i, κ i)*
      ((B+prefixCubeCost N)^N/((N.factorial:ℝ)*∏ i : Fin N, g (i.val+1))) := by
  let S := prefixRegion N (B+(N:ℝ)^2) 0 (fun i => -((N-i.val:ℕ):ℝ)^2)
  have hκpos (i) : 0 < κ i := zero_lt_one.trans_le (hκ i)
  have hp : 0 < ∏ i, κ i := Finset.prod_pos (fun i _ => hκpos i)
  have hd : LinearMap.det (simplexScale κ) ≠ 0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hsub : gridRegion K ⊆ (simplexScale κ) ⁻¹' S := by
    intro v hv
    obtain ⟨b,hv⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hb,hvb⟩ := Set.mem_iUnion.mp hv
    obtain ⟨u,hub,hu⟩ := hK b hb
    exact prefixRegion_unit_cube
      (enlargedSimplex_mapsTo hβ₀ hβ hκpos htop hstep hu)
      (simplexScale_unit_distance hκ (unitGridCell_coordinate_distance hub hvb))
  have hvol : volume (gridRegion K) ≤ ENNReal.ofReal (∏ i, κ i)*volume S := by
    apply (measure_mono hsub).trans_eq
    rw [← Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable
      (measurableSet_prefixRegion _ _ _ _),
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hd, simplexScale_det,
      inv_inv, abs_of_pos hp, Measure.smul_apply, smul_eq_mul]
  have he : B+(N:ℝ)^2-0-(∑ i : Fin N, g (i.val+1)*(-((N-i.val:ℕ):ℝ)^2)) =
      B+prefixCubeCost N := by
    simp only [prefixCubeCost, mul_neg, Finset.sum_neg_distrib]
    ring
  have hn : 0 ≤ B+prefixCubeCost N := add_nonneg hB (prefixCubeCost_nonneg N)
  change volume (gridRegion K) ≤ ENNReal.ofReal (∏ i, κ i)*
    volume (prefixRegion N (B+(N:ℝ)^2) 0 (fun i => -((N-i.val:ℕ):ℝ)^2)) at hvol
  rw [volume_prefixRegion_explicit N hN, he, max_eq_left hn,
    ← ENNReal.ofReal_mul hp.le] at hvol
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  have hnresult : 0 ≤ (∏ i, κ i)*((B+prefixCubeCost N)^N/
      ((N.factorial:ℝ)*∏ i : Fin N, g (i.val+1))) :=
    mul_nonneg hp.le (div_nonneg (pow_nonneg hn _)
      (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (g_pos _).le))))
  simpa only [gridRegion_volume_real, ENNReal.toReal_ofReal hnresult] using hh

end TotientAsymptotic

end

end OAI
