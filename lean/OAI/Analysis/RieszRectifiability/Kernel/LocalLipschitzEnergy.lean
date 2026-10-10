import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CutoffEnergyIntegral
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzTests

namespace OAI

/-!
# Local Lipschitz control of fractional energy

Almost-everywhere Lipschitz difference bounds and bounded pair distances give
integrability of fractional pair energies under global upper growth. Their weighted
differences lie in L², yielding integrability of the associated bilinear pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem fractionalEnergy_bound_of_difference_bound {d : ℕ} (p : ℕ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (x y : Ambient d)
    (h : |w x - w y| ≤ (K : ℝ) * dist x y) :
    fractionalPairEnergy (p + 1) w x y ≤ (K : ℝ) ^ 2 * inverseDistancePow p x y := by
  by_cases hxy : x = y
  · subst y
    simp only [fractionalPairEnergy, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    exact mul_nonneg (sq_nonneg _) (inverseDistancePow_nonneg _ _ _)
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hsq : (w x - w y) ^ 2 ≤ (K : ℝ) ^ 2 * dist x y ^ 2 := by
      simpa only [sq_abs, mul_pow] using!
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg K.coe_nonneg dist_nonneg)).mpr h
    calc
      _ ≤ ((K : ℝ) ^ 2 * dist x y ^ 2) / dist x y ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hsq (pow_nonneg dist_nonneg _)
      _ = _ := by
        rw [show p + 1 + 1 = p + 2 by omega, pow_add]
        unfold inverseDistancePow
        field_simp

theorem fractionalEnergy_integrable_of_ae_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w : Ambient d → ℝ) (hw : Measurable w) (K : ℝ≥0)
    (hK : ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2)
      (μ.prod μ) := by
  have hm : Measurable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) w q.1 q.2) := by
    unfold fractionalPairEnergy
    fun_prop
  apply ((nearPairWeight_integrable p C μ hg r hr).const_mul ((K : ℝ) ^ 2)).mono'
    hm.aestronglyMeasurable
  filter_upwards [hK, hdiam] with q hq hd
  have hmem : q ∈ nearPairSet r := by
    simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm] using! hd
  rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _), nearPairWeight,
    indicator_of_mem hmem]
  exact fractionalEnergy_bound_of_difference_bound p w K q.1 q.2 hq

theorem fractionalBilinear_integrable_of_ae_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w ψ : Ambient d → ℝ) (hw : Measurable w) (hψ : Measurable ψ) (K L : ℝ≥0)
    (hK : ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2)
    (hL : ∀ᵐ q ∂μ.prod μ, |ψ q.1 - ψ q.2| ≤ (L : ℝ) * dist q.1 q.2)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w ψ q.1 q.2)
      (μ.prod μ) := by
  have hf := weightedDifference_memLp (p + 1) w hw (μ.prod μ)
    (fractionalEnergy_integrable_of_ae_lipschitz p C μ hg w hw K hK r hr hdiam)
  have hgtest := weightedDifference_memLp (p + 1) ψ hψ (μ.prod μ)
    (fractionalEnergy_integrable_of_ae_lipschitz p C μ hg ψ hψ L hL r hr hdiam)
  have hprod : MemLp (fun q : Ambient d × Ambient d =>
      weightedDifference (p + 1) w q.1 q.2 * weightedDifference (p + 1) ψ q.1 q.2)
      1 (μ.prod μ) := hf.mul hgtest
  simpa only [weightedDifference_mul] using! memLp_one_iff_integrable.mp hprod

theorem ae_difference_bound_of_lipschitzOn {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (s : Set (Ambient d))
    (hs : ∀ᵐ x ∂μ, x ∈ s) (w : Ambient d → ℝ) (K : ℝ≥0) (hK : LipschitzOnWith K w s) :
    ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
    Measure.quasiMeasurePreserving_snd.ae hs] with q hx hy
  simpa only [Real.dist_eq] using! hK.dist_le_mul q.1 hx q.2 hy

theorem lipschitzOn_bounded_product_real {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (f g : X → ℝ) (Kf Kg Bf Bg : ℝ≥0)
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
    (hBf : ∀ x ∈ s, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x ∈ s, |g x| ≤ (Bg : ℝ)) :
    LipschitzOnWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) s := by
  apply lipschitzOnWith_iff_restrict.mpr
  exact lipschitz_bounded_product_real (lipschitzOnWith_iff_restrict.mp hf)
    (lipschitzOnWith_iff_restrict.mp hg) (fun x => hBf x x.property) (fun x => hBg x x.property)

theorem squared_cutoff_height_lipschitzOn {d : ℕ}
    (s : Set (Ambient d)) (w χ : Ambient d → ℝ) (K L W H : ℝ≥0)
    (hw : LipschitzOnWith K w s) (hχ : LipschitzOnWith L χ s)
    (hW : ∀ x ∈ s, |w x| ≤ (W : ℝ)) (hH : ∀ x ∈ s, |χ x| ≤ (H : ℝ)) :
    LipschitzOnWith (H * (H * K + L * W) + L * (H * W))
      (fun x => χ x ^ 2 * w x) s := by
  have hprod := lipschitzOn_bounded_product_real s χ w L K H W hχ hw hH hW
  have hbound (x : Ambient d) (hx : x ∈ s) : |χ x * w x| ≤ ((H * W : ℝ≥0) : ℝ) := by
    rw [abs_mul, NNReal.coe_mul]
    exact mul_le_mul (hH x hx) (hW x hx) (abs_nonneg _) H.coe_nonneg
  have h := lipschitzOn_bounded_product_real s χ (fun x => χ x * w x)
    L (H * K + L * W) H (H * W) hχ hprod hH hbound
  simpa only [pow_two, mul_assoc] using! h

theorem localized_cutoff_energy_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (s : Set (Ambient d)) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (K L W H : ℝ≥0) (hwLip : LipschitzOnWith K w s) (hχ : LipschitzWith L χ)
    (hW : ∀ x ∈ s, |w x| ≤ (W : ℝ)) (hH : ∀ x ∈ s, |χ x| ≤ (H : ℝ))
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r)
    (A : ℝ) (hA : (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) w (fun x => χ x ^ 2 * w x) q.1 q.2 ∂μ.prod μ) ≤ A) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2 ∂μ.prod μ) ≤
        A + (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  have htest := squared_cutoff_height_lipschitzOn s w χ K L W H hwLip hχ.lipschitzOnWith hW hH
  have hmtest : Measurable (fun x => χ x ^ 2 * w x) :=
    (hχ.continuous.measurable.pow_const 2).mul hw
  apply cutoff_energy_from_integrable_interior_pairing p C μ hg w χ hw hL2 L hχ r hr hdiam
  · exact fractionalBilinear_integrable_of_ae_lipschitz p C μ hg w (fun x => χ x ^ 2 * w x)
      hw hmtest K (H * (H * K + L * W) + L * (H * W))
      (ae_difference_bound_of_lipschitzOn μ s hs w K hwLip)
      (ae_difference_bound_of_lipschitzOn μ s hs _ _ htest) r hr hdiam
  · exact hA

end

end RieszRectifiability

end OAI
