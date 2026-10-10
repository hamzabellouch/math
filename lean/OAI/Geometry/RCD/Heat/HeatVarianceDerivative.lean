import OAI.Geometry.RCD.Heat.HeatSquarePairing

namespace OAI

/-! # Differentiating the forward/backward heat variance pairing -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

/-- The pairing whose endpoints give the heat variance. -/
def heatSquarePairing (f w : Lp ℝ 2 μ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) (T s : ℝ) : ℝ :=
  inner ℝ (heatAt μ hQ s w) (boundedLpSquare μ (heatAt μ hQ (T-s) f) C C.coe_nonneg
    (heatAt_abs_le_const μ hQ (T-s) C f hf))

/-- In the interior of the time interval, the derivative is twice the
weighted gradient energy of the backward heat flow. -/
theorem heatSquarePairing_hasDerivAt (f w : Lp ℝ 2 μ) (C B L : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) (hw : ∀ᵐ x ∂μ, |w x| ≤ B)
    (T s : ℝ) (hs : 0 < s) (hTs : 0 < T-s)
    (hg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ
      (heatSobolev μ hQ (T-s) hTs f) x ≤ L) :
    HasDerivAt (heatSquarePairing μ hQ f w C hf T)
      (2*∫ x, heatAt μ hQ s w x*(SobolevSpace.minimalSlope μ hQ
        (heatSobolev μ hQ (T-s) hTs f) x)^2 ∂μ) s := by
  let F := heatAt μ hQ (T-s) f
  let W := heatAt μ hQ s w
  let D := heatGeneratorAt μ hQ (T-s) f
  let U := heatSobolev μ hQ (T-s) hTs f
  let G := SobolevSpace.minimalSlope μ hQ U
  have hWb : ∀ᵐ x ∂μ, |W x| ≤ B := heatAt_abs_le_const μ hQ s B w hw
  let hVm : MemLp W ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable W) B
    (by simpa only [Real.norm_eq_abs] using hWb)
  let V := hVm.toLp W
  have hV : V =ᵐ[μ] W := hVm.coeFn_toLp
  have hF : HasDerivAt (fun r => heatAt μ hQ (T-r) f) D s := by
    have hh := (heatAt_hasDerivAt μ hQ (T-s) hTs f).scomp s
      ((hasDerivAt_const s T).sub (hasDerivAt_id s))
    simpa only [Function.comp_def,zero_sub,neg_smul,one_smul,neg_neg] using hh
  have hp := boundedSquare_pairing_hasDerivAt μ C.coe_nonneg
    (fun r => heatAt_abs_le_const μ hQ (T-r) C f hf) hF
    (heatAt_hasDerivAt μ hQ s hs w) V hV
  have hUb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ U x| ≤ C := by
    simpa only [U,heatSobolev_toLp] using heatAt_abs_le_const μ hQ (T-s) C f hf
  have hUd : IsWeakLaplacian μ hQ U (-D) := by
    simpa only [U,D,heatGeneratorAt_of_pos μ hQ (T-s) hTs] using
      heatSobolev_weak_laplacian μ hQ (T-s) hTs f
  have hleft := heat_square_inner_laplacian μ hQ U (-D) C L hUb hg hUd w s hs
  simp only [U,heatSobolev_toLp] at hleft
  have hFD : Integrable (fun x => W x*(F x*D x)) μ := by
    apply ((Lp.memLp F).integrable_mul (Lp.memLp D)).bdd_mul (Lp.aestronglyMeasurable W)
    simpa only [Real.norm_eq_abs] using hWb
  have hG : Integrable (fun x => W x*G x^2) μ := by
    apply (Lp.memLp G).integrable_sq.bdd_mul (Lp.aestronglyMeasurable W)
    simpa only [Real.norm_eq_abs] using hWb
  have hright : inner ℝ D (lpMultiplier μ V F) = ∫ x, W x*(F x*D x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpMultiplier_coe μ V F,hV] with x hx hv
    simp only [Real.inner_apply,hx,hv]
    ring
  have hi : (∫ x, W x*(F x*(-D) x+G x^2) ∂μ) =
      -(∫ x, W x*(F x*D x) ∂μ)+(∫ x, W x*G x^2 ∂μ) := by
    rw [← integral_neg]
    calc
      _ = ∫ x, -(W x*(F x*D x))+W x*G x^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_neg D] with x hx
        simp only [hx,Pi.neg_apply]
        ring
      _ = _ := by simpa only [Pi.add_apply,Pi.neg_apply] using integral_add hFD.neg hG
  change HasDerivAt (heatSquarePairing μ hQ f w C hf T) _ s at hp
  convert hp using 1
  rw [hleft]
  change 2*(∫ x, W x*G x^2 ∂μ) =
    2*(∫ x, W x*(F x*(-D) x+G x^2) ∂μ)+2*inner ℝ D (lpMultiplier μ V F)
  rw [hi,hright]
  ring

end RegularPointCoordinates

end

end OAI
