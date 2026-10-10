import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.MatrixCofactorOrder
import OAI.Geometry.PrescribedPotential.PotentialDensity
import OAI.Geometry.PrescribedRicci.KahlerVolumeVariation

namespace OAI

/-! Monge Ampere Energy. -/

section

 

noncomputable section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff ComplexOrder Classical Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma integral_sub [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h) :
    g.integral (fun x => f x - h x) = g.integral f - g.integral h := by
  have he : (fun x => f x - h x) = fun x => f x + (-1) * h x := by funext x; ring
  rw [he, g.integral_add hf (show Continuous (fun x => (-1) * h x) from continuous_const.fun_mul hh), g.integral_const_mul]
  ring

lemma integral_mono [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h) (hle : ∀ x, f x ≤ h x) :
    g.integral f ≤ g.integral h := by
  have he := g.integral_nonneg (fun x => sub_nonneg.mpr (hle x))
  rw [g.integral_sub hh hf] at he
  exact sub_nonneg.mp he

lemma integral_zero [T2Space X] [CompactSpace X] (g : KaehlerMetric A) :
    g.integral (fun _ => 0) = 0 := by simp [integral, chartIntegral]

lemma cofactorQuadratic_eq_gradientPair (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (p : Fin d → ℂ) :
    MongeAmpere.cofactorQuadratic H (star p) = H.det.re * (gradientPair H p p).re := by
  have he : star (star p) ⬝ᵥ (H⁻¹ *ᵥ star p) = gradientPair H p p := by
    simp only [gradientPair, dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [MongeAmpere.cofactorQuadratic, he, Complex.mul_re, hermitian_det_im hH, zero_mul, sub_zero]

lemma energy_segment_coercive (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (hd : 0 < d) (s : ℝ) (hs : s ∈ Ico 0 1) (x : X) :
    (1 - s) ^ (d - 1) * (g.energy φ φ).value x ≤
      (g.potentialDensity (φ.realSMul s)).value x *
        ((g.deform (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)).energy φ φ).value x := by
  let gs := g.deform (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)
  obtain ⟨i, hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  let z := A.chart i x
  let p := holRealDeriv (φ.localExpression i) z
  have hem : (((1 - s : ℝ) : ℂ) • g.matrix i z + (s : ℂ) •
      (g.matrix i z + φ.hessian i z)) = gs.matrix i z := by
    change _ = g.matrix i z + (φ.realSMul s).hessian i z
    rw [SmoothRealFunction.hessian_realSMul]
    ext j k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hm := MongeAmpere.cofactorQuadratic_segment (g.positive i z hz) (hp i z hz) (star p) hd hs
  rw [hem, cofactorQuadratic_eq_gradientPair _ (g.positive i z hz).isHermitian,
    cofactorQuadratic_eq_gradientPair _ (gs.positive i z hz).isHermitian] at hm
  have he := g.energy_local φ φ i hz
  have he' := gs.energy_local φ φ i hz
  simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi] at he he'
  change (g.energy φ φ).value x = (gradientPair (g.matrix i z) p p).re at he
  change (gs.energy φ φ).value x = (gradientPair (gs.matrix i z) p p).re at he'
  rw [← he, ← he'] at hm
  have hv := g.density_mul_volume (φ.realSMul s) i hz
  rw [(A.chart i).left_inv hi] at hv
  change (g.potentialDensity (φ.realSMul s)).value x * (g.matrix i z).det.re = (gs.matrix i z).det.re at hv
  apply (mul_le_mul_iff_of_pos_left (g.volumeCoefficient_pos i hz)).mp
  change (g.matrix i z).det.re * _ ≤ (g.matrix i z).det.re * _
  calc
    _ = (1 - s) ^ (d - 1) * ((g.matrix i z).det.re * (g.energy φ φ).value x) := by ring
    _ ≤ (gs.matrix i z).det.re * (gs.energy φ φ).value x := hm
    _ = _ := by rw [← hv]; ring

lemma integral_energy_segment_coercive [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ)
    (hd : 0 < d) (s : ℝ) (hs : s ∈ Ico 0 1) :
    (1 - s) ^ (d - 1) * g.integral (g.energy φ φ).value ≤
      (g.deform (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)).integral
        ((g.deform (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)).energy φ φ).value := by
  let gs := g.deform (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)
  rw [← g.integral_const_mul, ← g.integral_density (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)]
  apply g.integral_mono (continuous_const.mul (g.energy φ φ).continuous)
    ((gs.energy φ φ).continuous.mul (g.potentialDensity _).continuous)
  intro x
  change (1 - s) ^ (d - 1) * (g.energy φ φ).value x ≤
    (gs.energy φ φ).value x * (g.potentialDensity (φ.realSMul s)).value x
  simpa only [mul_comm] using g.energy_segment_coercive φ hp hd s hs x

 

lemma integral_energy_half_segment [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ)
    (hd : 0 < d) (s : ℝ) (hs : s ∈ Icc 0 (1/2)) :
    (1/2 : ℝ) ^ (d - 1) * g.integral (g.energy φ φ).value ≤
      (g.deform (φ.realSMul s) (hp.segment ⟨hs.1, by linarith [hs.2]⟩)).integral
        ((g.deform (φ.realSMul s) (hp.segment ⟨hs.1, by linarith [hs.2]⟩)).energy φ φ).value := by
  have hs' : s ∈ Ico 0 1 := ⟨hs.1, by linarith [hs.2]⟩
  refine le_trans ?_ (g.integral_energy_segment_coercive φ hp hd s hs')
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by norm_num) (by linarith [hs.2]) (d - 1))
    (g.integral_nonneg (g.energy_nonneg φ))

lemma potentialDensity_smul_zero (g : KaehlerMetric A) (φ : SmoothRealFunction A) (x : X) :
    (g.potentialDensity (φ.realSMul 0)).value x = 1 := by
  obtain ⟨i, hi⟩ := A.covers x
  change g.potentialDensityValue _ x = _
  rw [g.potentialDensityValue_local _ i hi]
  simp only [volumePolynomial, SmoothRealFunction.hessian_realSMul, Complex.ofReal_zero,
    zero_smul, add_zero, div_self (g.positive i _ ((A.chart i).mapsTo hi)).det_pos.ne', Complex.one_re]

lemma potentialDensity_smul_one (g : KaehlerMetric A) (φ : SmoothRealFunction A) (x : X) :
    (g.potentialDensity (φ.realSMul 1)).value x = (g.potentialDensity φ).value x := by
  obtain ⟨i, hi⟩ := A.covers x
  change g.potentialDensityValue _ x = g.potentialDensityValue _ x
  rw [g.potentialDensityValue_local _ i hi, g.potentialDensityValue_local _ i hi]
  simp only [volumePolynomial, SmoothRealFunction.hessian_realSMul, Complex.ofReal_one, one_smul]

 

theorem mongeAmpere_energy [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ) (hd : 0 < d) :
    (1/2 : ℝ) ^ d * g.integral (g.energy φ φ).value ≤
      g.integral φ.value - g.integral (fun x => φ.value x * (g.potentialDensity φ).value x) := by
  let f (t : ℝ) := g.integral (fun x => φ.value x * (g.potentialDensity (φ.realSMul t)).value x)
  have hf (s : ℝ) (hs : s ∈ Icc 0 1) := g.volume_firstVariation φ φ s (hp.segment hs)
  have hfc : ContinuousOn f (Icc 0 1) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hfd : DifferentiableOn ℝ f (interior (Icc 0 1)) :=
    fun s hs => (hf s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have ha : AntitoneOn f (Icc 0 1) := antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hfc hfd (by
    intro s hs
    rw [(hf s (interior_subset hs)).deriv]
    exact neg_nonpos.mpr ((g.deform (φ.realSMul s) (hp.segment (interior_subset hs))).integral_nonneg
      ((g.deform (φ.realSMul s) (hp.segment (interior_subset hs))).energy_nonneg φ)))
  have hsub : Icc (0 : ℝ) (1/2) ⊆ Icc 0 1 := fun s hs => ⟨hs.1, by linarith [hs.2]⟩
  have hdh : DifferentiableOn ℝ f (interior (Icc 0 (1/2))) :=
    fun s hs => (hf s (hsub (interior_subset hs))).differentiableAt.differentiableWithinAt
  have hh := (convex_Icc (0 : ℝ) (1/2)).image_sub_le_mul_sub_of_deriv_le
    (hfc.mono hsub) hdh (C := -((1/2 : ℝ) ^ (d - 1) * g.integral (g.energy φ φ).value))
    (by
      intro s hs
      rw [(hf s (hsub (interior_subset hs))).deriv]
      exact neg_le_neg (g.integral_energy_half_segment φ hp hd s (interior_subset hs)))
    0 (by norm_num) (1/2) (by norm_num) (by norm_num)
  have he := ha (show (1/2 : ℝ) ∈ Icc 0 1 by norm_num) (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num)
  have h0 : f 0 = g.integral φ.value := by
    dsimp only [f]
    simp_rw [g.potentialDensity_smul_zero, mul_one]
  have h1 : f 1 = g.integral (fun x => φ.value x * (g.potentialDensity φ).value x) := by
    dsimp only [f]
    simp_rw [g.potentialDensity_smul_one]
  have hpow : (1/2 : ℝ) ^ d = (1/2 : ℝ) ^ (d - 1) * (1/2) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
  rw [h0] at hh
  rw [h1] at he
  rw [hpow]
  nlinarith

lemma mongeAmpere_energy_density_bound [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ) (hd : 0 < d)
    (D : ℝ) (hD : ∀ x, |1 - (g.potentialDensity φ).value x| ≤ D) :
    (1/2 : ℝ) ^ d * g.integral (g.energy φ φ).value ≤ D * g.integral (fun x => |φ.value x|) := by
  refine (g.mongeAmpere_energy φ hp hd).trans ?_
  rw [← g.integral_sub φ.continuous (φ.continuous.fun_mul (g.potentialDensity φ).continuous),
    ← g.integral_const_mul]
  apply g.integral_mono (φ.continuous.sub (φ.continuous.fun_mul (g.potentialDensity φ).continuous))
    (continuous_const.mul φ.continuous.abs)
  intro x
  change φ.value x - φ.value x * (g.potentialDensity φ).value x ≤ D * |φ.value x|
  calc
    _ = φ.value x * (1 - (g.potentialDensity φ).value x) := by ring
    _ ≤ |φ.value x * (1 - (g.potentialDensity φ).value x)| := le_abs_self _
    _ = |φ.value x| * |1 - (g.potentialDensity φ).value x| := abs_mul _ _
    _ ≤ |φ.value x| * D := mul_le_mul_of_nonneg_left (hD x) (abs_nonneg _)
    _ = _ := mul_comm _ _

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
