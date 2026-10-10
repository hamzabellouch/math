import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction

namespace HarmonicCounterexample.Analytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def boundedDistribution (f : E →ᵇ ℂ) : 𝓢'(E,ℂ) :=
  ((f.memLp_top (μ := volume)).toLp f : Lp ℂ ⊤ (volume : Measure E))

lemma boundedDistribution_apply (f : E →ᵇ ℂ) (φ : 𝓢(E,ℂ)) :
    boundedDistribution f φ = ∫ x, φ x * f x := by
  rw [boundedDistribution,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(f.memLp_top (μ := volume)).coeFn_toLp] with x hx
  rw [hx,smul_eq_mul]

lemma integral_inverseFourier_mul (φ : 𝓢(E,ℂ)) (u : Lp ℂ 1 (volume : Measure E)) :
    (∫ x, (𝓕⁻ φ) x * u x) = ∫ x, φ x * (𝓕⁻ (u : E → ℂ)) x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -(innerₗ E)) (μ := volume) (ν := volume)
    Real.continuous_fourierChar (by change Continuous (fun p : E × E ↦ -inner ℝ p.1 p.2); fun_prop) φ.integrable (L1.integrable_coeFn u)
  simpa only [SchwartzMap.fourierInv_coe,Real.fourierInv_eq,
    VectorFourier.fourierIntegral,LinearMap.neg_apply,innerₗ_apply_apply,
    LinearMap.flip_apply,neg_neg,real_inner_comm,smul_eq_mul] using h

lemma inverseFourier_boundedDistribution (u : Lp ℂ 1 (volume : Measure E)) :
    𝓕⁻ (u : 𝓢'(E,ℂ)) = boundedDistribution (Real.Lp.fourierTransformInv u) := by
  ext φ
  rw [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,
    boundedDistribution_apply]
  simp only [smul_eq_mul,Real.Lp.fourierTransformInv_apply]
  exact integral_inverseFourier_mul φ u

theorem sobolev_exists_continuous {s : ℝ} (hs : Module.finrank ℝ E < 2*s)
    (f : 𝓢'(E,ℂ)) (hf : MemSobolev s 2 f) :
    ∃ U : E →ᵇ ℂ, boundedDistribution U = f := by
  obtain ⟨v,hv⟩ := hf.fourier_memL1 hs
  refine ⟨Real.Lp.fourierTransformInv v,?_⟩
  rw [← inverseFourier_boundedDistribution,← hv,fourierInv_fourier_eq]

open Laplacian Real in
lemma besselPotential_two (f : 𝓢'(E,ℂ)) :
    besselPotential E ℂ 2 f = f - ((2*π)^2)⁻¹ • Δ f := by
  have ha : (fun x : E ↦ Complex.ofReal (1+‖x‖^2)) =
      (fun _ : E ↦ (1:ℂ)) + (fun x : E ↦ Complex.ofReal (‖x‖^2)) := by
    ext x
    simp
  have hm : fourierMultiplierCLM ℂ (fun x : E ↦ Complex.ofReal (1+‖x‖^2)) f =
      f + fourierMultiplierCLM ℂ (fun x : E ↦ Complex.ofReal (‖x‖^2)) f := by
    simp only [ha,fourierMultiplierCLM_apply]
    rw [smulLeftCLM_add (by fun_prop) (by fun_prop)]
    simp
  rw [besselPotential]
  norm_num only [div_self (by norm_num : (2:ℝ) ≠ 0),Real.rpow_one]
  change fourierMultiplierCLM ℂ (fun x : E ↦ Complex.ofReal (1+‖x‖^2)) f = _
  rw [hm,laplacian_eq_fourierMultiplierCLM]
  rw [smul_smul]
  have hc : ((2*π)^2)⁻¹ * (-(2*π)^2) = (-1:ℝ) := by
    have hp : (2*π)^2 ≠ (0:ℝ) := by positivity
    field_simp
  rw [hc,neg_one_smul,sub_neg_eq_add]

open Laplacian in

theorem laplacianL2_exists_continuous (hdim : Module.finrank ℝ E < 4)
    (u v : Lp ℂ 2 (volume : Measure E))
    (hv : Δ (u : 𝓢'(E,ℂ)) = v) :
    ∃ U : E →ᵇ ℂ, boundedDistribution U = (u : 𝓢'(E,ℂ)) := by
  apply sobolev_exists_continuous (s:=2) (by exact_mod_cast hdim)
  refine ⟨u - (((2*Real.pi)^2)⁻¹ : ℝ) • v,?_⟩
  rw [besselPotential_two,hv]
  change _ = Lp.toTemperedDistributionCLM ℂ volume 2 (u - (((2*Real.pi)^2)⁻¹ : ℝ) • v)
  rw [map_sub,ContinuousLinearMap.map_smul_of_tower]
  rfl

lemma boundedDistribution_eq_L2_ae (U : E →ᵇ ℂ) (u : Lp ℂ 2 (volume : Measure E))
    (h : boundedDistribution U = (u : 𝓢'(E,ℂ))) :
    (U : E → ℂ) =ᵐ[volume] (u : E → ℂ) := by
  have hU : LocallyIntegrable (U : E → ℂ) (volume : Measure E) := U.continuous.locallyIntegrable
  have hu : LocallyIntegrable (u : E → ℂ) (volume : Measure E) :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have hz : ∀ᵐ x ∂(volume : Measure E), U x-u x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (hU.sub hu)
    intro φ hφ hc
    let ψ : 𝓢(E,ℂ) := (hc.comp_left (show Complex.ofRealCLM (0:ℝ) = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
    have he := congrArg (fun f : 𝓢'(E,ℂ) ↦ f ψ) h
    rw [boundedDistribution_apply,Lp.toTemperedDistribution_apply] at he
    have h1 := hU.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
    have h2 := hu.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
    change (∫ x, φ x • (U x-u x)) = 0
    simp_rw [smul_sub]
    rw [integral_sub h1 h2]
    apply sub_eq_zero.mpr
    convert he using 1 <;> apply integral_congr_ae <;> filter_upwards [] with x
    · change φ x • U x = Complex.ofReal (φ x)*U x
      exact Complex.real_smul
    · change φ x • u x = Complex.ofReal (φ x) • u x
      simp only [Complex.real_smul,smul_eq_mul]
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx


lemma sobolevWeight_memLp {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    MemLp (fun x : E ↦ Complex.ofReal ((1+‖x‖^2)^(-s/2))) 2 (volume : Measure E) := by
  have h : MemLp (fun x : E ↦ (1+‖x‖^2)^(-s/2)) 2 (volume : Measure E) := by
    have hg : (fun x : E ↦ (1+‖x‖^2)^(-s/2)).HasTemperateGrowth := by fun_prop
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) (by norm_num) hg.1.continuous.aestronglyMeasurable]
    suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1+‖a‖^2)^(-s)‖ < ⊤ from by
      norm_cast
      simp_rw [ofReal_norm] at h
      simp_rw [← enorm_pow]
      convert h
      rw [← Real.rpow_mul_natCast (by positivity)]
      simp
    apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_eq_self.mpr (by positivity)]
    congr
    ring
  exact h.ofReal

theorem sobolev_continuous_bound {s : ℝ} (hs : Module.finrank ℝ E < 2*s)
    (f : 𝓢'(E,ℂ)) (g : Lp ℂ 2 (volume : Measure E))
    (hg : besselPotential E ℂ s f = (g : 𝓢'(E,ℂ))) :
    ∃ U : E →ᵇ ℂ, boundedDistribution U = f ∧
      ‖U‖ ≤ (‖Real.Lp.fourierTransformInvCLM E ℂ‖ *
        ‖(sobolevWeight_memLp hs).toLp _‖)*‖g‖ := by
  let w : Lp ℂ 2 (volume : Measure E) := (sobolevWeight_memLp hs).toLp _
  let u : Lp ℂ 2 (volume : Measure E) := 𝓕 g
  have hu : smulLeftCLM ℂ (fun x : E ↦ ((1+‖x‖^2)^(s/2) : ℝ)) (𝓕 f) = (u : 𝓢'(E,ℂ)) := by
    have h := congrArg (fun z : 𝓢'(E,ℂ) ↦ 𝓕 z) hg
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      Lp.fourier_toTemperedDistribution_eq] at h
    exact h
  let v : Lp ℂ 1 (volume : Measure E) := w • u
  have hv : (v : 𝓢'(E,ℂ)) = 𝓕 f := by
    change (((sobolevWeight_memLp hs).toLp _ • u : Lp ℂ 1 (volume : Measure E)) : 𝓢'(E,ℂ)) = _
    rw [Lp.toTemperedDistribution_smul_eq]
    · rw [← hu,smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      have hp : (fun x : E ↦ Complex.ofReal ((1+‖x‖^2)^(s/2))) *
          (fun x : E ↦ Complex.ofReal ((1+‖x‖^2)^(-s/2))) = (fun _ : E ↦ (1:ℂ)) := by
        ext x
        rw [Pi.mul_apply]
        norm_cast
        rw [← Real.rpow_add (by positivity)]
        ring_nf
        simp
      rw [hp,smulLeftCLM_const,one_smul]
    · fun_prop
  refine ⟨Real.Lp.fourierTransformInv v,?_,?_⟩
  · rw [← inverseFourier_boundedDistribution,hv,fourierInv_fourier_eq]
  · have h1 : ‖Real.Lp.fourierTransformInv v‖ ≤ ‖Real.Lp.fourierTransformInvCLM E ℂ‖*‖v‖ :=
      (Real.Lp.fourierTransformInvCLM E ℂ).le_opNorm v
    have h2 : ‖v‖ ≤ ‖w‖*‖u‖ := Lp.norm_smul_le w u
    have hu' : ‖u‖ = ‖g‖ := Lp.norm_fourier_eq g
    rw [hu'] at h2
    exact h1.trans (by simpa only [mul_assoc,w] using
      mul_le_mul_of_nonneg_left h2 (norm_nonneg (Real.Lp.fourierTransformInvCLM E ℂ)))

open Laplacian in

theorem laplacianL2_continuous_estimate (hdim : Module.finrank ℝ E < 4) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u v : Lp ℂ 2 (volume : Measure E),
      Δ (u : 𝓢'(E,ℂ)) = v → ∃ U : E →ᵇ ℂ,
        (U : E → ℂ) =ᵐ[volume] u ∧ ‖U‖ ≤ B*(‖u‖+‖v‖) := by
  let η : ℝ := ((2*Real.pi)^2)⁻¹
  have hη : 0 ≤ η := by dsimp [η]; positivity
  let hdim' : (Module.finrank ℝ E : ℝ) < 2*(2:ℝ) := by exact_mod_cast hdim
  let B : ℝ := ‖Real.Lp.fourierTransformInvCLM E ℂ‖ *
    ‖(sobolevWeight_memLp hdim').toLp _‖
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨B*max 1 η,mul_nonneg hB (le_max_of_le_left zero_le_one),fun u v hv ↦ ?_⟩
  obtain ⟨U,hU,hUn⟩ := sobolev_continuous_bound hdim' (u : 𝓢'(E,ℂ)) (u-η • v) (by
    rw [besselPotential_two,hv]
    change _ = Lp.toTemperedDistributionCLM ℂ volume 2 (u-η • v)
    rw [map_sub,ContinuousLinearMap.map_smul_of_tower]
    rfl)
  refine ⟨U,boundedDistribution_eq_L2_ae U u hU,hUn.trans ?_⟩
  have hnorm : ‖u-η • v‖ ≤ max 1 η * (‖u‖+‖v‖) := by
    have h1 := norm_sub_le u (η • v)
    rw [norm_smul,Real.norm_of_nonneg hη] at h1
    have h2 := mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) η) (norm_nonneg u)
    have h3 := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) η) (norm_nonneg v)
    nlinarith
  simpa only [←mul_assoc,B] using mul_le_mul_of_nonneg_left hnorm hB

end HarmonicCounterexample.Analytic

end

end OAI
