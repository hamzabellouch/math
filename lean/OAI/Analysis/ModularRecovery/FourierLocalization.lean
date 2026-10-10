import OAI.Analysis.ModularRecovery.FourthMoments

namespace OAI

/-! Polar truncation and Fourier localization with a width-independent L1 bound. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma polarCutoff_vector_error_sq (xi : H) (z : H →L[ℂ] H) {K : ℝ} (hK : 0 < K) :
    ‖(z - polarCutoff z K) xi‖ ^ 2 ≤
      (K ^ 2)⁻¹ * (vectorStateLM xi ((star z * z) ^ 2)).re := by
  have hh := re_vectorState_mono xi (polarCutoff_error_le z hK)
  rw [vectorState_star_mul, LinearMap.map_smul_of_tower, Complex.smul_re] at hh
  exact hh

lemma norm_polarCutoff_vector_le (xi : H) (z : H →L[ℂ] H) {K : ℝ} (hK : 0 < K) :
    ‖polarCutoff z K xi‖ ≤ K * ‖xi‖ := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_polarCutoff_le z hK) (norm_nonneg _))

end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma norm_unitary_le_one (D : RealSpectralCalculus H) (t : ℝ) : ‖D.unitary t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simp [D.norm_unitary_apply]

def integratedUnitary (D : RealSpectralCalculus H) (k : ℝ → ℂ) (hk : Integrable k) : H →L[ℂ] H :=
  strongIntegral k hk D.unitary D.continuous_unitary_apply 1 D.norm_unitary_le_one

lemma integral_character_mul (f : BoundedContinuousFunction ℝ ℂ)
    (k : ℝ → ℂ) (hk : Integrable k)
    (hfk : ∀ u, f u = ∫ t, k t * spectralCharacter t u)
    (q : BoundedContinuousFunction ℝ ℂ) (hq : HasCompactSupport (q : ℝ → ℂ)) :
    Integrable (fun t => k t • (spectralCharacter t * q)) ∧
      (∫ t, k t • (spectralCharacter t * q)) = f * q := by
  have hbound (t : ℝ) : ‖spectralCharacter t * q‖ ≤ ‖q‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro u
    change ‖spectralCharacter t u * q u‖ ≤ ‖q‖
    simpa only [norm_mul, spectralCharacter_norm, one_mul] using q.norm_coe_le_norm u
  have hi := integrable_smul_bounded_orbit hk (continuous_character_mul q hq) hbound
  refine ⟨hi, ?_⟩
  ext u
  have hEval := (BoundedContinuousFunction.evalCLM ℂ u).integral_comp_comm hi
  change (∫ t, k t • (spectralCharacter t * q)) u = f u * q u
  change (BoundedContinuousFunction.evalCLM ℂ u) (∫ t, k t • (spectralCharacter t * q)) = _
  rw [← hEval, hfk u, ← integral_mul_const]
  congr 1
  funext t
  change k t * (spectralCharacter t u * q u) = k t * spectralCharacter t u * q u
  ring

lemma calculus_eq_integratedUnitary (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) (k : ℝ → ℂ) (hk : Integrable k)
    (hfk : ∀ u, f u = ∫ t, k t * spectralCharacter t u) :
    D.calculus f = D.integratedUnitary k hk := by
  have hclosed : IsClosed {h : H | D.calculus f h = D.integratedUnitary k hk h} :=
    isClosed_eq (D.calculus f).continuous (D.integratedUnitary k hk).continuous
  have hsub : {h : H | ∃ q : BoundedContinuousFunction ℝ ℂ,
      HasCompactSupport (q : ℝ → ℂ) ∧ ∃ v : H, D.calculus q v = h} ⊆
      {h : H | D.calculus f h = D.integratedUnitary k hk h} := by
    rintro h ⟨q, hq, v, rfl⟩
    obtain ⟨hi, heq⟩ := integral_character_mul f k hk hfk q hq
    change (D.calculus f * D.calculus q) v = _
    rw [← map_mul, ← heq]
    have hc := D.calculusCLM.integral_comp_comm hi
    change (D.calculusCLM (∫ t, k t • (spectralCharacter t * q))) v = _
    rw [← hc, ContinuousLinearMap.integral_apply (D.calculusCLM.integrable_comp hi)]
    change (∫ t, D.calculus (k t • (spectralCharacter t * q)) v) =
      ∫ t, k t • D.unitary t (D.calculus q v)
    simp only [map_smul, map_mul, smul_apply, mul_apply_eq_comp, unitary]
  have hall := closure_minimal hsub hclosed
  rw [D.nondegenerate.closure_eq] at hall
  exact ContinuousLinearMap.ext (fun h => hall (mem_univ h))

lemma calculus_apply_eq_integral (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) (k : ℝ → ℂ) (hk : Integrable k)
    (hfk : ∀ u, f u = ∫ t, k t * spectralCharacter t u) (h : H) :
    D.calculus f h = ∫ t, k t • D.unitary t h := by
  rw [D.calculus_eq_integratedUnitary f k hk hfk]
  rfl
end RealSpectralCalculus

namespace StandardModularData

def fourierFilter (S : StandardModularData H) (k : ℝ → ℂ) (hk : Integrable k)
    (a : H →L[ℂ] H) : H →L[ℂ] H :=
  strongIntegral k hk (fun t => S.sigma t a) (S.continuous_sigma_apply a) ‖a‖
    (fun t => (S.norm_sigma t a).le)

lemma norm_fourierFilter_le (S : StandardModularData H) (k : ℝ → ℂ) (hk : Integrable k)
    (a : H →L[ℂ] H) : ‖S.fourierFilter k hk a‖ ≤ (∫ t, ‖k t‖) * ‖a‖ :=
  norm_strongIntegral_le k hk _ _ (norm_nonneg a) _

lemma fourierFilter_mem (S : StandardModularData H) (k : ℝ → ℂ) (hk : Integrable k)
    {a : H →L[ℂ] H} (ha : a ∈ S.M) : S.fourierFilter k hk a ∈ S.M := by
  rw [← S.M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  apply ContinuousLinearMap.ext
  intro h
  have hi := integrable_smul_bounded_orbit hk (S.continuous_sigma_apply a h)
    (fun t => (S.sigma t a).le_opNorm h |>.trans_eq (by rw [S.norm_sigma]))
  change b (∫ t, k t • S.sigma t a h) = ∫ t, k t • S.sigma t a (b h)
  rw [← b.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [map_smul]
  congr 1
  have heq := (VonNeumannAlgebra.mem_commutant_iff.mp hb) (S.sigma t a) (S.sigma_mem t ha)
  exact (congrArg (fun c : H →L[ℂ] H => c h) heq).symm

lemma fourierFilter_apply_xi (S : StandardModularData H)
    (f : BoundedContinuousFunction ℝ ℂ) (k : ℝ → ℂ) (hk : Integrable k)
    (hfk : ∀ u, f u = ∫ t, k t * spectralCharacter t u) (a : H →L[ℂ] H) :
    S.fourierFilter k hk a S.xi = S.D.calculus f (a S.xi) := by
  rw [S.D.calculus_apply_eq_integral f k hk hfk]
  change (∫ t, k t • S.sigma t a S.xi) = _
  simp only [S.sigma_apply_xi]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace BoundedRecovery

def bump0 : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def bumpSchwartz : SchwartzMap ℝ ℂ :=
  ((bump0.hasCompactSupport.comp_homeomorph
      (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity))).comp_left
        (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (bump0.contDiff.comp (by
      change ContDiff ℝ _ (fun u : ℝ => 2 * Real.pi * u)
      fun_prop)))

@[simp] lemma bumpSchwartz_apply (u : ℝ) :
    bumpSchwartz u = (bump0 (2 * Real.pi * u) : ℂ) := rfl

def baseKernel : ℝ → ℂ := (𝓕 bumpSchwartz : SchwartzMap ℝ ℂ)

lemma baseKernel_integrable : Integrable baseKernel := (𝓕 bumpSchwartz).integrable

lemma bump0_fourier (u : ℝ) :
    (bump0 u : ℂ) = ∫ t, baseKernel t * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
  have hi := congrArg (fun f : SchwartzMap ℝ ℂ => f (u / (2 * Real.pi)))
    (FourierPair.fourierInv_fourier_eq (F := SchwartzMap ℝ ℂ) bumpSchwartz)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hi
  rw [bumpSchwartz_apply] at hi
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  have he : 2 * Real.pi * (u / (2 * Real.pi)) = u := by field_simp
  rw [he] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  change Complex.exp (((2 * Real.pi * ((u / (2 * Real.pi)) * t) : ℝ) : ℂ) * Complex.I) *
    (𝓕 bumpSchwartz) t = _
  have he' : 2 * Real.pi * ((u / (2 * Real.pi)) * t) = t * u := by field_simp
  rw [he']
  exact mul_comm _ _

def bandMultiplier (s rho : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u => (bump0 ((u-s)/rho) : ℂ))
    (Complex.continuous_ofReal.comp (bump0.continuous.comp (by fun_prop))) 1 (by
      intro u
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump0.nonneg]
        using (bump0.le_one (x := (u-s)/rho)))

@[simp] lemma bandMultiplier_apply (s rho u : ℝ) :
    bandMultiplier s rho u = (bump0 ((u-s)/rho) : ℂ) := rfl

lemma norm_bandMultiplier_le (s rho : ℝ) : ‖bandMultiplier s rho‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro u
  simpa only [bandMultiplier_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg bump0.nonneg] using (bump0.le_one (x := (u-s)/rho))

lemma bandMultiplier_one {s rho u : ℝ} (hrho : 0 < rho)
    (hu : u ∈ Icc (s-rho) (s+rho)) : bandMultiplier s rho u = 1 := by
  rw [bandMultiplier_apply, bump0.one_of_mem_closedBall]
  · simp
  · rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    change |(u-s)/rho| ≤ 1
    rw [abs_div, abs_of_pos hrho, div_le_one hrho]
    exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩

lemma bandMultiplier_zero {s rho u : ℝ} (hrho : 0 < rho)
    (hu : u ∉ Icc (s-2*rho) (s+2*rho)) : bandMultiplier s rho u = 0 := by
  rw [bandMultiplier_apply, bump0.zero_of_le_dist]
  · simp
  · rw [dist_zero_right, Real.norm_eq_abs]
    change 2 ≤ |(u-s)/rho|
    rw [abs_div, abs_of_pos hrho, le_div_iff₀ hrho]
    by_cases h : s-2*rho ≤ u
    · have h' : s+2*rho < u := lt_of_not_ge (fun hh => hu ⟨h,hh⟩)
      exact (by linarith : 2 * rho ≤ u-s).trans (le_abs_self _)
    · have h' : u < s-2*rho := lt_of_not_ge h
      exact (by linarith : 2 * rho ≤ -(u-s)).trans (neg_le_abs _)

def bandKernel (s rho : ℝ) (t : ℝ) : ℂ :=
  (rho : ℂ) * Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I) * baseKernel (rho*t)

lemma norm_bandKernel {s rho : ℝ} (hrho : 0 < rho) (t : ℝ) :
    ‖bandKernel s rho t‖ = rho * ‖baseKernel (rho*t)‖ := by
  simp [bandKernel, Complex.norm_exp, abs_of_pos hrho]

lemma bandKernel_integrable {s rho : ℝ} (hrho : 0 < rho) : Integrable (bandKernel s rho) := by
  have hi := (integrable_comp_mul_left_iff baseKernel hrho.ne').mpr baseKernel_integrable
  have hc : Continuous (fun t : ℝ => Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hi' := (hi.bdd_mul hc.aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall (fun t => by simp [Complex.norm_exp]))).const_mul (rho : ℂ)
  change Integrable (fun t => (rho : ℂ) * Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I) * baseKernel (rho*t))
  simpa only [mul_assoc] using hi'

lemma integral_norm_bandKernel {s rho : ℝ} (hrho : 0 < rho) :
    (∫ t, ‖bandKernel s rho t‖) = ∫ t, ‖baseKernel t‖ := by
  simp_rw [norm_bandKernel hrho]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun t => ‖baseKernel t‖) rho]
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hrho)]
  rw [← mul_assoc, mul_inv_cancel₀ hrho.ne', one_mul]

lemma bandMultiplier_fourier {s rho : ℝ} (hrho : 0 < rho) (u : ℝ) :
    bandMultiplier s rho u =
      ∫ t, bandKernel s rho t * Complex.exp (((t*u : ℝ) : ℂ) * Complex.I) := by
  rw [bandMultiplier_apply, bump0_fourier]
  have he (t : ℝ) :
      bandKernel s rho t * Complex.exp (((t*u : ℝ) : ℂ) * Complex.I) =
      (rho : ℂ) * (baseKernel (rho*t) *
        Complex.exp ((((rho*t)*((u-s)/rho) : ℝ) : ℂ) * Complex.I)) := by
    unfold bandKernel
    rw [show (rho : ℂ) * Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I) * baseKernel (rho*t) *
      Complex.exp (((t*u : ℝ) : ℂ) * Complex.I) =
      (rho : ℂ) * (baseKernel (rho*t) * (Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((t*u : ℝ) : ℂ) * Complex.I))) by ring, ← Complex.exp_add]
    congr 3
    have heR : -s*t + t*u = (rho*t)*((u-s)/rho) := by field_simp; ring
    rw [← add_mul, ← Complex.ofReal_add, heR]
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun t => baseKernel t * Complex.exp (((t*((u-s)/rho) : ℝ) : ℂ) * Complex.I)) rho]
  rw [abs_of_pos (inv_pos.mpr hrho)]
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hrho.ne',
    Complex.ofReal_one, one_mul]

end BoundedRecovery

noncomputable section
open Set MeasureTheory
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def filterL1 : ℝ := ∫ t, ‖baseKernel t‖
lemma filterL1_nonneg : 0 ≤ filterL1 := integral_nonneg (fun _ => norm_nonneg _)

namespace StandardModularData

def bandFilter (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    (a : H →L[ℂ] H) : H →L[ℂ] H :=
  S.fourierFilter (bandKernel s rho) (bandKernel_integrable hrho) a

lemma bandFilter_mem (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    {a : H →L[ℂ] H} (ha : a ∈ S.M) : S.bandFilter s rho hrho a ∈ S.M :=
  S.fourierFilter_mem _ _ ha

lemma norm_bandFilter_le (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    (a : H →L[ℂ] H) : ‖S.bandFilter s rho hrho a‖ ≤ filterL1 * ‖a‖ := by
  have hh := S.norm_fourierFilter_le (bandKernel s rho) (bandKernel_integrable hrho) a
  rw [integral_norm_bandKernel hrho] at hh
  exact hh

lemma bandFilter_apply_xi (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    (a : H →L[ℂ] H) : S.bandFilter s rho hrho a S.xi = S.D.calculus (bandMultiplier s rho) (a S.xi) :=
  S.fourierFilter_apply_xi _ _ _ (bandMultiplier_fourier hrho) a

lemma bandFilter_support (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    (a : H →L[ℂ] H) : S.D.HasSpectralSupport (Icc (s-2*rho) (s+2*rho))
      (S.bandFilter s rho hrho a S.xi) := by
  rw [S.bandFilter_apply_xi]
  exact S.D.support_calculus_apply _ _ (fun _u hu => bandMultiplier_zero hrho hu) _

lemma bandMultiplier_fixes (S : StandardModularData H) {s rho : ℝ} (hrho : 0 < rho)
    {h : H} (hh : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h) :
    S.D.calculus (bandMultiplier s rho) h = h := hh.fixed (fun _u hu => bandMultiplier_one hrho hu)

lemma bandMultiplier_contracts (S : StandardModularData H) (s rho : ℝ) (h : H) :
    ‖S.D.calculus (bandMultiplier s rho) h‖ ≤ ‖h‖ := by
  calc
    _ ≤ ‖bandMultiplier s rho‖ * ‖h‖ := S.D.norm_calculus_apply_le _ _
    _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right (norm_bandMultiplier_le s rho) (norm_nonneg _)
    _ = _ := one_mul _

lemma bandFilter_vector_error_le (S : StandardModularData H) {s rho : ℝ} (hrho : 0 < rho)
    (a : H →L[ℂ] H) {h : H} (hh : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h) :
    ‖S.bandFilter s rho hrho a S.xi - h‖ ≤ ‖a S.xi - h‖ := by
  rw [S.bandFilter_apply_xi, ← S.bandMultiplier_fixes hrho hh, ← map_sub]
  rw [S.bandMultiplier_fixes hrho hh]
  exact S.bandMultiplier_contracts s rho _

lemma exists_band_representative (S : StandardModularData H) {s rho : ℝ} (hrho : 0 < rho)
    {h : H} (hh : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h) (hn : ‖h‖ = 1)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ y : H →L[ℂ] H, y ∈ S.M ∧ ‖y S.xi‖ ≤ 2 ∧ ‖y S.xi - h‖ < eps ∧
      S.D.HasSpectralSupport (Icc (s-2*rho) (s+2*rho)) (y S.xi) := by
  obtain ⟨v,⟨a,ha,rfl⟩,hd⟩ := Metric.mem_closure_iff.mp (S.cyclic h) (min eps 1) (lt_min heps one_pos)
  have hsmall : ‖a S.xi - h‖ < min eps 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hd
  have hb := (S.bandFilter_vector_error_le hrho a hh).trans_lt hsmall
  have hbn : ‖S.bandFilter s rho hrho a S.xi‖ ≤ 2 := by
    have hh' := norm_le_norm_sub_add (S.bandFilter s rho hrho a S.xi) h
    rw [hn] at hh'
    have := hb.trans_le (min_le_right _ _)
    linarith
  exact ⟨S.bandFilter s rho hrho a, S.bandFilter_mem s rho hrho ha, hbn,
    hb.trans_le (min_le_left _ _), S.bandFilter_support s rho hrho a⟩

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
