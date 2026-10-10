import Mathlib
import OAI.Analysis.CoulombRadii.Localization.SmoothMultiplier

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem energy_localization_identity {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    {θ : Configuration n → ℝ} (hθ : SmoothMultiplier θ) :
    energy Z (multiplyWavefunction θ ψ) (multiplyGradient θ ψ g) =
      formMultiplierPairing Z ψ g (fun x => θ x^2) + localizationError ψ θ := by
  have hsq : SmoothMultiplier (fun x => θ x^2) := by
    simpa only [pow_two] using hθ.mul hθ
  have hi : ∀ σ i a, (∫ x : Configuration n, ‖multiplyGradient θ ψ g σ i a x‖^2) =
      (∫ x : Configuration n,
        inner ℝ (g σ i a x) (multiplyGradient (fun y => θ y^2) ψ g σ i a x)) +
      ∫ x : Configuration n, (fderiv ℝ θ x (coordinateDirection i a))^2*‖ψ σ x‖^2 := by
    intro σ i a
    simp_rw [norm_multiplyGradient_sq hθ.smooth]
    exact integral_add (integrable_real_inner_of_memLp (hd.2.2.2.1 σ i a)
      ((hd.multiply hsq).2.2.2.1 σ i a)) (integrable_localization_error hd.2.2.1 hθ σ i a)
  simp only [energy, formMultiplierPairing, localizationError, hi,
    norm_multiplyWavefunction_sq, Finset.sum_add_distrib,
    mul_left_comm (coulombPotential Z _)]
  ring

theorem groundState_localization {Z : ℕ} {ψ : Wavefunction Z}
    (hψ : IsNormalizedGroundState Z ψ) :
    ∃ g : Gradient Z, FormDomain ψ g ∧ normSquared ψ = 1 ∧
      ∀ (θ : Configuration Z → ℝ), SmoothMultiplier θ →
        energy Z (multiplyWavefunction θ ψ) (multiplyGradient θ ψ g) =
          energy Z ψ g*normSquared (multiplyWavefunction θ ψ) + localizationError ψ θ := by
  obtain ⟨g,hd,hn,hmin⟩ := hψ
  refine ⟨g,hd,hn,fun θ hθ => ?_⟩
  have hsq : SmoothMultiplier (fun x => θ x^2) := by
    simpa only [pow_two] using hθ.mul hθ
  rw [energy_localization_identity Z hd hθ, minimizer_multiplier_pairing Z hd hn hmin hsq]
  simp only [stateWeightedIntegral, normSquared, norm_multiplyWavefunction_sq]

theorem localizationError_nonneg {n : ℕ} (ψ : Wavefunction n) (θ : Configuration n → ℝ) :
    0 ≤ localizationError ψ θ := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))

theorem localizationError_le {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {θ : Configuration n → ℝ}
    (hθ : SmoothMultiplier θ) (C : Fin n → Fin 3 → ℝ)
    (hC : ∀ i a x, |fderiv ℝ θ x (coordinateDirection i a)| ≤ C i a) :
    localizationError ψ θ ≤ ((1/2:ℝ)*(∑ i : Fin n, ∑ a : Fin 3, (C i a)^2))*normSquared ψ := by
  have hi : ∀ σ i a, (∫ x : Configuration n,
      (fderiv ℝ θ x (coordinateDirection i a))^2*‖ψ σ x‖^2) ≤
      (C i a)^2 * (∫ x : Configuration n, ‖ψ σ x‖^2) := by
    intro σ i a
    rw [← integral_const_mul]
    apply integral_mono (integrable_localization_error hψ hθ σ i a)
      ((hψ σ).norm.integrable_sq.const_mul _)
    intro x
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC i a x) 2
  calc
    localizationError ψ θ ≤ (1/2:ℝ)*(∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
        (C i a)^2 * (∫ x : Configuration n, ‖ψ σ x‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun a _ => hi σ i a
    _ = ((1/2:ℝ)*(∑ i : Fin n, ∑ a : Fin 3, (C i a)^2))*normSquared ψ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, normSquared]
      ring

theorem groundState_normalized_localization {Z : ℕ} {ψ : Wavefunction Z}
    (hψ : IsNormalizedGroundState Z ψ) :
    ∃ g : Gradient Z, FormDomain ψ g ∧ normSquared ψ = 1 ∧
      ∀ (θ : Configuration Z → ℝ), SmoothMultiplier θ →
        ∀ _hn : 0 < normSquared (multiplyWavefunction θ ψ),
          let c := (Real.sqrt (normSquared (multiplyWavefunction θ ψ)))⁻¹
          FormDomain (scaleWavefunction c (multiplyWavefunction θ ψ))
            (scaleGradient c (multiplyGradient θ ψ g)) ∧
          normSquared (scaleWavefunction c (multiplyWavefunction θ ψ)) = 1 ∧
          energy Z (scaleWavefunction c (multiplyWavefunction θ ψ))
            (scaleGradient c (multiplyGradient θ ψ g)) = energy Z ψ g +
              localizationError ψ θ / normSquared (multiplyWavefunction θ ψ) := by
  obtain ⟨g,hd,hn,hloc⟩ := groundState_localization hψ
  refine ⟨g,hd,hn,fun θ hθ hnθ => ?_⟩
  dsimp only
  let c := (Real.sqrt (normSquared (multiplyWavefunction θ ψ)))⁻¹
  change FormDomain (scaleWavefunction c (multiplyWavefunction θ ψ))
      (scaleGradient c (multiplyGradient θ ψ g)) ∧ _
  have hc : c^2 = (normSquared (multiplyWavefunction θ ψ))⁻¹ := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hnθ.le]
  refine ⟨(hd.multiply hθ).scale c, ?_, ?_⟩
  · rw [normSquared_scale, hc, inv_mul_cancel₀ hnθ.ne']
  · rw [energy_scale, hc, hloc θ hθ]
    field_simp

theorem tendsto_integral_bounded_real_smul
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure X}
    {F : ℕ → X → ℝ} {F₀ : X → ℝ} {f : X → E} {C : ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hb : ∀ k x, |F k x| ≤ C) (hf : Integrable f μ)
    (hl : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (F₀ x))) :
    Tendsto (fun k => ∫ x, F k x • f x ∂μ) atTop
      (𝓝 (∫ x, F₀ x • f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖f x‖)
  · intro k
    exact (hF k).smul hf.aestronglyMeasurable
  · exact hf.norm.const_mul C
  · intro k
    exact Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb k x) (norm_nonneg _)
  · exact Eventually.of_forall fun x => (hl x).smul tendsto_const_nhds

theorem tendsto_integral_two_bounded_real_smul
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure X}
    {F G : ℕ → X → ℝ} {F₀ G₀ : X → ℝ} {f g : X → E} {C D : ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hG : ∀ k, AEStronglyMeasurable (G k) μ)
    (hbF : ∀ k x, |F k x| ≤ C) (hbG : ∀ k x, |G k x| ≤ D)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hlF : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (F₀ x)))
    (hlG : ∀ x, Tendsto (fun k => G k x) atTop (𝓝 (G₀ x))) :
    Tendsto (fun k => ∫ x, F k x • f x + G k x • g x ∂μ) atTop
      (𝓝 (∫ x, F₀ x • f x + G₀ x • g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => C * ‖f x‖ + D * ‖g x‖)
  · intro k
    exact ((hF k).smul hf.aestronglyMeasurable).add
      ((hG k).smul hg.aestronglyMeasurable)
  · exact (hf.norm.const_mul C).add (hg.norm.const_mul D)
  · intro k
    exact Eventually.of_forall fun x => by
      calc
        ‖F k x • f x + G k x • g x‖ ≤ ‖F k x • f x‖ + ‖G k x • g x‖ := norm_add_le _ _
        _ ≤ C * ‖f x‖ + D * ‖g x‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (hbF k x) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hbG k x) (norm_nonneg _))
  · exact Eventually.of_forall fun x =>
      ((hlF x).smul tendsto_const_nhds).add ((hlG x).smul tendsto_const_nhds)

def explicitMultiplyGradient {n : ℕ} (θ : Configuration n → ℝ)
    (Dθ : Fin n → Fin 3 → Configuration n → ℝ)
    (ψ : Wavefunction n) (g : Gradient n) : Gradient n :=
  fun σ i a x => Dθ i a x • ψ σ x + θ x • g σ i a x

theorem HasWeakGradient.multiply_limit {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hgLp : ∀ σ i a, MemLp (g σ i a) 2 volume)
    {θ : Configuration n → ℝ} {Dθ : Fin n → Fin 3 → Configuration n → ℝ}
    {θk : ℕ → Configuration n → ℝ}
    (hθk : ∀ k, ContDiff ℝ ∞ (θk k))
    (hb : ∃ C : ℝ, ∀ k x, |θk k x| ≤ C)
    (hdb : ∀ i a, ∃ C : ℝ, ∀ k x,
      |fderiv ℝ (θk k) x (coordinateDirection i a)| ≤ C)
    (hl : ∀ x, Tendsto (fun k => θk k x) atTop (𝓝 (θ x)))
    (hdl : ∀ i a x, Tendsto
      (fun k => fderiv ℝ (θk k) x (coordinateDirection i a)) atTop (𝓝 (Dθ i a x))) :
    HasWeakGradient (multiplyWavefunction θ ψ) (explicitMultiplyGradient θ Dθ ψ g) := by
  intro σ i a φ hφ hφc
  let dφ : Configuration n → ℝ := fun x => fderiv ℝ φ x (coordinateDirection i a)
  have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport dφ := hφc.fderiv_apply ℝ _
  obtain ⟨C,hC⟩ := hb
  obtain ⟨B,hB⟩ := hdb i a
  have hi₁ := integrable_test_real_smul (hψ σ) hdφ hdφc
  have hi₂ := integrable_test_real_smul (hψ σ) hφ.continuous hφc
  have hi₃ := integrable_test_real_smul (hgLp σ i a) hφ.continuous hφc
  have hleft := tendsto_integral_bounded_real_smul
    (fun k => (hθk k).continuous.aestronglyMeasurable) hC hi₁ hl
  have hright := tendsto_integral_two_bounded_real_smul
    (fun k => ((hθk k).continuous_fderiv (by simp)).clm_apply continuous_const |>.aestronglyMeasurable)
    (fun k => (hθk k).continuous.aestronglyMeasurable) hB hC hi₂ hi₃ (hdl i a) hl
  have heq : ∀ k,
      (∫ x, θk k x • (dφ x • ψ σ x)) =
      -(∫ x, (fderiv ℝ (θk k) x (coordinateDirection i a)) • (φ x • ψ σ x) +
        θk k x • (φ x • g σ i a x)) := by
    intro k
    have h := hg.multiply hψ hgLp (hθk k) σ i a φ hφ hφc
    change (∫ x, dφ x • (θk k x • ψ σ x)) =
      -(∫ x, φ x • ((fderiv ℝ (θk k) x (coordinateDirection i a)) • ψ σ x +
        θk k x • g σ i a x)) at h
    simpa only [smul_add, smul_smul, mul_comm] using h
  have ht := tendsto_nhds_unique hleft (hright.neg.congr' (Eventually.of_forall fun k => (heq k).symm))
  change (∫ x, dφ x • (θ x • ψ σ x)) =
    -(∫ x, φ x • (Dθ i a x • ψ σ x + θ x • g σ i a x))
  simpa only [smul_add, smul_smul, mul_comm] using ht

theorem memLp_bounded_measurable_real_smul {n : ℕ} {f : Configuration n → ℂ}
    (hf : MemLp f 2 volume) {θ : Configuration n → ℝ}
    (hθ : AEStronglyMeasurable θ volume)
    (hb : ∃ C : ℝ, ∀ x, |θ x| ≤ C) : MemLp (fun x => θ x • f x) 2 volume := by
  obtain ⟨C,hC⟩ := hb
  apply hf.of_le_mul (c := C) (hθ.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖θ x • f x‖ ≤ C * ‖f x‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem FormDomain.multiply_limit {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : FormDomain ψ g)
    {θ : Configuration n → ℝ} {Dθ : Fin n → Fin 3 → Configuration n → ℝ}
    {θk : ℕ → Configuration n → ℝ}
    (hθ : Continuous θ) (hsym : ∀ (p : Equiv.Perm (Fin n)) x, θ (x ∘ p) = θ x)
    (hD : ∀ i a, AEStronglyMeasurable (Dθ i a) volume)
    (hθk : ∀ k, ContDiff ℝ ∞ (θk k))
    (hb : ∃ C : ℝ, ∀ k x, |θk k x| ≤ C)
    (hdb : ∀ i a, ∃ C : ℝ, ∀ k x,
      |fderiv ℝ (θk k) x (coordinateDirection i a)| ≤ C)
    (hl : ∀ x, Tendsto (fun k => θk k x) atTop (𝓝 (θ x)))
    (hdl : ∀ i a x, Tendsto
      (fun k => fderiv ℝ (θk k) x (coordinateDirection i a)) atTop (𝓝 (Dθ i a x))) :
    FormDomain (multiplyWavefunction θ ψ) (explicitMultiplyGradient θ Dθ ψ g) := by
  have hbθ : ∃ C : ℝ, ∀ x, |θ x| ≤ C := by
    obtain ⟨C,hC⟩ := hb
    exact ⟨C, fun x => le_of_tendsto (hl x).abs (Eventually.of_forall fun k => hC k x)⟩
  have hbD : ∀ i a, ∃ C : ℝ, ∀ x, |Dθ i a x| ≤ C := by
    intro i a
    obtain ⟨C,hC⟩ := hdb i a
    exact ⟨C, fun x => le_of_tendsto (hdl i a x).abs (Eventually.of_forall fun k => hC k x)⟩
  refine ⟨hg.1.multiply hsym,
    hg.2.1.multiply_limit hg.2.2.1 hg.2.2.2.1 hθk hb hdb hl hdl, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact memLp_bounded_real_smul (hg.2.2.1 σ) hθ hbθ
  · intro σ i a
    exact (memLp_bounded_measurable_real_smul (hg.2.2.1 σ) (hD i a) (hbD i a)).add
      (memLp_bounded_real_smul (hg.2.2.2.1 σ i a) hθ hbθ)
  · intro σ i
    exact integrable_weight_multiply hθ hbθ ψ σ (hg.2.2.2.2.1 σ i)
  · intro σ i j hij
    exact integrable_weight_multiply hθ hbθ ψ σ (hg.2.2.2.2.2 σ i j hij)

def explicitLocalizationError {n : ℕ} (ψ : Wavefunction n)
    (Dθ : Fin n → Fin 3 → Configuration n → ℝ) : ℝ :=
  (1/2:ℝ)*(∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
    ∫ x : Configuration n, (Dθ i a x)^2*‖ψ σ x‖^2)

theorem energy_localization_explicit {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {θ : Configuration n → ℝ}
    {Dθ : Fin n → Fin 3 → Configuration n → ℝ}
    (hsq : SmoothMultiplier (fun x => θ x^2))
    (hD : ∀ i a, AEStronglyMeasurable (Dθ i a) volume)
    (hDb : ∀ i a, ∃ C : ℝ, ∀ x, |Dθ i a x| ≤ C)
    (hrel : ∀ i a x, fderiv ℝ (fun y => θ y^2) x (coordinateDirection i a) =
      2*θ x*Dθ i a x) :
    energy Z (multiplyWavefunction θ ψ) (explicitMultiplyGradient θ Dθ ψ g) =
      formMultiplierPairing Z ψ g (fun x => θ x^2) + explicitLocalizationError ψ Dθ := by
  have hpw : ∀ σ i a x, ‖explicitMultiplyGradient θ Dθ ψ g σ i a x‖^2 =
      inner ℝ (g σ i a x) (multiplyGradient (fun y => θ y^2) ψ g σ i a x) +
      (Dθ i a x)^2*‖ψ σ x‖^2 := by
    intro σ i a x
    simp only [explicitMultiplyGradient, multiplyGradient, hrel, norm_add_sq_real, norm_smul,
      inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm (ψ σ x) (g σ i a x)]
    ring
  have herr : ∀ σ i a, Integrable (fun x : Configuration n => (Dθ i a x)^2*‖ψ σ x‖^2) := by
    intro σ i a
    have hl := memLp_bounded_measurable_real_smul (hd.2.2.1 σ) (hD i a) (hDb i a)
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hl.norm.integrable_sq
  have hi : ∀ σ i a, (∫ x : Configuration n, ‖explicitMultiplyGradient θ Dθ ψ g σ i a x‖^2) =
      (∫ x : Configuration n,
        inner ℝ (g σ i a x) (multiplyGradient (fun y => θ y^2) ψ g σ i a x)) +
      ∫ x : Configuration n, (Dθ i a x)^2*‖ψ σ x‖^2 := by
    intro σ i a
    simp_rw [hpw]
    exact integral_add (integrable_real_inner_of_memLp (hd.2.2.2.1 σ i a)
      ((hd.multiply hsq).2.2.2.1 σ i a)) (herr σ i a)
  simp only [energy, formMultiplierPairing, explicitLocalizationError, hi,
    norm_multiplyWavefunction_sq, Finset.sum_add_distrib, mul_left_comm (coulombPotential Z _)]
  ring

open scoped ENNReal Convolution

def observationNoiseBase (u : ℝ) : ℝ := expNegInvGlue (1-u^2)

theorem observationNoiseBase_contDiff : ContDiff ℝ ∞ observationNoiseBase :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem observationNoiseBase_nonneg (u : ℝ) : 0 ≤ observationNoiseBase u :=
  expNegInvGlue.nonneg _

theorem observationNoiseBase_formula (u : ℝ) :
    observationNoiseBase u = if |u| < 1 then Real.exp (-(1-u^2)⁻¹) else 0 := by
  have he : 0 < 1-u^2 ↔ |u| < 1 := by
    rw [abs_lt]
    constructor
    · intro hh
      constructor <;> nlinarith [sq_nonneg (u+1), sq_nonneg (u-1)]
    · rintro ⟨hl,hu⟩
      nlinarith [mul_pos (by linarith : 0 < u+1) (by linarith : 0 < 1-u)]
  unfold observationNoiseBase expNegInvGlue
  by_cases hu : |u| < 1
  · simp [hu, not_le.mpr (he.mpr hu)]
  · simp [hu, le_of_not_gt (he.not.mpr hu)]

theorem observationNoiseBase_compact : HasCompactSupport observationNoiseBase := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))
  intro u hu
  rw [observationNoiseBase_formula, ite_eq_right]
  intro hh
  exact hu ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩

theorem observationNoiseBase_integrable : Integrable observationNoiseBase :=
  observationNoiseBase_contDiff.continuous.integrable_of_hasCompactSupport
    observationNoiseBase_compact

theorem observationNoiseBase_integral_pos : 0 < ∫ u, observationNoiseBase u := by
  apply integral_pos_of_integrable_nonneg_nonzero
    observationNoiseBase_contDiff.continuous observationNoiseBase_integrable
    observationNoiseBase_nonneg (x := 0)
  exact (expNegInvGlue.pos_of_pos (by norm_num : (0:ℝ) < 1-0^2)).ne'

def observationNoiseNormalizer : ℝ := (∫ u, observationNoiseBase u)⁻¹

def observationNoiseDensity (u : ℝ) : ℝ := observationNoiseNormalizer*observationNoiseBase u

theorem observationNoiseDensity_nonneg (u : ℝ) : 0 ≤ observationNoiseDensity u :=
  mul_nonneg (inv_nonneg.mpr observationNoiseBase_integral_pos.le)
    (observationNoiseBase_nonneg u)

theorem observationNoiseDensity_contDiff : ContDiff ℝ ∞ observationNoiseDensity :=
  contDiff_const.mul observationNoiseBase_contDiff

theorem observationNoiseDensity_integrable : Integrable observationNoiseDensity :=
  observationNoiseBase_integrable.const_mul _

theorem observationNoiseDensity_mass : (∫ u, observationNoiseDensity u) = 1 := by
  unfold observationNoiseDensity
  rw [integral_const_mul, observationNoiseNormalizer]
  exact inv_mul_cancel₀ observationNoiseBase_integral_pos.ne'

def observationNoiseLaw : Measure ℝ := volume.withDensity
  (fun u => ENNReal.ofReal (observationNoiseDensity u))

instance observationNoiseLaw_probability : IsProbabilityMeasure observationNoiseLaw := by
  constructor
  rw [observationNoiseLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal observationNoiseDensity_integrable
      (Filter.Eventually.of_forall observationNoiseDensity_nonneg), observationNoiseDensity_mass]
  norm_num

theorem observationNoiseDensity_formula (u : ℝ) :
    observationNoiseDensity u = observationNoiseNormalizer*
      (if |u| < 1 then Real.exp (-(1-u^2)⁻¹) else 0) := by
  rw [observationNoiseDensity, observationNoiseBase_formula]

def observationTranslationScore (u : ℝ) : ℝ := 2 * u / (1-u^2)^2

theorem observationTranslationScore_measurable : Measurable observationTranslationScore := by
  unfold observationTranslationScore
  fun_prop

theorem observationNoiseDensity_even (u : ℝ) :
    observationNoiseDensity (-u) = observationNoiseDensity u := by
  simp [observationNoiseDensity, observationNoiseBase]

theorem observationTranslationScore_odd (u : ℝ) :
    observationTranslationScore (-u) = -observationTranslationScore u := by
  simp [observationTranslationScore, neg_div]

theorem observationNoiseDensity_hasDerivAt (u : ℝ) :
    HasDerivAt observationNoiseDensity
      (-observationTranslationScore u * observationNoiseDensity u) u := by
  have hg : HasDerivAt expNegInvGlue
      ((1-u^2)⁻¹ ^ 2 * expNegInvGlue (1-u^2)) (1-u^2) := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (1-u^2)
  have hi : HasDerivAt (fun v : ℝ => 1-v^2) (-2*u) u := by
    convert! (hasDerivAt_pow 2 u).const_sub 1 using 1
    ring
  convert! (hg.comp u hi).const_mul observationNoiseNormalizer using 1
  simp only [observationNoiseDensity, observationNoiseBase, observationTranslationScore,
    div_eq_mul_inv, inv_pow]
  ring

theorem pow_mul_exp_neg_le_factorial (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t^k * Real.exp (-t) ≤ (k.factorial : ℝ) := by
  have hk : (0:ℝ) < k.factorial := by positivity
  have h := (div_le_iff₀ hk).mp (Real.pow_div_factorial_le_exp t ht k)
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-t)).le
  simpa [Real.exp_neg, mul_assoc, mul_left_comm, mul_comm] using hh

theorem observationScore_weighted_pow_bound (q : ℕ) (u : ℝ) :
    |observationTranslationScore u|^q * observationNoiseDensity u ≤
      (Set.Icc (-1:ℝ) 1).indicator
        (fun _ => observationNoiseNormalizer * 2^q * ((2*q).factorial : ℝ)) u := by
  classical
  have hc : 0 ≤ observationNoiseNormalizer :=
    inv_nonneg.mpr observationNoiseBase_integral_pos.le
  by_cases hu : |u| < 1
  · have hb : u ∈ Set.Icc (-1:ℝ) 1 :=
      ⟨(abs_lt.mp hu).1.le, (abs_lt.mp hu).2.le⟩
    rw [Set.indicator_of_mem hb, observationNoiseDensity_formula, ite_eq_left hu]
    have hv : 0 < 1-u^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one u).mpr hu)
    have hs : |observationTranslationScore u| ≤ 2 * ((1-u^2)⁻¹)^2 := by
      unfold observationTranslationScore
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_pow, abs_of_pos hv]
      rw [div_eq_mul_inv, inv_pow]
      nlinarith [mul_le_mul_of_nonneg_right hu.le
        (inv_nonneg.mpr (sq_nonneg (1-u^2)))]
    calc
      |observationTranslationScore u|^q *
          (observationNoiseNormalizer * Real.exp (-(1-u^2)⁻¹)) ≤
          (2 * ((1-u^2)⁻¹)^2)^q *
            (observationNoiseNormalizer * Real.exp (-(1-u^2)⁻¹)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hs q)
          (mul_nonneg hc (Real.exp_pos _).le)
      _ = (observationNoiseNormalizer * 2^q) *
          (((1-u^2)⁻¹)^(2*q) * Real.exp (-(1-u^2)⁻¹)) := by
        rw [mul_pow, pow_mul]; ring
      _ ≤ (observationNoiseNormalizer * 2^q) * ((2*q).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left
          (pow_mul_exp_neg_le_factorial (2*q) (inv_nonneg.mpr hv.le))
          (mul_nonneg hc (by positivity))
  · rw [observationNoiseDensity_formula, ite_eq_right hu]
    simp only [mul_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) u

end NeutralAtom
end
end
end

end OAI
