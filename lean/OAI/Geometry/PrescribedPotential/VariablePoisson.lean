import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevParametrix

namespace OAI

/-! Variable Poisson. -/

section

 

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Real

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 
def secondH2Symbol (v w ξ : E) : ℂ :=
  (-(2 * Real.pi)^2 : ℂ) * (inner ℝ ξ v : ℂ) * (inner ℝ ξ w : ℂ) *
    ((1 + ‖ξ‖^2)^(-1 : ℝ) : ℝ)

lemma secondH2Symbol_temperate (v w : E) :
    (secondH2Symbol v w).HasTemperateGrowth := by
  unfold secondH2Symbol
  fun_prop

lemma secondH2Symbol_bound (v w ξ : E) :
    ‖secondH2Symbol v w ξ‖ ≤ (2 * Real.pi)^2 * ‖v‖ * ‖w‖ := by
  have hp : 0 < 1 + ‖ξ‖^2 := by positivity
  have hv := abs_real_inner_le_norm ξ v
  have hw := abs_real_inner_le_norm ξ w
  have hmul := mul_le_mul hv hw (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hle : |inner ℝ ξ v| * |inner ℝ ξ w| ≤
      (1 + ‖ξ‖^2) * (‖v‖ * ‖w‖) := by
    have hnonneg : 0 ≤ ‖v‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  simp only [secondH2Symbol, norm_mul, norm_neg, norm_pow, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Real.rpow_neg_one,
    abs_inv, abs_of_pos hp]
  have hpi : 0 ≤ (2 * Real.pi)^2 := sq_nonneg _
  calc
    _ = (2 * Real.pi)^2 * ((|inner ℝ ξ v| * |inner ℝ ξ w|) / (1 + ‖ξ‖^2)) := by ring
    _ ≤ (2 * Real.pi)^2 * (‖v‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ hp).mpr (by nlinarith [hle])) hpi
    _ = _ := by ring

def secondH2SymbolBCF (v w : E) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (secondH2Symbol v w)
    (secondH2Symbol_temperate v w).1.continuous
    ((2 * Real.pi)^2 * ‖v‖ * ‖w‖) (secondH2Symbol_bound v w)

lemma secondH2SymbolBCF_norm (v w : E) :
    ‖secondH2SymbolBCF v w‖ ≤ (2 * Real.pi)^2 * ‖v‖ * ‖w‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (secondH2Symbol_bound v w)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def secondH2 (v w : E) : L2 E →L[ℂ] L2 E := multiplier (secondH2SymbolBCF v w)

lemma secondH2_bound (v w : E) (u : L2 E) :
    ‖secondH2 v w u‖ ≤ ((2 * Real.pi)^2 * ‖v‖ * ‖w‖) * ‖u‖ :=
  (multiplier_norm_le (secondH2SymbolBCF v w) u).trans
    (mul_le_mul_of_nonneg_right (secondH2SymbolBCF_norm v w) (norm_nonneg _))

lemma secondH2_distribution (v w : E) (u : L2 E) :
    (secondH2 v w u : 𝓢'(E, ℂ)) = ∂_{v} (∂_{w} (realize 2 u)) := by
  rw [FrozenPoisson.second_deriv_multiplier]
  change (multiplier (secondH2SymbolBCF v w) u : 𝓢'(E, ℂ)) =
    fourierMultiplierCLM ℂ _ (besselPotential E ℂ (-2) (u : 𝓢'(E, ℂ)))
  rw [multiplier_distribution _ (secondH2Symbol_temperate v w), besselPotential,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr 2
  ext ξ
  change secondH2Symbol v w ξ = _
  simp only [secondH2Symbol, Pi.mul_apply]
  norm_num
  ring

variable {ι : Type*} [Fintype ι]

 
def perturbation (v : ι → E) (a : ι → ι → E →ᵇ ℂ) : L2 E →L[ℂ] L2 E :=
  ∑ i, ∑ j, multiply (a i j) ∘L secondH2 (v i) (v j)

def perturbationBound (v : ι → E) (a : ι → ι → E →ᵇ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖a i j‖ * ((2 * Real.pi)^2 * ‖v i‖ * ‖v j‖)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma perturbationBound_nonneg (v : ι → E) (a : ι → ι → E →ᵇ ℂ) :
    0 ≤ perturbationBound v a := by
  unfold perturbationBound
  positivity

lemma perturbation_bound (v : ι → E) (a : ι → ι → E →ᵇ ℂ) (u : L2 E) :
    ‖perturbation v a u‖ ≤ perturbationBound v a * ‖u‖ := by
  simp only [perturbation, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    perturbationBound, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ‖a i j‖ * ‖secondH2 (v i) (v j) u‖ := multiply_norm_le _ _
    _ ≤ ‖a i j‖ * (((2 * Real.pi)^2 * ‖v i‖ * ‖v j‖) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (secondH2_bound _ _ u) (norm_nonneg _)
    _ = _ := by ring

lemma perturbation_distribution (v : ι → E) (a : ι → ι → E →ᵇ ℂ)
    (ha : ∀ i j, (a i j : E → ℂ).HasTemperateGrowth) (u : L2 E) :
    (perturbation v a u : 𝓢'(E, ℂ)) =
      ∑ i, ∑ j, smulLeftCLM ℂ (a i j) (∂_{v i} (∂_{v j} (realize 2 u))) := by
  change Lp.toTemperedDistributionCLM ℂ volume 2 _ = _
  simp only [perturbation, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Lp.toTemperedDistributionCLM_apply, multiply_distribution _ (ha i j),
    secondH2_distribution]

end SobolevChart

namespace FrozenPoisson
open EllipticKernel SobolevChart
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma perturbation_resolvent_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ) :
    ‖perturbation v a ∘L hilbertResolvent H hH‖ ≤
      perturbationBound v a * ellipticBound H hH := by
  apply ContinuousLinearMap.opNorm_le_bound (perturbation v a ∘L hilbertResolvent H hH)
    (mul_nonneg (perturbationBound_nonneg v a) (ellipticBound_pos H hH).le)
  intro u
  calc
    _ ≤ perturbationBound v a * ‖hilbertResolvent H hH u‖ := perturbation_bound _ _ _
    _ ≤ perturbationBound v a * (ellipticBound H hH * ‖u‖) :=
      mul_le_mul_of_nonneg_left (hilbertResolvent_bound H hH u)
        (perturbationBound_nonneg v a)
    _ = _ := by ring

 
def localResolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) :
    L2 (EC n) →L[ℂ] L2 (EC n) :=
  hilbertResolvent H hH ∘L
    (↑((Units.oneSub (perturbation v a ∘L hilbertResolvent H hH)
      ((perturbation_resolvent_bound H hH v a).trans_lt hsmall))⁻¹) :
      L2 (EC n) →L[ℂ] L2 (EC n))

lemma localResolvent_equation (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    realize 2 (localResolvent H hH v a hsmall f) -
      frozenDifferential H (realize 2 (localResolvent H hH v a hsmall f)) -
      (perturbation v a (localResolvent H hH v a hsmall f) : 𝓢'(EC n, ℂ)) =
      (f : 𝓢'(EC n, ℂ)) := by
  let U := Units.oneSub (perturbation v a ∘L hilbertResolvent H hH)
      ((perturbation_resolvent_bound H hH v a).trans_lt hsmall)
  let f' := (↑U⁻¹ : L2 (EC n) →L[ℂ] L2 (EC n)) f
  have he : f' - perturbation v a (hilbertResolvent H hH f') = f := by
    change ((↑U : L2 (EC n) →L[ℂ] L2 (EC n)) * ↑U⁻¹) f = f
    rw [Units.mul_inv, one_apply_eq_self]
  have hr := (hilbert_frozen_inverse H hH 0 f').1
  norm_num at hr
  change realize 2 (hilbertResolvent H hH f') -
    frozenDifferential H (realize 2 (hilbertResolvent H hH f')) -
      (perturbation v a (hilbertResolvent H hH f') : 𝓢'(EC n, ℂ)) = _
  rw [hr]
  have hz (g : L2 (EC n)) : realize 0 g = (g : 𝓢'(EC n, ℂ)) := by simp [realize]
  rw [hz]
  simpa only [map_sub, Lp.toTemperedDistributionCLM_apply] using
    congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) he

lemma fixed_for_perturbed (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ) (u f : L2 (EC n))
    (hu : realize 2 u - frozenDifferential H (realize 2 u) -
      (perturbation v a u : 𝓢'(EC n, ℂ)) = (f : 𝓢'(EC n, ℂ))) :
    u = hilbertResolvent H hH (f + perturbation v a u) := by
  apply realize_injective 2
  have hs : 2 = (0 : ℝ) + 2 := by norm_num
  rw [hs, hilbertResolvent_realize H hH 0]
  have he : shifted H (realize 2 u) =
      realize 0 (f + perturbation v a u) := by
    rw [shifted_eq_identity_sub H hH]
    simpa [realize, map_add, sub_eq_iff_eq_add] using sub_eq_iff_eq_add.mp hu
  rw [← he, resolvent_shifted H hH]
  norm_num

lemma perturbed_unique (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1)
    (u w f : L2 (EC n))
    (hu : realize 2 u - frozenDifferential H (realize 2 u) -
      (perturbation v a u : 𝓢'(EC n, ℂ)) = (f : 𝓢'(EC n, ℂ)))
    (hw : realize 2 w - frozenDifferential H (realize 2 w) -
      (perturbation v a w : 𝓢'(EC n, ℂ)) = (f : 𝓢'(EC n, ℂ))) : u = w := by
  have huf := fixed_for_perturbed H hH v a u f hu
  have hwf := fixed_for_perturbed H hH v a w f hw
  have he : u - w = hilbertResolvent H hH (perturbation v a (u - w)) := by
    rw [map_sub, map_sub]
    rw [map_add] at huf hwf
    calc
      u - w = (hilbertResolvent H hH f + hilbertResolvent H hH (perturbation v a u)) -
          (hilbertResolvent H hH f + hilbertResolvent H hH (perturbation v a w)) :=
        congrArg₂ (· - ·) huf hwf
      _ = _ := by abel
  have hn : ‖u - w‖ ≤ ellipticBound H hH * perturbationBound v a * ‖u - w‖ := by
    calc
      _ = ‖hilbertResolvent H hH (perturbation v a (u - w))‖ := congrArg norm he
      _ ≤ _ := (hilbertResolvent_bound H hH _).trans
        (by nlinarith [perturbation_bound v a (u - w), ellipticBound_pos H hH])
  have : ‖u - w‖ = 0 := by nlinarith [norm_nonneg (u - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma localResolvent_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    ‖localResolvent H hH v a hsmall f‖ ≤
      (ellipticBound H hH / (1 - perturbationBound v a * ellipticBound H hH)) * ‖f‖ := by
  let u := localResolvent H hH v a hsmall f
  have he := fixed_for_perturbed H hH v a u f (localResolvent_equation H hH v a hsmall f)
  have hn : ‖u‖ ≤ ellipticBound H hH *
      (‖f‖ + perturbationBound v a * ‖u‖) := by
    calc
      ‖u‖ = ‖hilbertResolvent H hH (f + perturbation v a u)‖ := congrArg norm he
      _ ≤ ellipticBound H hH * ‖f + perturbation v a u‖ := hilbertResolvent_bound H hH _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add le_rfl (perturbation_bound v a u)))
          (ellipticBound_pos H hH).le
  have hp : 0 < 1 - perturbationBound v a * ellipticBound H hH := sub_pos.mpr hsmall
  change ‖u‖ ≤ _
  rw [div_mul_eq_mul_div, le_div_iff₀ hp]
  nlinarith

 

theorem variable_sobolev_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (ha : ∀ i j, (a i j : EC n → ℂ).HasTemperateGrowth)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    ∃! u : L2 (EC n),
      realize 2 u - frozenDifferential H (realize 2 u) -
        ∑ i, ∑ j, smulLeftCLM ℂ (a i j) (∂_{v i} (∂_{v j} (realize 2 u))) =
          (f : 𝓢'(EC n, ℂ)) := by
  refine ⟨localResolvent H hH v a hsmall f, ?_, ?_⟩
  · dsimp only
    rw [← perturbation_distribution v a ha]
    exact localResolvent_equation H hH v a hsmall f
  · intro u hu
    rw [← perturbation_distribution v a ha] at hu
    exact perturbed_unique H hH v a hsmall u _ f hu
      (localResolvent_equation H hH v a hsmall f)

end FrozenPoisson

end
end

end OAI
