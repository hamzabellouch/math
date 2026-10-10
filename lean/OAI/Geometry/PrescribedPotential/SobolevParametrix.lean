import Mathlib
import OAI.Geometry.PrescribedPotential.FrozenPoisson

namespace OAI

/-! Sobolev Parametrix. -/

section

 

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Real

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev L2 (E : Type*) [MeasureSpace E] := Lp ℂ 2 (volume : Measure E)

 

def realize (s : ℝ) : L2 E →L[ℂ] 𝓢'(E, ℂ) :=
  besselPotential E ℂ (-s) ∘L Lp.toTemperedDistributionCLM ℂ volume 2

lemma bessel_realize (s : ℝ) (u : L2 E) :
    besselPotential E ℂ s (realize s u) = (u : 𝓢'(E, ℂ)) := by
  simp [realize]

lemma realize_memSobolev (s : ℝ) (u : L2 E) : MemSobolev s 2 (realize s u) :=
  ⟨u, bessel_realize s u⟩

lemma l2_injective : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2) :=
  LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot

lemma realize_injective (s : ℝ) : Function.Injective (realize (E := E) s) := by
  intro u v h
  apply l2_injective
  rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply]
  simpa only [bessel_realize] using congrArg (besselPotential E ℂ s) h

lemma memSobolev_iff_realize (s : ℝ) (u : 𝓢'(E, ℂ)) :
    MemSobolev s 2 u ↔ ∃ v : L2 E, realize s v = u := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change besselPotential E ℂ (-s) (v : 𝓢'(E, ℂ)) = u
    exact (besselPotential_neg_apply_eq_iff s _ u).mpr hv
  · rintro ⟨v, rfl⟩
    exact realize_memSobolev s v

 
def multiply (g : E →ᵇ ℂ) : L2 E →L[ℂ] L2 E :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 (g.memLp_top.toLp g)

lemma multiply_eq (g : E →ᵇ ℂ) (u : L2 E) :
    multiply g u = (g.memLp_top.toLp g : Lp ℂ ⊤ volume) • u := by
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := 2) (g.memLp_top.toLp g : Lp ℂ ⊤ volume) u,
    Lp.coeFn_lpSMul (r := 2) (g.memLp_top.toLp g : Lp ℂ ⊤ volume) u] with x h₁ h₂
  exact h₁.trans (by simpa [Pi.smul_apply, smul_eq_mul] using h₂.symm)

lemma multiply_norm_le (g : E →ᵇ ℂ) (u : L2 E) :
    ‖multiply g u‖ ≤ ‖g‖ * ‖u‖ := by
  rw [multiply_eq]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_lpSMul (r := 2)
    (g.memLp_top.toLp g : Lp ℂ ⊤ volume) u,
    (g.memLp_top (μ := volume)).coeFn_toLp] with x h₁ h₂
  rw [h₁, Pi.smul_apply', h₂, norm_smul]
  exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)

lemma multiply_distribution (g : E →ᵇ ℂ) (hg : (g : E → ℂ).HasTemperateGrowth)
    (u : L2 E) :
    (multiply g u : 𝓢'(E, ℂ)) = smulLeftCLM ℂ g (u : 𝓢'(E, ℂ)) := by
  rw [multiply_eq]
  exact Lp.toTemperedDistribution_smul_eq hg g.memLp_top u

 
def multiplier (g : E →ᵇ ℂ) : L2 E →L[ℂ] L2 E :=
  fourierInvCLM ℂ (L2 E) ∘L multiply g ∘L fourierCLM ℂ (L2 E)

lemma multiplier_norm_le (g : E →ᵇ ℂ) (u : L2 E) :
    ‖multiplier g u‖ ≤ ‖g‖ * ‖u‖ := by
  change ‖(Lp.fourierTransformₗᵢ E ℂ).symm (multiply g (𝓕 u))‖ ≤ _
  rw [(Lp.fourierTransformₗᵢ E ℂ).symm.norm_map]
  simpa only [Lp.norm_fourier_eq] using multiply_norm_le g (𝓕 u)

lemma multiplier_distribution (g : E →ᵇ ℂ) (hg : (g : E → ℂ).HasTemperateGrowth)
    (u : L2 E) :
    (multiplier g u : 𝓢'(E, ℂ)) = fourierMultiplierCLM ℂ g (u : 𝓢'(E, ℂ)) := by
  change ((𝓕⁻ (multiply g (𝓕 u)) : L2 E) : 𝓢'(E, ℂ)) = _
  rw [← Lp.fourierInv_toTemperedDistribution_eq, multiply_distribution g hg,
    ← Lp.fourier_toTemperedDistribution_eq]
  rfl

lemma bessel_multiplier_comm {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (s : ℝ) (u : 𝓢'(E, ℂ)) :
    besselPotential E ℂ s (fourierMultiplierCLM ℂ g u) =
      fourierMultiplierCLM ℂ g (besselPotential E ℂ s u) := by
  rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply hg (by fun_prop),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) hg, mul_comm]

lemma realize_multiplier (s : ℝ) (g : E →ᵇ ℂ)
    (hg : (g : E → ℂ).HasTemperateGrowth) (u : L2 E) :
    realize s (multiplier g u) = fourierMultiplierCLM ℂ g (realize s u) := by
  change besselPotential E ℂ (-s) (multiplier g u : 𝓢'(E, ℂ)) = _
  rw [multiplier_distribution g hg, bessel_multiplier_comm hg]
  rfl

end SobolevChart

namespace FrozenPoisson
open EllipticKernel SobolevChart
variable {n : ℕ}

def gainSymbol (H : Matrix (Fin n) (Fin n) ℂ) (ξ : EC n) : ℂ :=
  (1 + ‖ξ‖^2 : ℝ) * inverseSymbol H ξ

lemma gainSymbol_temperate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    (gainSymbol H).HasTemperateGrowth := by
  have hi := inverseSymbol_temperate H hH
  unfold gainSymbol
  fun_prop

 
def ellipticBound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) : ℝ :=
  max 1 (inverseSymbol_weighted_bounded H hH).choose

lemma ellipticBound_pos (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    0 < ellipticBound H hH := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

lemma gainSymbol_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (ξ : EC n) :
    ‖gainSymbol H ξ‖ ≤ ellipticBound H hH :=
  ((inverseSymbol_weighted_bounded H hH).choose_spec ξ).trans (le_max_right _ _)

def gainSymbolBCF (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) : EC n →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gainSymbol H)
    (gainSymbol_temperate H hH).1.continuous (ellipticBound H hH) (gainSymbol_bound H hH)

lemma gainSymbolBCF_norm (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    ‖gainSymbolBCF H hH‖ ≤ ellipticBound H hH :=
  (BoundedContinuousFunction.norm_le (ellipticBound_pos H hH).le).mpr (gainSymbol_bound H hH)

 
def hilbertResolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    L2 (EC n) →L[ℂ] L2 (EC n) := multiplier (gainSymbolBCF H hH)

lemma hilbertResolvent_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (u : L2 (EC n)) :
    ‖hilbertResolvent H hH u‖ ≤ ellipticBound H hH * ‖u‖ :=
  (multiplier_norm_le (gainSymbolBCF H hH) u).trans
    (mul_le_mul_of_nonneg_right (gainSymbolBCF_norm H hH) (norm_nonneg u))

lemma bessel_two_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (u : 𝓢'(EC n, ℂ)) :
    besselPotential (EC n) ℂ 2 (resolvent H u) =
      fourierMultiplierCLM ℂ (gainSymbol H) u := by
  rw [besselPotential, resolvent,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (inverseSymbol_temperate H hH)
      (by fun_prop)]
  congr 2
  ext ξ
  simp [gainSymbol, mul_comm]

lemma hilbertResolvent_realize (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (s : ℝ) (u : L2 (EC n)) :
    realize (s + 2) (hilbertResolvent H hH u) = resolvent H (realize s u) := by
  change besselPotential (EC n) ℂ (-(s + 2))
    (Lp.toTemperedDistributionCLM ℂ MeasureTheory.volume 2 (hilbertResolvent H hH u)) = _
  rw [besselPotential_neg_apply_eq_iff]
  have hc : resolvent H (realize s u) = besselPotential (EC n) ℂ (-s)
      (resolvent H (Lp.toTemperedDistributionCLM ℂ MeasureTheory.volume 2 u)) :=
    (bessel_multiplier_comm (inverseSymbol_temperate H hH) (-s) _).symm
  rw [hc, besselPotential_besselPotential_apply]
  have hs : -s + (s + 2) = 2 := by ring
  rw [hs, bessel_two_resolvent H hH]
  exact (multiplier_distribution (gainSymbolBCF H hH) (gainSymbol_temperate H hH) u).symm

 

theorem hilbert_frozen_inverse (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (s : ℝ) (f : L2 (EC n)) :
    let u := hilbertResolvent H hH f
    realize (s + 2) u - frozenDifferential H (realize (s + 2) u) = realize s f ∧
      ‖u‖ ≤ ellipticBound H hH * ‖f‖ := by
  refine ⟨?_, hilbertResolvent_bound H hH f⟩
  rw [← shifted_eq_identity_sub H hH, hilbertResolvent_realize,
    shifted_resolvent H hH]

end FrozenPoisson

end
end

end OAI
