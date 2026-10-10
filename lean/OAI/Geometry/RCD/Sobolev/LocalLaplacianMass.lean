import OAI.Geometry.RCD.Sobolev.WeakLaplacianLowerMass

namespace OAI

/-! # Absolute local Laplacian mass from local gradient bounds -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem local_laplacian_mass (u χ : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (v : X → ℝ)
    (hv : SobolevSpace.toLp μ Q χ =ᵐ[μ] v) (hvi : Integrable v μ) (hv0 : ∀ x, 0≤v x)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (hfinite : μ Ω≠∞)
    (hvzero : ∀ x∉Ω, v x=0) (L M : ℝ≥0)
    (huL : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q u x≤L)
    (hχM : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q χ x≤M)
    {C : ℝ} (hC : 0≤C) (hlower : ∀ᵐ x ∂μ.restrict Ω, -C≤d x) :
    Integrable (fun x => v x*|d x|) μ ∧
      (∫ x, v x*|d x| ∂μ)≤(L:ℝ)*M*μ.real Ω+2*C*(∫ x, v x ∂μ) := by
  have hΓ : ∀ᵐ x ∂μ.restrict Ω, |localGamma μ Q u χ x|≤(L:ℝ)*M := by
    filter_upwards [huL,ae_restrict_of_ae hχM,ae_restrict_of_ae (localGamma_abs_le μ Q u χ),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q χ))]
      with x hu hχ hg hn
    change 0≤SobolevSpace.minimalSlope μ Q χ x at hn
    exact hg.trans (mul_le_mul hu hχ hn L.coe_nonneg)
  have hz : ∀ᵐ x ∂μ, x∉Ω → localGamma μ Q u χ x=0 := by
    filter_upwards [hv,localGamma_comm μ Q u χ,localGamma_zero_on_level μ Q χ u 0]
      with x hx hc h0 hout
    exact hc.trans (h0 (hx.trans (hvzero x hout)))
  have he : |energyForm μ Q u χ|≤(L:ℝ)*M*μ.real Ω := by
    rw [← integral_localGamma_eq_energyForm,
      ← setIntegral_eq_integral_of_ae_compl_eq_zero hz]
    calc
      _ ≤ ∫ x in Ω, |localGamma μ Q u χ x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ in Ω, (L:ℝ)*M ∂μ := integral_mono_ae
        (localGamma_memL1 μ Q u χ).integrableOn.abs (integrableOn_const hfinite) hΓ
      _ = _ := by simp only [setIntegral_const,smul_eq_mul]; ring
  have hl : ∀ᵐ x ∂μ, v x≠0 → -C≤d x := by
    filter_upwards [(ae_restrict_iff' hΩ).mp hlower] with x hx hne
    apply hx
    by_contra hout
    exact hne (hvzero x hout)
  obtain ⟨hi,hm⟩ := weakLaplacian_lower_weighted_mass μ Q u χ d hd v hv hvi hv0 hC hl
  exact ⟨hi,hm.trans (add_le_add he le_rfl)⟩

end RegularPointCoordinates

end

end OAI
