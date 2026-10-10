import OAI.Geometry.RCD.Heat.LogarithmicEnergyIdentity

namespace OAI

/-! # Half-sums of the actual scaled logarithmic representatives -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem local_half_pair_gradient {Ω : Set X} (P V : SobolevSpace μ Q)
    {H : ℝ} (hH : 0≤H)
    (hP : ∀ᵐ x ∂μ.restrict Ω, (SobolevSpace.minimalSlope μ Q P x)^2≤H)
    (hV : ∀ᵐ x ∂μ.restrict Ω, (SobolevSpace.minimalSlope μ Q V x)^2≤H) :
    (∀ᵐ x ∂μ.restrict Ω,
      SobolevSpace.minimalSlope μ Q ((1/2:ℝ) • (P+V)) x≤Real.sqrt H) ∧
    (∀ᵐ x ∂μ.restrict Ω,
      SobolevSpace.minimalSlope μ Q ((1/2:ℝ) • (V-P)) x≤Real.sqrt H) := by
  have hs (w : SobolevSpace μ Q) :
      SobolevSpace.minimalSlope μ Q ((1/2:ℝ) • w) =ᵐ[μ]
        fun x => (1/2:ℝ)*SobolevSpace.minimalSlope μ Q w x := by
    rw [SobolevSpace.minimalSlope_smul_nonneg μ Q w (by norm_num : (0:ℝ)≤1/2)]
    exact Lp.coeFn_smul _ _
  have hh : ∀ᵐ x ∂μ.restrict Ω,
      SobolevSpace.minimalSlope μ Q ((1/2:ℝ) • (P+V)) x≤Real.sqrt H ∧
      SobolevSpace.minimalSlope μ Q ((1/2:ℝ) • (V-P)) x≤Real.sqrt H := by
    filter_upwards [hP,hV,ae_restrict_of_ae (hs (P+V)),ae_restrict_of_ae (hs (V-P)),
      ae_restrict_of_ae ((Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_add_le μ Q P V)),
      ae_restrict_of_ae ((Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_sub_le μ Q V P)),
      ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.minimalSlope μ Q P) (SobolevSpace.minimalSlope μ Q V)),
      ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.minimalSlope μ Q V) (SobolevSpace.minimalSlope μ Q P))]
      with x hp hv hsp hsm hap ham hcoe hcoe'
    rw [hcoe] at hap
    rw [hcoe'] at ham
    simp only [Pi.add_apply] at hap ham
    have hps : SobolevSpace.minimalSlope μ Q P x≤Real.sqrt H := by
      nlinarith [Real.sq_sqrt hH,Real.sqrt_nonneg H]
    have hvs : SobolevSpace.minimalSlope μ Q V x≤Real.sqrt H := by
      nlinarith [Real.sq_sqrt hH,Real.sqrt_nonneg H]
    rw [hsp,hsm]
    constructor <;> linarith
  exact ⟨hh.mono fun _ hx => hx.1,hh.mono fun _ hx => hx.2⟩

theorem scaled_log_pair_bounds {Ω : Set X} (F G : X → ℝ)
    (P V : SobolevSpace μ Q) {c H : ℝ} (hc : 0<c) (hH : 0≤H)
    (hP : SobolevSpace.toLp μ Q P =ᵐ[μ.restrict Ω] fun x => (2*c)*Real.log (F x))
    (hV : SobolevSpace.toLp μ Q V =ᵐ[μ.restrict Ω] fun x => (2*c)*Real.log (G x))
    (hPg : ∀ᵐ x ∂μ.restrict Ω, (SobolevSpace.minimalSlope μ Q P x)^2≤H)
    (hVg : ∀ᵐ x ∂μ.restrict Ω, (SobolevSpace.minimalSlope μ Q V x)^2≤H) :
    ∃ U W : SobolevSpace μ Q,
      (SobolevSpace.toLp μ Q U =ᵐ[μ.restrict Ω] fun x => Real.log (F x)) ∧
      (SobolevSpace.toLp μ Q W =ᵐ[μ.restrict Ω] fun x => Real.log (G x)) ∧
      (∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q (c • (W-U)) x≤Real.sqrt H) ∧
      (∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q (c • (U+W)) x≤Real.sqrt H) := by
  let U := (2*c)⁻¹ • P
  let W := (2*c)⁻¹ • V
  have hscale : c*(2*c)⁻¹=(1/2:ℝ) := by field_simp
  have he₁ : c • (W-U)=(1/2:ℝ) • (V-P) := by
    dsimp only [U,W]
    rw [← smul_sub,smul_smul,hscale]
  have he₂ : c • (U+W)=(1/2:ℝ) • (P+V) := by
    dsimp only [U,W]
    rw [← smul_add,smul_smul,hscale]
  have hrep (u : SobolevSpace μ Q) (f : X → ℝ)
      (hu : SobolevSpace.toLp μ Q u =ᵐ[μ.restrict Ω] fun x => (2*c)*Real.log (f x)) :
      SobolevSpace.toLp μ Q ((2*c)⁻¹ • u) =ᵐ[μ.restrict Ω] fun x => Real.log (f x) := by
    filter_upwards [hu,ae_restrict_of_ae (Lp.coeFn_smul (2*c)⁻¹ (SobolevSpace.toLp μ Q u))]
      with x hx hs
    change SobolevSpace.toLp μ Q ((2*c)⁻¹ • u) x=(2*c)⁻¹*SobolevSpace.toLp μ Q u x at hs
    rw [hs,hx]
    field_simp
  have hh := local_half_pair_gradient μ Q P V hH hPg hVg
  exact ⟨U,W,hrep P F hP,hrep V G hV,he₁ ▸ hh.2,he₂ ▸ hh.1⟩

end RegularPointCoordinates

end

end OAI
