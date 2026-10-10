import OAI.Analysis.KadisonSimilarity.Representation.SpectralCutBounds
import OAI.Analysis.KadisonSimilarity.Tracial.GNSProjectionContinuity
import OAI.Analysis.KadisonSimilarity.Representation.StrongApplyLimits

namespace OAI

/-! Vanishing normal trace norm forces any convergent fixed-vector orbit
to have zero limit, by cutting off its high left spectrum. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance normalTruncation_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

theorem norm_limit_le_of_spectral_truncation
    (M : VonNeumannAlgebra H) (a : ℕ → M.toStarSubalgebra)
    (ξ y : H) (hv : Tendsto (fun n => (a n : H →L[ℂ] H) ξ) atTop (𝓝 y))
    (ε : ℝ) (hε : 0 < ε)
    (hz : ∀ z : H, Tendsto
      (fun n => (leftSpectralCut M (a n) ε : H →L[ℂ] H) z) atTop (𝓝 0)) :
    ‖y‖ ≤ ε * ‖ξ‖ := by
  let p (n : ℕ) := leftSpectralCut M (a n) ε
  let T (n : ℕ) : H →L[ℂ] H := p n
  have hp (n : ℕ) : IsStarProjection (p n) := leftSpectralCut_isStarProjection M (a n) ε
  have hT (n : ℕ) : ‖T n‖ ≤ 1 := (hp n).norm_le
  have hc := contractive_complement_apply T hT hz
    (fun n => (a n : H →L[ℂ] H) ξ) y hv
  apply le_of_tendsto hc.norm
  filter_upwards [] with n
  calc
    ‖(1 - T n) ((a n : H →L[ℂ] H) ξ)‖ =
        ‖(((1 - p n) * a n : M.toStarSubalgebra) : H →L[ℂ] H) ξ‖ := rfl
    _ ≤ ‖(1 - p n) * a n‖ * ‖ξ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right
      (norm_complement_leftSpectralCut_mul_le M (a n) ε hε.le) (norm_nonneg _)

theorem limit_eq_zero_of_spectral_truncation
    (M : VonNeumannAlgebra H) (a : ℕ → M.toStarSubalgebra)
    (ξ y : H) (hv : Tendsto (fun n => (a n : H →L[ℂ] H) ξ) atTop (𝓝 y))
    (hz : ∀ ε : ℝ, 0 < ε → ∀ z : H, Tendsto
      (fun n => (leftSpectralCut M (a n) ε : H →L[ℂ] H) z) atTop (𝓝 0)) :
    y = 0 := by
  have hbound (ε : ℝ) (hε : 0 < ε) : ‖y‖ ≤ ε * ‖ξ‖ :=
    norm_limit_le_of_spectral_truncation M a ξ y hv ε hε (hz ε hε)
  have hsmall : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖ξ‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖ξ‖
  exact norm_eq_zero.mp (le_antisymm
    (ge_of_tendsto hsmall (Eventually.of_forall fun n =>
      hbound ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n))) (norm_nonneg _))

theorem normal_gns_orbit_limit_eq_zero
    (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hf : ∀ a, τ (star a * a) = 0 → a = 0) (hN : HasNormalGNS τ)
    (a : ℕ → M.toStarSubalgebra)
    (ha : Tendsto (fun n => gnsTracialVector τ (a n)) atTop (𝓝 0))
    (ξ y : H) (hv : Tendsto (fun n => (a n : H →L[ℂ] H) ξ) atTop (𝓝 y)) :
    y = 0 := by
  apply limit_eq_zero_of_spectral_truncation M a ξ y hv
  intro ε hε z
  exact projection_tendsto_zero_of_normal_gns M τ h1 htr hf hN
    (fun n => leftSpectralCut M (a n) ε)
    (fun n => leftSpectralCut_isStarProjection M (a n) ε)
    (leftSpectralCut_trace_tendsto_zero M τ htr a ha ε hε) z

/-- Equal trace inner products identify the orbit norms in any tracial
geometry with the native GNS orbit norms. -/
theorem tracialGeometry_gns_norm_eq
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (G : TracialCornerGeometry A E)
    (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (a : A) : ‖gnsTracialVector τ a‖ = ‖G.vector a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    gnsTracialVector_inner, G.inner_vector, hτ]

theorem normal_geometry_orbit_limit_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra)
    (a : ℕ → M.toStarSubalgebra) (ha : Tendsto (fun n => G.vector (a n)) atTop (𝓝 0))
    (ξ y : H) (hv : Tendsto (fun n => (a n : H →L[ℂ] H) ξ) atTop (𝓝 y)) :
    y = 0 := by
  have hg : Tendsto (fun n => gnsTracialVector τ (a n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [tracialGeometry_gns_norm_eq G τ hτ, norm_zero] using ha.norm
  have htr (a b : M.toStarSubalgebra) : τ (a * b) = τ (b * a) := by
    rw [hτ, hτ, G.tracial]
  apply limit_eq_zero_of_spectral_truncation M a ξ y hv
  intro ε hε z
  exact projection_tendsto_zero_of_normal_geometry M G τ hτ h1 hf N hN
    (fun n => leftSpectralCut M (a n) ε)
    (fun n => leftSpectralCut_isStarProjection M (a n) ε)
    (leftSpectralCut_trace_tendsto_zero M τ htr a hg ε hε) z

end KadisonSimilarity

end

end OAI
