import OAI.MathematicalPhysics.Boltzmann.Branching.CommonBoundedAverageCompactness
import OAI.MathematicalPhysics.Boltzmann.Branching.FirstEntryMass
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedPairUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityAverageDifference
import OAI.MathematicalPhysics.Boltzmann.Compactness.L1TruncationCauchy
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalL1ApproximationLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrableGainTail

namespace OAI

section

/-! # Uniform three-collision access weight for integration over collision times -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem three_collision_access_lower {κ ρ ε c R b₀ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε0 : 0 < ε) (hε : ε ≤ 1/12) (hερ : 6*ε ≤ ρ)
    (hc : 0 < c) (hb₀ : c ≤ b₀) (hR : 0 ≤ R)
    {e v w₀ : V} (he : ‖e‖ = 1) (hv : ‖v‖ ≤ R) (hw₀ : ‖w₀‖ ≤ 2)
    (hve : 3/4 ≤ ‖v-w₀‖) (hnear : dist w₀ e ≤ ε/2)
    (w₁ w₂ : V → Sphere × Sphere → V) (b₁ b₂ : V → Sphere × Sphere → ℝ)
    (hpartners : ∀ u ∈ ball e ε, ∀ a ∈ accessAngles κ (ρ/2),
      ‖w₁ u a-(-e)‖ ≤ ε ∧ ‖w₂ u a-beamAxis‖ ≤ ε)
    (hdensity : ∀ u ∈ ball e ε, ∀ a ∈ accessAngles κ (ρ/2),
      c ≤ b₁ u a ∧ c ≤ b₂ u a)
    :
    firstEntryMass R ε c *
      ((ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
        (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))) ≤
      ENNReal.ofReal (4*Real.pi*b₀*‖v-w₀‖)*
      ∫⁻ u, (∫⁻ a, accessWeight u (w₁ u) (w₂ u) (b₁ u) (b₂ u) κ ρ a
        ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w₀) := by
  let k := (ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
    (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))
  have hbound : k*outgoing (v,w₀) (ball e ε) ≤
      ∫⁻ u, (∫⁻ a, accessWeight u (w₁ u) (w₂ u) (b₁ u) (b₂ u) κ ρ a
        ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w₀) := by
    calc
      _ = ∫⁻ _u in ball e ε, k ∂outgoing (v,w₀) := by
        rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
      _ ≤ ∫⁻ u in ball e ε, (∫⁻ a, accessWeight u (w₁ u) (w₂ u) (b₁ u) (b₂ u) κ ρ a
          ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w₀) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
        apply accessWeight_lower hκ0 hκ hρ hε hερ hc he
          (show ‖u-e‖ ≤ ε from le_of_lt hu)
        · exact hpartners u hu
        · exact hdensity u hu
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have hfirst := firstEntryMass_lower hR hε0 hc hb₀ hw₀ hv hve hnear
  calc
    firstEntryMass R ε c*k ≤
        (ENNReal.ofReal (4*Real.pi*b₀*‖v-w₀‖)*outgoing (v,w₀) (ball e ε))*k := by
      exact mul_le_mul' hfirst le_rfl
    _ = ENNReal.ofReal (4*Real.pi*b₀*‖v-w₀‖)*(k*outgoing (v,w₀) (ball e ε)) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hbound

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniformly integrable sources have locally compact velocity averages -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

theorem uniform_average_compactness (r : ℕ → Velocity × FourierSpace → ℂ)
    (hm : ∀ n, Measurable (r n)) (hui : UniformIntegrable r 1 volume)
    (R : ℝ) (hs : ∀ n p, R < ‖p.1‖ → r n p = 0) :
    ∃ (φ : ℕ → ℕ) (g : Lp ℂ 1 (volume : Measure FourierSpace)), StrictMono φ ∧
      ∀ K : Set FourierSpace, volume K < ⊤ →
        Tendsto (fun n => eLpNorm (velocityLineAverage (r (φ n))-(g : FourierSpace → ℂ))
          1 (volume.restrict K)) atTop (𝓝 0) := by
  classical
  have hi n : Integrable (r n) := memLp_one_iff_integrable.mp (hui.memLp n)
  obtain ⟨C,hC⟩ := hui.2
  have hmass n : (∫ p, ‖r n p‖) ≤ (C : ℝ) := by
    have h := hC n
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n)] at h
    exact (ENNReal.ofReal_le_ofReal_iff C.coe_nonneg).mp (by simpa only [ENNReal.ofReal_coe_nnreal] using h)
  have ht m := uniform_value_truncation r hm hui
    (ENNReal.ofReal_pos.mpr (truncationError_pos m))
  choose B u hum hub hus hud hue using ht
  have hui' m n : Integrable (u m n) :=
    (hi n).norm.mono' (hum m n).aestronglyMeasurable (ae_of_all _ (hud m n))
  have hus' m n p (hp : R < ‖p.1‖) : u m n p = 0 := hus m n p (hs n p hp)
  have humass m n : (∫ p, ‖u m n p‖) ≤ (C : ℝ) :=
    (integral_mono (hui' m n).norm (hi n).norm (hud m n)).trans (hmass n)
  obtain ⟨φ,g,hφ,hg⟩ := common_bounded_average_compactness u hum hui' R
    (fun m => B m) (fun _ => C) (fun m => (B m).coe_nonneg) (fun _ => C.coe_nonneg)
    hub hus' humass
  have hlocal m (K : Set FourierSpace) (hK : volume K < ⊤) :
      Tendsto (fun n => eLpNorm (velocityLineAverage (u m (φ n))-(g m : FourierSpace → ℂ))
        1 (volume.restrict K)) atTop (𝓝 0) := by
    have h := localL2_L1_tendsto K hK (hg m K hK)
    have he n : eLpNorm (boundedAverageL2 (u m (φ n)) (hui' m (φ n))
        (hub m (φ n)) (hus' m (φ n))-g m : Lp ℂ 2 volume) 1 (volume.restrict K) =
        eLpNorm (velocityLineAverage (u m (φ n))-(g m : FourierSpace → ℂ)) 1 (volume.restrict K) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub
        (boundedAverageL2 (u m (φ n)) (hui' m (φ n)) (hub m (φ n)) (hus' m (φ n))) (g m)),
        ae_restrict_of_ae (MemLp.coeFn_toLp (velocityLineAverage_memLp_two
          (hui' m (φ n)) (hub m (φ n)) (hus' m (φ n))))] with x hx ha
      simp only [Pi.sub_apply] at hx ⊢
      rw [hx]
      change (boundedAverageL2 (u m (φ n)) (hui' m (φ n)) (hub m (φ n)) (hus' m (φ n))) x = velocityLineAverage (u m (φ n)) x at ha
      rw [ha]
    simpa only [he] using h
  have hbound m n : eLpNorm (velocityLineAverage (u m n)) 1 volume ≤ (C : ℝ≥0∞) := by
    apply (velocityLineAverage_eLpNorm_le (hui' m n)).trans
    exact (eLpNorm_mono (hui' m n).aestronglyMeasurable (hud m n)).trans (hC n)
  have hgi m : Integrable (g m : FourierSpace → ℂ) := by
    have h := localL1_global_bound (Lp.aestronglyMeasurable (g m)) (C : ℝ≥0∞)
      (fun n => hbound m (φ n)) (hlocal m)
    refine ⟨Lp.aestronglyMeasurable (g m),?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    rw [← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable (g m))]
    exact h.trans_lt ENNReal.coe_lt_top
  have herr m n : eLpNorm (velocityLineAverage (r (φ n))-velocityLineAverage (u m (φ n)))
      1 volume ≤ ENNReal.ofReal (truncationError m) :=
    (velocityLineAverage_difference_le (hi (φ n)) (hui' m (φ n))).trans (hue m (φ n))
  obtain ⟨q,hq⟩ := localL1_approximation_limit (fun n => velocityLineAverage (r (φ n)))
    (fun m n => velocityLineAverage (u m (φ n))) (fun m => (g m : FourierSpace → ℂ))
    hgi truncationError (fun m => (truncationError_pos m).le) truncationError_tendsto herr hlocal
  exact ⟨φ,q,hφ,hq⟩

end BoltzmannNonuniqueness.Published

end

end

end OAI
