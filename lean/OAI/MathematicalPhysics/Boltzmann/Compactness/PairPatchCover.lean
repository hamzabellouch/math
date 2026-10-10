import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedL1Tests
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedPairRate
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocitySmoothingError
import OAI.MathematicalPhysics.Boltzmann.Compactness.L1VelocityTranslationApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairBoundedTruncation
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

/-! # Gain translation control from bounded compact moment approximations -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem pairGain_translation_of_moment_approximation
    {g : ℕ → X × (Velocity × Velocity) → ℝ}
    (hgm : ∀ n, Measurable (g n))
    (hmi : ∀ n, Integrable (momentPair (g n)) (μ.prod (volume : Measure (Velocity × Velocity))))
    (happrox : ∀ δ : ℝ, 0 < δ →
      ∃ (R : ℝ) (_hR : 0 < R) (B : ℝ≥0) (u : ℕ → X × (Velocity × Velocity) → ℝ),
        (∀ n, Measurable (u n)) ∧ (∀ n z, |u n z| ≤ B) ∧
        (∀ n z, z.2 ∉ incomingBall R → u n z = 0) ∧
        (∀ n, eLpNorm (momentPair (fun z => g n z-u n z)) 1
          (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ENNReal.ofReal δ))
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,
      |pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p| ∂μ.prod volume) atTop (𝓝 0) := by
  have hri n := pairPreRate_integrable_of_moment (hgm n) (hmi n)
  apply velocityTranslation_of_uniform_L1_approximation (fun n => pairGain_integrable (hri n))
  intro ε hε
  let D := sphereArea.real univ
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  let δ := ε/(D+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨R,hR,B,u,hum,huB,hus,herr⟩ := happrox δ hδ
  have hui n := bounded_pairPreRate_integrable (μ := μ) R (hum n) (huB n) (hus n)
  refine ⟨fun n => pairGain (u n),fun n => pairGain_integrable (hui n),?_,
    bounded_pairGain_translation_no_rate_assumption R ha hum huB hus⟩
  intro n
  have he : (fun z => pairPreRate (g n) z-pairPreRate (u n) z) =
      pairPreRate (fun z => g n z-u n z) := by
    funext z
    exact (mul_sub _ _ _).symm
  have hn : eLpNorm (fun p => pairGain (g n) p-pairGain (u n) p) 1 (μ.prod volume) ≤
      sphereArea univ*eLpNorm (momentPair (fun z => g n z-u n z)) 1
        (μ.prod (volume : Measure (Velocity × Velocity))) := by
    apply (pairGain_difference_eLpNorm_le (hgm n) (hum n) (hri n) (hui n)).trans
    rw [he]
    exact pairPreRate_moment_norm_le ((hgm n).sub (hum n))
  have hDreal : ENNReal.ofReal D = sphereArea univ :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have heps : D*δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < D+1)).mpr
    nlinarith
  have heL : eLpNorm (fun p => pairGain (g n) p-pairGain (u n) p) 1 (μ.prod volume) ≤
      ENNReal.ofReal ε := by
    apply hn.trans
    calc
      _ ≤ sphereArea univ*ENNReal.ofReal δ := mul_le_mul' le_rfl (herr n)
      _ = ENNReal.ofReal (D*δ) := by rw [← hDreal,ENNReal.ofReal_mul hD]
      _ ≤ _ := ENNReal.ofReal_le_ofReal heps
  exact Published.integral_abs_le_of_eLpNorm_le
    ((pairGain_integrable (hri n)).sub (pairGain_integrable (hui n))) hε.le heL


end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Reassembling pair identities from a countable nonzero patch cover -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
theorem pair_ae_of_patch_cover {W U : X × Y → ℝ} (hW : Measurable W) (hU : Measurable U)
    {χ : ℕ → X → ℝ} (hχ : ∀ j, Measurable (χ j))
    (hcover : ∀ᵐ x ∂μ, ∃ j, χ j x ≠ 0)
    (hpatch : ∀ j k : ℕ, W =ᵐ[(μ.restrict {x | 1/((k:ℝ)+1) ≤ |χ j x|}).prod ν] U) :
    W =ᵐ[μ.prod ν] U := by
  have hlocal : ∀ᵐ x ∂μ, ∀ j k : ℕ, 1/((k:ℝ)+1) ≤ |χ j x| →
      (fun y => W (x,y)) =ᵐ[ν] (fun y => U (x,y)) := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro k
    exact (ae_restrict_iff' (measurableSet_le measurable_const (hχ j).abs)).mp
      (Measure.ae_ae_of_ae_prod (hpatch j k))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hW hU)).mpr
  filter_upwards [hcover,hlocal] with x hx hloc
  obtain ⟨j,hj⟩ := hx
  have ht : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨k,hk⟩ := (ht.eventually (gt_mem_nhds (abs_pos.mpr hj))).exists
  exact hloc j k hk.le

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
