import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceGrowthBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedPairUniformIntegrability

namespace OAI

section

/-! # Compatible velocity-entry and positive-growth parameters -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem exists_access_growth_parameters : ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧
    (referenceClock : ℝ)*κ < referenceGrowth ∧
    ∀ d : ℝ, 0 < d → d ≤ 1/2 → ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/12 ∧
      6*ε ≤ d*κ/4 ∧
      0 < (sphereProbability.prod sphereProbability) (accessAngles κ (d*κ/8)) := by
  obtain ⟨δ,hδ,_hδsmall,haccess⟩ := accessAngles_positive
  let κ := min (δ/4) (1/1000)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκbound : κ ≤ (1:ℝ)/1000 := min_le_right _ _
  have hκδ : κ ≤ δ/4 := min_le_left _ _
  have hκ1 : κ < 1 := hκbound.trans_lt (by norm_num)
  have hg : (referenceClock : ℝ)*κ < referenceGrowth := by
    change (48*Real.pi)*κ < 11*Real.pi/6
    have hh := mul_le_mul_of_nonneg_left hκbound (show 0 ≤ 48*Real.pi by positivity)
    nlinarith [Real.pi_pos]
  refine ⟨κ,hκ,hκ1,hg,?_⟩
  intro d hd hdsmall
  let ε := min (1/12) (d*κ/24)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεb : ε ≤ 1/12 := min_le_left _ _
  have hεr : 6*ε ≤ d*κ/4 := by
    have hh : ε ≤ d*κ/24 := min_le_right _ _
    linarith
  refine ⟨ε,hε,hεb,hεr,haccess κ (d*κ/8) hκ (by positivity) ?_⟩
  have hdκ := mul_le_mul_of_nonneg_right hdsmall hκ.le
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The fixed angular-pair entry integral equals the iterated physical gains -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem accessWeight_iterated (v w₁ : V) (w₂ : Sphere → V) (b₁ : ℝ) (b₂ : Sphere → ℝ)
    (hw₂ : Measurable w₂) (hb₂ : Measurable b₂) (κ ρ : ℝ) :
    (∫⁻ a, accessWeight v (fun _ => w₁) (fun a => w₂ a.1)
      (fun _ => b₁) (fun a => b₂ a.1) κ ρ a ∂sphereProbability.prod sphereProbability) =
      ENNReal.ofReal (4*Real.pi*b₁*‖v-w₁‖)*
        ∫⁻ n₁ : Sphere, ENNReal.ofReal (4*Real.pi*b₂ n₁*‖child v w₁ n₁.1-w₂ n₁‖)*
          ∫⁻ n₂ : Sphere, (ball (κ • firstAxis) ρ).indicator (fun _ => (1:ℝ≥0∞))
            (child (child v w₁ n₁.1) (w₂ n₁) n₂.1) ∂sphereProbability ∂sphereProbability := by
  have hu : Measurable (fun a : Sphere × Sphere => child v w₁ a.1.1) := by
    unfold child
    fun_prop
  have hw : Measurable (fun a : Sphere × Sphere => w₂ a.1) := hw₂.comp measurable_fst
  have hb : Measurable (fun a : Sphere × Sphere => b₂ a.1) := hb₂.comp measurable_fst
  have hz : Measurable (fun a : Sphere × Sphere => child (child v w₁ a.1.1) (w₂ a.1) a.2.1) := by
    unfold child
    fun_prop
  have hI : Measurable ((ball (κ • firstAxis) ρ).indicator (fun _ : V => (1:ℝ≥0∞))) :=
    measurable_const.indicator measurableSet_ball
  have hM : Measurable (fun a : Sphere × Sphere => accessWeight v (fun _ => w₁)
      (fun a => w₂ a.1) (fun _ => b₁) (fun a => b₂ a.1) κ ρ a) := by
    exact (measurable_const.mul
      ((measurable_const.mul hb).mul (hu.sub hw).norm).ennreal_ofReal).mul (hI.comp hz)
  rw [lintegral_prod _ hM.aemeasurable]
  simp only [accessWeight]
  simp_rw [mul_assoc,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
