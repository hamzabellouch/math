import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedMeshStep
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedPairUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution

namespace OAI

section

/-! # Positive three-collision access from a bounded incoming velocity -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem three_collision_access_positive {κ ρ ε c R b₀ : ℝ}
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
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))) :
    0 < ENNReal.ofReal (4*Real.pi*b₀*‖v-w₀‖)*
      ∫⁻ u, (∫⁻ a, accessWeight u (w₁ u) (w₂ u) (b₁ u) (b₂ u) κ ρ a
        ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w₀) := by
  have hne : v ≠ w₀ := by
    intro h
    rw [h,sub_self,norm_zero] at hve
    norm_num at hve
  have houtreal := outgoing_near_partner_positive hR hε0 v w₀ e hw₀ hv hne hnear
  have hout : 0 < outgoing (v,w₀) (ball e ε) :=
    (ENNReal.ofReal_pos.mpr houtreal).trans_le ENNReal.ofReal_toReal_le
  let k := (ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
    (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))
  have hk : 0 < k := by
    apply pos_iff_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))) (ne_of_gt hA)
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
  have hint : 0 < ∫⁻ u, (∫⁻ a, accessWeight u (w₁ u) (w₂ u) (b₁ u) (b₂ u) κ ρ a
      ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w₀) :=
    (pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hk) (ne_of_gt hout))).trans_le hbound
  have hb₀0 : 0 < b₀ := hc.trans_le hb₀
  have hvw : 0 < ‖v-w₀‖ := lt_of_lt_of_le (by norm_num) hve
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) (ne_of_gt hint))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A positive time window for three ordered collision waits -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev ThreeWaits := ℝ × (ℝ × ℝ)

def threeWaitBox (h : ℝ) : Set ThreeWaits :=
  Ioo 0 (h/4) ×ˢ (Ioo 0 (h/4) ×ˢ Ioo 0 (h/4))

theorem threeWaitBox_measurable (h : ℝ) : MeasurableSet (threeWaitBox h) :=
  measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)

theorem threeWaitBox_volume {h : ℝ} (hh : 0 < h) :
    0 < (volume : Measure ThreeWaits) (threeWaitBox h) := by
  rw [Measure.volume_eq_prod,threeWaitBox,Measure.prod_prod,
    Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ioo,sub_zero]
  have hp : 0 < ENNReal.ofReal (h/4) := ENNReal.ofReal_pos.mpr (by positivity)
  exact pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hp) (mul_ne_zero (ne_of_gt hp) (ne_of_gt hp)))

theorem threeWaitBox_sum {h : ℝ} (hh : 0 < h) {s : ThreeWaits}
    (hs : s ∈ threeWaitBox h) :
    0 < s.1 ∧ 0 < s.2.1 ∧ 0 < s.2.2 ∧ s.1+s.2.1+s.2.2 < h := by
  exact ⟨hs.1.1,hs.2.1.1,hs.2.2.1,by linarith [hs.1.2,hs.2.1.2,hs.2.2.2]⟩

theorem threeWaitBox_integral_pos {h : ℝ} (hh : 0 < h)
    {F : ThreeWaits → ℝ≥0∞} (hF : Measurable F)
    (hp : ∀ s ∈ threeWaitBox h, 0 < F s) :
    0 < ∫⁻ s in threeWaitBox h, F s := by
  apply (setLIntegral_pos_iff hF).mpr
  apply (threeWaitBox_volume hh).trans_le
  apply measure_mono
  intro s hs
  exact ⟨(ne_of_gt (hp s hs)),hs⟩

theorem three_wait_survival (C : ℝ≥0) (T : ℝ) (s : ThreeWaits) :
    clockSurvival C s.1*clockSurvival C s.2.1*clockSurvival C s.2.2*
      clockSurvival C (T-(s.1+s.2.1+s.2.2)) = clockSurvival C T := by
  rw [← clockSurvival_add,← clockSurvival_add,← clockSurvival_add]
  congr 1
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
