import OAI.Probability.SLE.Geometry.FiniteStoppedScalar
import OAI.Probability.SLE.Geometry.FiniteCenteredConsistency

namespace OAI

/-! The moments of an increasing progressive mass, evaluated at radius
stops, increase with the finite centered law's terminal level. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

theorem finiteCenteredLaw_stoppedScalar_moment_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z∈upperHalfPlane) (v V : ℝ) (hv : 0≤v) (hvV : v≤V)
    (A : ℝ≥0 → Ω → ℝ)
    (hA : IsProgressive (Filtration.natural B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) A)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (σ τ : Ω → WithTop ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) σ)
    (_hτ : IsStoppingTime (Filtration.natural B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) τ)
    (hσeq : ∀ᵐ ω ∂P, σ ω=radiusLevelTime (γ ω) (G ω) z v)
    (hτeq : ∀ᵐ ω ∂P, τ ω=radiusLevelTime (γ ω) (G ω) z V) (m : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (finiteStoppedScalar A σ ω)^m ∂finiteCenteredLaw P κ B γ G z v) ≤
      ∫⁻ ω, ENNReal.ofReal (finiteStoppedScalar A τ ω)^m ∂finiteCenteredLaw P κ B γ G z V := by
  let Q := finiteCenteredLaw P κ B γ G z V
  have hσf : ∀ᵐ ω ∂Q, σ ω≠⊤ :=
    finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F hw z hz v V hv hvV σ
      (hσeq.mono (fun _ h => h.le))
  have hτf : ∀ᵐ ω ∂Q, τ ω≠⊤ :=
    finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F hw z hz V V
      (hv.trans hvV) le_rfl τ (hτeq.mono (fun _ h => h.le))
  have horder : ∀ᵐ ω ∂P, σ ω≤τ ω := by
    filter_upwards [hw,hσeq,hτeq] with ω hω hs ht
    rw [hs,ht]
    exact radiusLevelTime_mono ((hc ω).const_mul _) hω z hv hvV
  have habs : Q.AbsolutelyContinuous P := withDensity_absolutelyContinuous P _
  have heq : (∫⁻ ω, ENNReal.ofReal (finiteStoppedScalar A σ ω)^m ∂Q) =
      ∫⁻ ω, ENNReal.ofReal (finiteStoppedScalar A σ ω)^m ∂finiteCenteredLaw P κ B γ G z v := by
    apply lintegral_eq_of_stopped_events Q (finiteCenteredLaw P κ B γ G z v)
      hσ.measurableSpace hσ.measurableSpace_le
    · intro E hE
      exact finiteCenteredLaw_consistent_at_radius_stop hB hBm hc h0 κ hκ hκ8 γ G F hw
        z hz v V hv hvV σ hσ hσeq E hE
    · exact ((finiteStoppedScalar_measurable _ A hA σ hσ).ennreal_ofReal).pow_const m
  rw [← heq]
  apply lintegral_mono_ae
  filter_upwards [hσf,hτf,habs.ae_le horder,habs.ae_le hmono] with ω hs ht hst hm
  apply pow_le_pow_left'
  apply ENNReal.ofReal_le_ofReal
  simp only [finiteStoppedScalar,hs,ht,ite_false]
  apply hm
  exact WithTop.untopD_mono ht hst

end SLEExactGauge

end

end OAI
