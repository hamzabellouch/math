import OAI.Probability.SLE.Geometry.CenteredStoppedMonotonicity

namespace OAI

/-! Tail events of increasing canonical scalars under consistent finite laws.
Only the stopped past is transported when the terminal level is increased. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

theorem finiteCenteredLaw_stoppedScalar_tail_mono
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
    (hσeq : ∀ᵐ ω ∂P, σ ω=radiusLevelTime (γ ω) (G ω) z v)
    (hτeq : ∀ᵐ ω ∂P, τ ω=radiusLevelTime (γ ω) (G ω) z V) (b : ℝ) :
    finiteCenteredLaw P κ B γ G z v {ω | b ≤ finiteStoppedScalar A σ ω} ≤
      finiteCenteredLaw P κ B γ G z V {ω | b ≤ finiteStoppedScalar A τ ω} := by
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
  have he := finiteCenteredLaw_consistent_at_radius_stop hB hBm hc h0 κ hκ hκ8 γ G F hw
    z hz v V hv hvV σ hσ hσeq {ω | b ≤ finiteStoppedScalar A σ ω}
    (measurableSet_le measurable_const (finiteStoppedScalar_measurable _ A hA σ hσ))
  rw [← he]
  apply measure_mono_ae
  filter_upwards [hσf,hτf,habs.ae_le horder,habs.ae_le hmono] with ω hs ht hst hm
  intro hb
  apply hb.trans
  simp only [finiteStoppedScalar,hs,ht,ite_false]
  exact hm (WithTop.untopD_mono ht hst)

/-- A finite-law moment gives a tail bound without constructing an infinite
centered path law. This form is convenient before taking the level supremum. -/
lemma stoppedScalar_tail_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X)
    (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    ENNReal.ofReal (b^n)*Q {ω | b ≤ X ω} ≤ ∫⁻ ω, ENNReal.ofReal (X ω)^n ∂Q := by
  have he : ENNReal.ofReal (b^n)=ENNReal.ofReal b^n := ENNReal.ofReal_pow hb n
  rw [he]
  apply le_trans ?_ (mul_meas_ge_le_lintegral (hX.ennreal_ofReal.pow_const n) (ENNReal.ofReal b^n))
  apply mul_le_mul' le_rfl
  apply measure_mono
  intro ω hω
  exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hω) n

end SLEExactGauge

end

end OAI
