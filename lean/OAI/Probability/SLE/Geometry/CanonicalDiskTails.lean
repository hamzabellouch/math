import OAI.Probability.SLE.Geometry.CenteredDiskLaw
import OAI.Probability.SLE.Geometry.CenteredStoppedTails

namespace OAI

/-! The tails of the actual finite centered disk laws increase with the
radius level. Their supremum is sufficient; no infinite tilted path law
is postulated. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge

lemma measure_joint_tail_of_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure (α × β)) (η : Measure α) (Q : α → Measure β)
    (h : ∀ f : α × β → ℝ≥0∞, Measurable f →
      (∫⁻ p, f p ∂ν) = ∫⁻ a, ∫⁻ b, f (a,b) ∂Q a ∂η)
    (X : α × β → ℝ) (hX : Measurable X) (c : ℝ) :
    ν {p | c ≤ X p} = ∫⁻ a, Q a {b | c ≤ X (a,b)} ∂η := by
  have hA : MeasurableSet {p | c ≤ X p} := measurableSet_le measurable_const hX
  let f : α × β → ℝ≥0∞ := {p | c ≤ X p}.indicator 1
  have hf : Measurable f := (measurable_one : Measurable (1 : α × β → ℝ≥0∞)).indicator hA
  calc
    _ = ∫⁻ p, f p ∂ν := (lintegral_indicator_one hA).symm
    _ = ∫⁻ a, ∫⁻ b, f (a,b) ∂Q a ∂η := h f hf
    _ = _ := by
      apply lintegral_congr
      intro a
      have hpair : Measurable (fun b : β => (a,b)) := measurable_const.prodMk measurable_id
      have hAa : MeasurableSet {b | c ≤ X (a,b)} := hA.preimage hpair
      change (∫⁻ b, {b | c ≤ X (a,b)}.indicator 1 b ∂Q a) = _
      exact lintegral_indicator_one hAa

end SLEExactGauge

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

def centeredDiskTail (hc : ∀ ω, Continuous (fun t => B t ω)) (b u : ℝ) : ℝ≥0∞ :=
  centeredDiskLaw P κ B hc u {p | b ≤ C.diskAtRadius p.1 u p.2}

lemma centeredDiskTail_eq_integral
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0<κ) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (b u : ℝ) (hu : 0≤u) :
    C.centeredDiskTail hc b u = ∫⁻ θ,
      finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) u
        {ω | b ≤ C.diskAtRadius θ u ω} ∂Target.angleLaw κ := by
  exact measure_joint_tail_of_lintegral (centeredDiskLaw P κ B hc u) (Target.angleLaw κ)
    (fun θ => finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) u)
    (fun f hf => centeredDiskLaw_lintegral P κ hκ B
      (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc γ G F hw u hu f hf)
    (fun p => C.diskAtRadius p.1 u p.2) (C.diskAtRadius_joint_measurable hc F hw u hu) b

lemma diskAtRadius_tail_mono
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (b v V : ℝ) (hv : 0≤v) (hvV : v≤V) :
    finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) v {ω | b ≤ C.diskAtRadius θ v ω} ≤
      finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) V {ω | b ≤ C.diskAtRadius θ V ω} := by
  let z := Target.diskMapInv θ 0
  have hz : z ∈ upperHalfPlane := Target.diskMapInv_maps hθ (by simp)
  let σ := fun ω => radiusLevelTime (γ ω) (G ω) z v
  let τ := fun ω => radiusLevelTime (γ ω) (G ω) z V
  have hσ := actual_radiusLevelTime_stopping hB
    (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hc h0 κ hκ hκ8 γ G F hw z hz v hv
  have hf (w : ℝ) (hw0 : 0≤w) := finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F
    (Eventually.of_forall hw) z hz w w hw0 le_rfl
    (fun ω => radiusLevelTime (γ ω) (G ω) z w) (Eventually.of_forall (fun _ => le_rfl))
  have he (w : ℝ) (hw0 : 0≤w) :
      finiteCenteredLaw P κ B γ G z w {ω | b ≤ C.diskAtRadius θ w ω} =
      finiteCenteredLaw P κ B γ G z w
        {ω | b ≤ finiteStoppedScalar (C.diskScalar θ hθ)
          (fun ω => radiusLevelTime (γ ω) (G ω) z w) ω} := by
    apply measure_congr
    filter_upwards [hf w hw0] with ω hω
    rw [C.diskAtRadius_eq_finite θ hθ w
      (fun ω => radiusLevelTime (γ ω) (G ω) z w) ω rfl hω]
  rw [he v hv,he V (hv.trans hvV)]
  exact finiteCenteredLaw_stoppedScalar_tail_mono hB hBm hc h0 κ hκ hκ8 γ G F
    (Eventually.of_forall hw) z hz v V hv hvV (C.diskScalar θ hθ)
    (C.diskScalar_progressive θ hθ)
    ((C.compactWeightedMass_paths (Target.diskMassWeight κ θ hθ) (Target.diskSourceHalfPlane θ)
      (Target.diskSourceHalfPlane_compact hθ)).mono (fun _ h => h.1))
    σ τ hσ (Eventually.of_forall (fun _ => rfl)) (Eventually.of_forall (fun _ => rfl)) b

lemma centeredDiskTail_mono
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (b : ℝ) : MonotoneOn (C.centeredDiskTail hc b) (Ici 0) := by
  intro v hv V hV hvV
  rw [C.centeredDiskTail_eq_integral hc hκ F hw b v hv,
    C.centeredDiskTail_eq_integral hc hκ F hw b V hV]
  apply lintegral_mono_ae
  filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
  exact C.diskAtRadius_tail_mono hB hc h0 hκ hκ8 F hw θ hθ b v V hv hvV

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
