import OAI.Probability.SLE.Angle.TargetDiskVisit
import OAI.Probability.SLE.Mass.PositiveTraceMass
import OAI.Probability.SLE.Gauge.CenteredMomentJensen

namespace OAI

/-! Strict positivity of the exact finite-level disk coefficients. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma compactWeightedMass_pos (w : C(upperHalfPlane,ℝ≥0))
    (hw : ∀ z, 0<w z) (K : Set upperHalfPlane) (hK : IsCompact K)
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ] (hμ : 0<μ K) :
    0<compactWeightedMass w K μ := by
  rw [compactWeightedMass,integral_pos_iff_support_of_nonneg
    (fun z => (w z).coe_nonneg) (compact_weight_integrable w K hK μ)]
  have hs : Function.support (fun z => (w z:ℝ))=univ := by
    ext z
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (show (0:ℝ)<w z from hw z)
  rw [hs,Measure.restrict_apply_univ]
  exact hμ

namespace CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma centered_diskScalar_positive
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (u : ℝ) (hu : 0≤u)
    (hsmall : Real.exp (-u)<1/8) :
    ∀ᵐ ω ∂finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) u,
      0<C.diskScalar θ hθ (radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) u).toNNReal ω := by
  let z := Target.diskMapInv θ 0
  have hz : z∈upperHalfPlane := Target.diskMapInv_maps hθ (by simp)
  have hl := finiteCenteredLaw_live_compact hB κ hκ hκ8 γ G F (Eventually.of_forall hw) z hz u hu
  have hac : finiteCenteredLaw P κ B γ G z u ≪ P := withDensity_absolutelyContinuous P _
  have hp := hac.ae_le
    (C.positive_open_visited hB hc h0 hκ F hw hpublished)
  filter_upwards [hl,hp] with ω hω hpω
  obtain ⟨t,_,_,ht,_⟩ := hω
  have hf : radiusLevelTime (γ ω) (G ω) z u≠∞ := by rw [ht]; exact ENNReal.coe_ne_top
  obtain ⟨s,hs,hst,hvisit⟩ := Target.radius_level_visits_diskSource ((hc ω).const_mul _) (hw ω)
    θ hθ u hsmall hf
  have hpos := hpω (ball z (z.im/4)) isOpen_ball s
    (radiusLevelTime (γ ω) (G ω) z u).toNNReal hs hst hvisit
  have hmass : 0<C.process (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω
      (Target.diskSourceHalfPlane θ) :=
    hpos.trans_le (measure_mono (preimage_mono (Target.marked_ball_subset_diskSource hθ)))
  let := (C.radon (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω).2
  apply compactWeightedMass_pos _ _ _ (Target.diskSourceHalfPlane_compact hθ) _ hmass
  intro v
  apply NNReal.coe_pos.mp
  rw [Target.diskMassWeight_coe]
  exact Real.rpow_pos_of_pos (Target.diskMap_deriv_pos hθ v.property) _

include C in
lemma levelCoefficient_positive
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ)
    (hsmall : Real.exp (-(4*ℓ/κ))<1/8) :
    0<Target.levelCoefficient κ W ℓ 1 θ := by
  let z := Target.diskMapInv θ 0
  let u := 4*ℓ/κ
  have hu : 0≤u := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  let σ := fun ω => (radiusLevelTime (γ ω) (G ω) z u : WithTop ℝ≥0)
  have hσ := actual_radiusLevelTime_stopping hB
    (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)))
    hBm hc h0 κ hκ hκ8 γ G F hw z (Target.diskMapInv_maps hθ (by simp)) u hu
  have heσ : ∀ᵐ ω ∂P, σ ω=radiusLevelTime (γ ω) (G ω) z u := Eventually.of_forall (fun _ => rfl)
  let Q := finiteCenteredLaw P κ B γ G z u
  let : IsProbabilityMeasure Q := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F
    (Eventually.of_forall hw) z (Target.diskMapInv_maps hθ (by simp)) u hu
  obtain ⟨hi,he⟩ := C.centered_diskScalar_integrable_eq hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ 1 σ hσ heσ
  rw [he]
  simp only [pow_one] at hi ⊢
  have hfinite := finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F
    (Eventually.of_forall hw) z (Target.diskMapInv_maps hθ (by simp)) u u hu le_rfl σ
    (Eventually.of_forall (fun _ => le_rfl))
  have hp := C.centered_diskScalar_positive hB hc h0 hκ hκ8 F hw hpublished θ hθ u hu hsmall
  have hpos : ∀ᵐ ω ∂Q, 0<finiteStoppedScalar (C.diskScalar θ hθ) σ ω := by
    filter_upwards [hfinite,hp] with ω hf hpω
    simpa only [finiteStoppedScalar,ite_eq_right hf,σ,ENNReal.toNNReal] using hpω
  apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ h => h.le)) hi).2
  have hevent : Q (Function.support (finiteStoppedScalar (C.diskScalar θ hθ) σ))=Q univ :=
    measure_congr (hpos.mono (fun ω h => propext
      (show finiteStoppedScalar (C.diskScalar θ hθ) σ ω≠0 ↔ True from iff_true_intro h.ne')))
  rw [hevent,measure_univ]
  exact zero_lt_one

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
