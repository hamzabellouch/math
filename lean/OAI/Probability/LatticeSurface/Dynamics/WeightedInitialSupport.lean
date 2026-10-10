import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.WeightedBathDefinitions

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set ConvexSkorokhod

lemma weightedBodyMeasure_finite_pos {m : ℕ} (B : Body (FreeHeightSpace m))
    (c : FreeHeightSpace m) (r R : ℝ) (hr : 0<r)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R)
    (b : FreeHeightSpace m) : IsFiniteMeasure (weightedBodyMeasure B b) ∧
      weightedBodyMeasure B b univ ≠ 0 := by
  let ρ : FreeHeightSpace m → ℝ := fun x => Real.exp (inner ℝ b x)
  have hρ : Continuous ρ := by fun_prop
  let : IsLocallyFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have hcompact : IsCompact B.carrier :=
    (isCompact_closedBall c R).of_isClosed_subset B.closed (fun z hz => by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hR z hz)
  have hf : IsFiniteMeasure (weightedBodyMeasure B b) := by
    dsimp [weightedBodyMeasure]
    rw [← restrict_withDensity B.closed.measurableSet]
    exact isFiniteMeasure_restrict.mpr hcompact.measure_ne_top
  refine ⟨hf,?_⟩
  have hvol : (volume : Measure (FreeHeightSpace m)) B.carrier ≠ 0 := by
    apply ne_of_gt
    have hbp : 0<(volume : Measure (FreeHeightSpace m)) (Metric.ball c r) :=
      Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hr)
    exact hbp.trans_le (measure_mono (Metric.ball_subset_closedBall.trans hball))
  intro hzero
  have hac : volume.restrict B.carrier ≪ weightedBodyMeasure B b :=
    withDensity_absolutelyContinuous' (by fun_prop) (Filter.Eventually.of_forall (fun x =>
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'))
  exact hvol (by simpa using hac hzero)

lemma weightedBodyLaw_probability {m : ℕ} (B : Body (FreeHeightSpace m))
    (c : FreeHeightSpace m) (r R : ℝ) (hr : 0<r)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R)
    (b : FreeHeightSpace m) : IsProbabilityMeasure (weightedBodyLaw B b) := by
  obtain ⟨hf,hpos⟩ := weightedBodyMeasure_finite_pos B c r R hr hball hR b
  let := hf
  constructor
  simp only [weightedBodyLaw,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)

lemma weightedBodyLaw_support {m : ℕ} (B : Body (FreeHeightSpace m))
    (b : FreeHeightSpace m) : weightedBodyLaw B b B.carrierᶜ=0 := by
  have hz : weightedBodyMeasure B b B.carrierᶜ=0 := by
    apply withDensity_absolutelyContinuous
    simp [Measure.restrict_apply B.closed.measurableSet.compl]
  simp [weightedBodyLaw,Measure.smul_apply,hz]

lemma fullReflectedMap_continuous {m : ℕ} (B : Body (FreeHeightSpace m))
    (c : FreeHeightSpace m) (r R : ℝ) (hr : 0<r)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R) :
    Continuous (fullReflectedMap B c r R hr hball hR) := by
  have hproj : Continuous (project B) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (by
      intro x y
      simpa only [NNReal.coe_one,one_mul,dist_eq_norm] using project_nonexpansive B x y)).continuous
  exact (Classical.choose_spec (joint_causal_reflected_map B c r R hr hball hR)).1.comp
    (((hproj.comp continuous_fst).subtype_mk _).prodMk continuous_snd)

lemma fullReflectedMap_zero {m : ℕ} (B : Body (FreeHeightSpace m))
    (c : FreeHeightSpace m) (r R : ℝ) (hr : 0<r)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R)
    (p : FreeHeightSpace m × VectorPath (FreeHeightSpace m)) :
    fullReflectedMap B c r R hr hball hR p ⟨0,by norm_num⟩=project B p.1 := by
  obtain ⟨u,k,ν,hu,huc,hkc,hu0,hk0,hrest⟩ :=
    (Classical.choose_spec (joint_causal_reflected_map B c r R hr hball hR)).2.1
      ⟨project B p.1,project_mem B p.1⟩ p.2
  exact (hu ⟨0,by norm_num⟩).trans hu0

end BrownianForcing

end OAI
