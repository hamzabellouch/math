import OAI.Probability.SLE.Loewner.TargetDriverContinuation

namespace OAI

/-! The Brownian time scaling in the prescribed flow, and uniqueness of
the based Wiener law used by its deterministic coefficient formula. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

local instance normalizationPathMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance normalizationPathBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def normalizedDriver {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0) (ω : Ω) : Driver where
  toFun t := Real.sqrt κ*B (t/κ.toNNReal) ω
  continuous_toFun := continuous_const.mul ((hc ω).comp (continuous_id.div_const _))
  map_zero' := by simp [h0]

lemma normalizedDriver_measurable {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0) :
    Measurable (normalizedDriver κ B hc h0) := by
  apply ContinuousMapZero.isClosedEmbedding_toContinuousMap.measurableEmbedding.measurable_comp_iff.mp
  exact source_path_measurable _ (fun t => measurable_const.mul (hm _))

lemma normalizedDriver_matches {Ω : Type*} (κ : ℝ) (hκ : 0<κ)
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (ω : Ω) (s : ℝ) (_hs : 0 ≤ s) :
    Real.sqrt κ*B s.toNNReal ω=driverValue (normalizedDriver κ B hc h0 ω) (κ*s) := by
  change _=Real.sqrt κ*B ((κ*s).toNNReal/κ.toNNReal) ω
  rw [Real.toNNReal_mul hκ.le,mul_div_cancel_left₀ _ (Real.toNNReal_pos.mpr hκ).ne']

theorem normalizedDriver_isBrownian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (κ : ℝ) (hκ : 0<κ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) :
    IsBrownianReal (fun t ω => normalizedDriver κ B hc h0 ω t) P := by
  have h := hB.smul (c := (κ.toNNReal)⁻¹)
    (inv_ne_zero (Real.toNNReal_pos.mpr hκ).ne')
  change IsBrownianReal (fun t ω => Real.sqrt κ*B (t/κ.toNNReal) ω) P
  simpa only [NNReal.coe_inv,
    Real.coe_toNNReal _ hκ.le,Real.sqrt_inv,inv_inv,div_eq_mul_inv,mul_comm] using h

theorem normalizedDriver_isWiener {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (κ : ℝ) (hκ : 0<κ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0) :
    IsWiener (P.map (normalizedDriver κ B hc h0)) := by
  have hbp := normalizedDriver_measurable κ B hm hc h0
  have hBrownian := normalizedDriver_isBrownian κ hκ B hB hc h0
  refine ⟨⟨fun I => ?_⟩,Eventually.of_forall (fun b => map_continuous b)⟩
  have hI : Measurable (fun b : Driver => I.restrict (fun t => b t)) :=
    Measurable.of_eval (fun i => (continuous_eval_const (i:ℝ≥0)).measurable)
  refine ⟨hI.aemeasurable,?_⟩
  rw [Measure.map_map hI hbp]
  exact (hBrownian.hasLaw I).map_eq

theorem isWiener_unique (W V : WienerLaw) (hW : IsWiener W) (hV : IsWiener V) : W=V := by
  have hm : Measurable (fun b : Driver => fun t => b t) :=
    Measurable.of_eval (fun t => (continuous_eval_const t).measurable)
  have hleft : IsProjectiveLimit (W.map (fun b : Driver => fun t => b t))
      BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hm]
    exact (hW.hasLaw I).map_eq
  have hright : IsProjectiveLimit (V.map (fun b : Driver => fun t => b t))
      BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hm]
    exact (hV.hasLaw I).map_eq
  have he := congrArg (Measure.map (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)))
    (hleft.unique hright)
  have hd : Measurable (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [Measure.map_map hd hm,Measure.map_map hd hm] at he
  have hemb := (source_path_evaluation_embedding (E := ℝ)).comp
    ContinuousMapZero.isClosedEmbedding_toContinuousMap.measurableEmbedding
  exact hemb.map_injective he

theorem normalizedDriver_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (κ : ℝ) (hκ : 0<κ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (W : WienerLaw) (hW : IsWiener W) :
    HasLaw (normalizedDriver κ B hc h0) W P :=
  ⟨(normalizedDriver_measurable κ B hm hc h0).aemeasurable,
    isWiener_unique _ _ (normalizedDriver_isWiener κ hκ B hB hm hc h0) hW⟩

end SLEExactGauge.Target

end

end OAI
