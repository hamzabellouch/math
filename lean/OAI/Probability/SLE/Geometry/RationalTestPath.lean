import OAI.Probability.SLE.Mass.RadonPathCertificates
import OAI.Probability.SLE.StoppedMeasures

namespace OAI

/-! A Borel certificate that rational test values extend to a continuous
real path. This makes the good-path event countably measurable. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported NNReal

namespace SLEExactGauge

local instance rationalTestPathMeasurable : MeasurableSpace C(ℝ,ℝ) := borel _
local instance rationalTestPathBorel : BorelSpace C(ℝ,ℝ) := ⟨rfl⟩

def rationalTestPathValues (f : C(ℝ,ℝ)) : ℚ → ℝ := fun q => f (q:ℝ)

lemma rationalTestPathValues_embedding : MeasurableEmbedding rationalTestPathValues := by
  apply Continuous.measurableEmbedding
  · exact continuous_pi fun q => continuous_eval_const (q:ℝ)
  · intro f g h
    apply DFunLike.coe_injective
    exact Rat.denseRange_cast.equalizer f.continuous g.continuous h

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

def HasContinuousRationalTests (D : LocalTestFamily X) (μ : ℚ → Measure X) : Prop :=
  ∀ j, (fun q => ∫ x, D.test j x ∂μ q) ∈ range rationalTestPathValues

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
lemma measurableSet_hasContinuousRationalTests
    {Y : Type*} [MeasurableSpace Y] (D : LocalTestFamily X)
    (μ : ℚ → Y → Measure X)
    (hm : ∀ q j, Measurable (fun y => ∫ x, D.test j x ∂μ q y)) :
    MeasurableSet {y | HasContinuousRationalTests D (fun q => μ q y)} := by
  simp only [HasContinuousRationalTests,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact rationalTestPathValues_embedding.measurableSet_range.preimage
    (measurable_pi_iff.mpr (fun q => hm q j))

theorem HasContinuousRationalTests.continuous_extension
    (D : LocalTestFamily upperHalfPlane) (μ : ℚ → Measure upperHalfPlane)
    (hr : ∀ q, (μ q).Regular) (hc : HasContinuousRationalTests D μ) :
    (∀ q : ℚ, 0 ≤ q → rationalRadonExtension (fun q (_ : Unit) => μ q) (q:ℝ).toNNReal () = μ q) ∧
    ∀ f : C_c(upperHalfPlane,ℝ),
      Continuous (fun t => ∫ z, f z ∂rationalRadonExtension (fun q (_ : Unit) => μ q) t ()) := by
  let : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
  choose F hF using hc
  have hcoord (t : ℝ≥0) (j : ℕ) :
      (∫ z, D.test j z ∂rationalRadonExtension (fun q (_ : Unit) => μ q) t ()) = F j (t:ℝ) := by
    let (n : ℕ) : IsFiniteMeasureOnCompacts (μ (leftRationalSample n t)) := by
      let := hr (leftRationalSample n t)
      infer_instance
    have hl (k : ℕ) : Tendsto (fun n => ∫ z, D.test k z ∂μ (leftRationalSample n t)) atTop
        (𝓝 (F k (t:ℝ))) := by
      have he (q : ℚ) : (∫ z, D.test k z ∂μ q)=F k (q:ℝ) := congr_fun (hF k) q |>.symm
      simpa only [he,Function.comp_def] using
        (F k).continuous.continuousAt.tendsto.comp (leftRationalSample_tendsto t)
    obtain ⟨ν,hν,_,hνl⟩ := D.exists_radon_limit (fun n => μ (leftRationalSample n t))
      (fun k => ⟨F k (t:ℝ),hl k⟩)
    have he := canonicalRadonLimit_identified (fun n => μ (leftRationalSample n t)) ν ⟨hν,hνl⟩
    change (∫ z, D.test j z ∂canonicalRadonLimit (fun n => μ (leftRationalSample n t))) = _
    rw [he]
    exact tendsto_nhds_unique (hνl (D.test j)) (hl j)
  constructor
  · intro q hq
    let := (rationalRadonExtension_regular (fun q (_ : Unit) => μ q) (q:ℝ).toNNReal ()).1
    let := hr q
    apply D.measure_eq_of_test_integrals
    intro j
    rw [hcoord,Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq)]
    exact congr_fun (hF j) q
  · apply D.continuous_integrals_of_tests
      (fun t => rationalRadonExtension (fun q (_ : Unit) => μ q) t ())
      (fun t => (rationalRadonExtension_regular _ t ()).1)
    intro j
    simp_rw [hcoord]
    exact (F j).continuous.comp NNReal.continuous_coe

end SLEExactGauge

end

end OAI
