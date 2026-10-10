import OAI.Probability.SLE.Mass.CanonicalRadonLimit

namespace OAI

/-! Raw Radon reconstruction from countable test-Cauchy data. The existing
canonical reconstruction tests Cauchy convergence in the data space itself;
its cutoff coordinates supply the local mass bounds. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

lemma LocalTestFamily.exists_raw_radon_limit
    (D : LocalTestFamily X) {Y : Type*} [MeasurableSpace Y]
    (μ : ℕ → Y → Measure X) (hμ : ∀ n y, (μ n y).Regular)
    (hm : ∀ n (f : C_c(X,ℝ)), Measurable (fun y => ∫ x, f x ∂μ n y)) :
    ∃ ν : Y → Measure X, Measurable ν ∧ (∀ y, (ν y).Regular) ∧
      ∀ y, (∀ j, CauchySeq (fun n => ∫ x, D.test j x ∂μ n y)) →
        ∀ f : C_c(X,ℝ), Tendsto (fun n => ∫ x, f x ∂μ n y) atTop (𝓝 (∫ x, f x ∂ν y)) := by
  let ν (y : Y) := canonicalRadonLimit (fun n => μ n y)
  refine ⟨ν,canonicalRadonLimit_measurable μ ?_ hm,
    fun y => canonicalRadonLimit_regular _,?_⟩
  · intro n y
    let := hμ n y
    infer_instance
  · intro y hy
    let (n : ℕ) : IsFiniteMeasureOnCompacts (μ n y) := by
      let := hμ n y
      infer_instance
    obtain ⟨η,hη,_,hl⟩ := D.exists_radon_limit (fun n => μ n y)
      (fun j => cauchySeq_tendsto_of_complete (hy j))
    have he : ν y=η := canonicalRadonLimit_identified _ η ⟨hη,hl⟩
    simpa only [he] using hl

end SLEExactGauge

end

end OAI
