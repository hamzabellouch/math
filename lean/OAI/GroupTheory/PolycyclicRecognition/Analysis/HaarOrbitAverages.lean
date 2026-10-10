import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarInvariantRepresentative
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PointwiseOrbitAverages

namespace OAI

/-! # Convex orbit averages for locally compact group actions -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
  (μ : Measure X) [SFinite μ] [SMulInvariantMeasure G X μ]

theorem fixedL2_haarInvariantRepresentative (v : Lp ℝ 2 μ)
    (hfix : ∀ g : G, stationaryPullback μ g v = v) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] v ∧ ∀ (g : G) x, F (g • x) = F x := by
  apply aemeasurable_haarInvariantRepresentative μ v (Lp.aestronglyMeasurable v).aemeasurable
  intro g
  have hp : Lp.compMeasurePreserving (fun x : X => g • x)
      (measurePreserving_smul g μ) v = v := by
    simpa only [stationaryPullback, inv_inv] using hfix g⁻¹
  have he := Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g μ)
  rw [hp] at he
  exact he.symm

attribute [local instance] stationaryL2Action

theorem exists_L2_haarOrbitAverage (v : Lp ℝ 2 μ) :
    ∃ (w : Lp ℝ 2 μ) (F : X → ℝ),
      w ∈ closure (convexHull ℝ (range (fun g : G => stationaryPullback μ g v))) ∧
      Measurable F ∧ F =ᵐ[μ] w ∧ ∀ (g : G) x, F (g • x) = F x := by
  obtain ⟨w, hw, hfix⟩ := exists_fixed_in_convex_orbit (G := G) v
  obtain ⟨F, hF, he, hFi⟩ := fixedL2_haarInvariantRepresentative μ w hfix
  exact ⟨w, F, hw, hF, he, hFi⟩

theorem exists_pointwise_haarOrbitAverages (f : X → ℝ) (hf : MemLp f 2 μ) :
    ∃ (A : ℕ → FiniteOrbitAverage G) (F : X → ℝ),
      Measurable F ∧ (∀ (g : G) x, F (g • x) = F x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => (A n).apply f x) atTop (𝓝 (F x)) := by
  let v := hf.toLp f
  obtain ⟨w, F, hw, hF, he, hFi⟩ := exists_L2_haarOrbitAverage (G := G) μ v
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hw
  choose A hA using fun n => exists_finiteOrbitAverage (G := G) μ v (u n) (hu n)
  have hlim' : Tendsto (fun n => (A n).onL2 μ v) atTop (𝓝 w) := by
    simpa only [hA] using hlim
  have hmeas : TendstoInMeasure μ (fun n => (A n).apply f) atTop F := by
    have hcoe (n : ℕ) := ((A n).onL2_coe μ v).trans
      ((A n).apply_congr_ae μ hf.coeFn_toLp)
    exact TendstoInMeasure.congr hcoe he.symm (tendstoInMeasure_of_tendsto_Lp hlim')
  obtain ⟨ns, _, hns⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨A ∘ ns, F, hF, hFi, hns⟩

end PolycyclicRecognition

end

end OAI
