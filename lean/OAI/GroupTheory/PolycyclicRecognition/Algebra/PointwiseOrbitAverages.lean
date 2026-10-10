import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrbitAverage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantL2Representative
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

namespace OAI

/-! # Almost-everywhere convergence of finite orbit averages

For a countable measure-preserving action, finite convex averages of any L2
function have a subsequence converging almost everywhere to an exactly
invariant measurable function. These are actual functions, so the convergence
can be disintegrated to the conditional measures.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {G X : Type*} [Group G] [MeasurableSpace X]
  [MulAction G X] [MeasurableConstSMul G X]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

theorem FiniteOrbitAverage.apply_congr_ae (A : FiniteOrbitAverage G) {f h : X → ℝ}
    (hfh : f =ᵐ[μ] h) : A.apply f =ᵐ[μ] A.apply h := by
  have hi (i : A.index) : (fun x => f ((A.element i)⁻¹ • x)) =ᵐ[μ]
      fun x => h ((A.element i)⁻¹ • x) :=
    (measurePreserving_smul (A.element i)⁻¹ μ).quasiMeasurePreserving.ae_eq_comp hfh
  filter_upwards [ae_all_iff.2 hi] with x hx
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun t : ℝ => A.weight i * t) (hx i))

variable [Countable G]

/-- The measurable invariant limit of genuine finite orbit averages. -/
theorem exists_pointwise_orbitAverages (f : X → ℝ) (hf : MemLp f 2 μ) :
    ∃ (A : ℕ → FiniteOrbitAverage G) (F : X → ℝ),
      Measurable F ∧ (∀ (g : G) x, F (g • x) = F x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => (A n).apply f x) atTop (𝓝 (F x)) := by
  let v := hf.toLp f
  obtain ⟨w, F, hw, hF, he, hFi⟩ := exists_L2_orbitAverage (G := G) μ v
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
