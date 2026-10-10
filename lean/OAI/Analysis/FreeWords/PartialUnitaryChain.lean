import Mathlib
import OAI.Analysis.FreeWords.PartialUnitaryNorm
import OAI.Analysis.FreeWords.PartialUnitaryTrace
import OAI.Analysis.FreeWords.TraceL2Convergence

namespace OAI

noncomputable section

namespace KKLocalPatching.PartialUnitary

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKFactorSupport

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

local instance : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem directed_power_cauchy {I : Type*} [Nonempty I] [SemilatticeSup I]
    (f : I → PartialUnitary (ConcreteAlgebra M)) (hf : Monotone f) (k : ℤ) :
    CauchySeq (fun i => gnsVector (tracePositive τ) ((f i).power k)) := by
  let t (i:I) := (τ.map (f i).support).re
  have ht : Monotone t := fun i j hij => support_trace_mono τ (hf hij)
  have hb : BddAbove (Set.range t) := ⟨1,fun _ ⟨i,hi⟩ => hi ▸ support_trace_le_one τ (f i)⟩
  let T := ⨆ i,t i
  have hle (i:I) : t i≤T := le_ciSup hb i
  have hlim : Tendsto t atTop (𝓝 T) := tendsto_atTop_ciSup ht hb
  have hz : Tendsto (fun i => Real.sqrt (T-t i)) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ((tendsto_const_nhds (x := T)).sub hlim)
    simpa only [Function.comp_def,sub_self,Real.sqrt_zero] using hh
  apply cauchySeq_of_le_tendsto_0' (fun i => Real.sqrt (T-t i)) ?_ hz
  intro i j hij
  have hsq := power_dist_sq τ (hf hij) k
  have hh := Real.sq_sqrt (sub_nonneg.mpr (hle i))
  have hn := Real.sqrt_nonneg (T-t i)
  have hd := dist_nonneg (x := gnsVector (tracePositive τ) ((f i).power k))
    (y := gnsVector (tracePositive τ) ((f j).power k))
  change _ = t j-t i at hsq
  nlinarith [hle j]

theorem directed_limit {I : Type*} [Nonempty I] [SemilatticeSup I]
    (f : I → PartialUnitary (ConcreteAlgebra M)) (hf : Monotone f) :
    ∃ v : PartialUnitary (ConcreteAlgebra M), (∀ i, f i≤v) ∧
      ∀ k, Tendsto (fun i => gnsVector (tracePositive τ) ((f i).power k)) atTop
        (𝓝 (gnsVector (tracePositive τ) (v.power k))) := by
  have hex (k:ℤ) : ∃ a : ConcreteAlgebra M, ‖a‖≤1 ∧
      Tendsto (fun i => gnsVector (tracePositive τ) ((f i).power k)) atTop
        (𝓝 (gnsVector (tracePositive τ) a)) := by
    obtain ⟨z,hz,hlim⟩ := cauchySeq_tendsto_of_isComplete
      (gnsVector_closedBall_isClosed τ 1).isComplete
      (fun i => (show gnsVector (tracePositive τ) ((f i).power k) ∈
        gnsVector (tracePositive τ) '' Metric.closedBall (0:ConcreteAlgebra M) 1 from
          ⟨(f i).power k, by simpa only [Metric.mem_closedBall,dist_zero_right] using (f i).norm_power_le_one k,rfl⟩))
      (directed_power_cauchy τ f hf k)
    obtain ⟨a,ha,rfl⟩ := hz
    exact ⟨a,by simpa only [Metric.mem_closedBall,dist_zero_right] using ha,hlim⟩
  choose a ha hlim using hex
  have hadd (k l:ℤ) : a (k+l)=a k*a l := by
    apply gnsVector_injective τ
    have hm := tendsto_gns_mul τ 1 zero_le_one (fun i => (f i).norm_power_le_one k) (hlim k) (hlim l)
    have he (i:I) : (f i).power k*(f i).power l=(f i).power (k+l) := ((f i).add _ _).symm
    simp only [he] at hm
    exact tendsto_nhds_unique (hlim (k+l)) hm
  have hstar (k:ℤ) : star (a k)=a (-k) := by
    apply gnsVector_injective τ
    have hs := tendsto_gns_star τ (hlim k)
    simp only [power_star] at hs
    exact tendsto_nhds_unique hs (hlim (-k))
  let v : PartialUnitary (ConcreteAlgebra M) := ⟨a,hadd,hstar⟩
  refine ⟨v,?_,hlim⟩
  intro i k
  constructor
  · apply gnsVector_injective τ
    have hm := tendsto_gns_mul τ 1 zero_le_one (fun j => (f j).norm_power_le_one k)
      (hlim k) (tendsto_const_nhds (x := gnsVector (tracePositive τ) (f i).support))
    have he : (fun j => gnsVector (tracePositive τ) ((f j).power k*(f i).support)) =ᶠ[atTop]
        (fun _ => gnsVector (tracePositive τ) ((f i).power k)) := by
      filter_upwards [eventually_ge_atTop i] with j hij
      rw [(hf hij k).1]
    exact tendsto_nhds_unique hm (tendsto_const_nhds.congr' he.symm)
  · apply gnsVector_injective τ
    have hm := tendsto_gns_mul τ 1 zero_le_one (fun (_:I) => (f i).norm_support_le_one)
      (tendsto_const_nhds (x := gnsVector (tracePositive τ) (f i).support)) (hlim k)
    have he : (fun j => gnsVector (tracePositive τ) ((f i).support*(f j).power k)) =ᶠ[atTop]
        (fun _ => gnsVector (tracePositive τ) ((f i).power k)) := by
      filter_upwards [eventually_ge_atTop i] with j hij
      rw [(hf hij k).2]
    exact tendsto_nhds_unique hm (tendsto_const_nhds.congr' he.symm)

end

end KKLocalPatching.PartialUnitary
end

end OAI
