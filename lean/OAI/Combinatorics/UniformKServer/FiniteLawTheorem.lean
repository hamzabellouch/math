import Mathlib
import OAI.Combinatorics.UniformKServer.RealFlowBounds
import OAI.Combinatorics.UniformKServer.OfflineLaw

namespace OAI

noncomputable section

/-! The finite-law theorem has arbitrary request atoms and literal offline OPT.
Its endpoint is fixed by the instance, before the law or horizon are chosen. -/
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree PilotEdits TreeRounding
open scoped Classical
variable {n k : ℕ} [NeZero k]
local instance configEqFL : DecidableEq (Configuration n k) := fun a b=>Classical.propDecidable (a=b)

theorem finite_law (d : RationalMetric n) (s : Configuration n k) (hk : 2≤k) :
    ∃ B : ℝ,∀ (Ω : Type) [Fintype Ω] (N : ℕ) (word : Ω→List (Fin n)) (P : Law Ω),
      (∀ω,(word ω).length≤N) →
      ∃ F : RealFlow.Data (Fin n) (Configuration n k) (Fin k),
        RealFlow.Valid F serve PublicInput.allowed s N ∧
        P.expect (fun ω=>RealFlow.flowCost F (fun c r j=>(d.distance (c j) r : ℝ)) [] (word ω))≤
          absoluteRate*(Real.log (k+1))^2*P.expect (fun ω=>offlineCost d s (word ω))+B := by
  let := d.metric
  let R := metricRadius (X:=Fin n)
  have hR : 0<R := metricRadius_pos
  let A := fixedConfig R hR (s 0)
  obtain ⟨J,hJ,hsmall⟩ := terminal_scale A
  refine ⟨flowEndpoint A k J,?_⟩
  intro Ω inst N word P hb
  let D := data d s word P
  let ω₀ : PositiveSupport.Support P.weight := Classical.choice (support_nonempty P)
  have hp : D.Public := data_public d s word P
  have hdiam : ∀p q : Fin n,dist p q≤40*A.R := metricRadius_bounds
  let F := lawFlow (N:=N) (J:=J) A D hk hdiam ω₀ hp s
  have hv : RealFlow.Valid F serve PublicInput.allowed s N := literal_valid A D hk hdiam ω₀ hp s
  refine ⟨F,hv,?_⟩
  have hbound := literal_bound (N:=N) (J:=J) R hR (s 0) D hk hdiam ω₀ hp s hJ hsmall
  have hcost := data_cost d s word P hb
  change (∑t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))=_ at hcost
  rw [hcost] at hbound
  have hpre (ω : PositiveSupport.Support P.weight) :
      RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω)≤
      RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (D.transcript N ω) := by
    apply RealFlow.flowCost_prefix hv _ (fun _ _ _=>dist_nonneg) _ _
      (by rw [D.transcript_length])
    rw [←data_trace d s word P ω]
    exact HiddenHistory.trace_prefix s _ _ _ (hb ω)
  have he : P.expect (fun ω=>RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω))=
      average D.weight (fun ω=>RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω)) :=
    (PositiveSupport.weighted_sum P.weight P.nonneg
      (fun ω=>RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω))).symm
  change P.expect (fun ω=>RealFlow.flowCost F (fun c r j=>dist (c j) r) [] (word ω))≤_
  rw [he]
  exact (average_mono D.weight _ _ (fun ω=>(D.positive ω).le) hpre).trans hbound

end UniformKServer.OfflineLaw

end

end OAI
