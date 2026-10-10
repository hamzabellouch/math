import Mathlib
import OAI.Combinatorics.UniformKServer.OfflineDynamic
import OAI.Combinatorics.UniformKServer.HiddenHistory
import OAI.Combinatorics.UniformKServer.FiniteLawFinance
import OAI.Combinatorics.UniformKServer.MetricRealization

namespace OAI

noncomputable section

/-! No hidden-trajectory hypothesis is added: an optimal finite serving history
is selected for each atom of an arbitrary finite request law. -/
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree PilotEdits
open scoped Classical
variable {n k N : ℕ} [NeZero k] {Ω : Type} [Fintype Ω]

def history (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) : History n k :=
  (OfflineDynamic.optRat_attained d s w).choose

theorem history_map (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    (history d s w).map Prod.fst=w := (OfflineDynamic.optRat_attained d s w).choose_spec.1

theorem history_cost (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    costAlong d s (history d s w)=offlineCost d s w := by
  rw [OfflineDynamic.offline_eq_optRat]
  exact (OfflineDynamic.optRat_attained d s w).choose_spec.2

theorem history_length (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    (history d s w).length=w.length := by
  simpa only [List.length_map] using congrArg List.length (history_map d s w)

def data (d : RationalMetric n) (s : Configuration n k) (word : Ω→List (Fin n))
    (P : Law Ω) : HiddenFlow.Data (Fin n) (PositiveSupport.Support P.weight) k :=
  HiddenHistory.data s (fun ω=>history d s (word ω)) (fun ω=>P.weight ω)
    (fun ω=>ω.property) (PositiveSupport.total P.weight P.nonneg P.total)

theorem data_public (d : RationalMetric n) (s : Configuration n k) (word : Ω→List (Fin n))
    (P : Law Ω) : (data d s word P).Public := HiddenHistory.is_public _ _ _ _ _

theorem support_nonempty (P : Law Ω) : Nonempty (PositiveSupport.Support P.weight) := by
  by_contra hn
  have hz (ω : Ω) : P.weight ω=0 := by
    apply le_antisymm _ (P.nonneg ω)
    exact le_of_not_gt (fun h=>hn ⟨⟨ω,h⟩⟩)
  have hh := P.total
  simp only [hz,sum_const_zero] at hh
  norm_num at hh

theorem data_trace (d : RationalMetric n) (s : Configuration n k) (word : Ω→List (Fin n))
    (P : Law Ω) (ω : PositiveSupport.Support P.weight) :
    (data d s word P).transcript (word ω).length ω=word ω := by
  change HiddenHistory.trace s (history d s (word ω)) (word ω).length=word ω
  rw [←history_length d s (word ω),HiddenHistory.trace_full,history_map]

theorem data_cost (d : RationalMetric n) (s : Configuration n k) (word : Ω→List (Fin n))
    (P : Law Ω) (hb : ∀ω,(word ω).length≤N) :
    letI := d.metric
    (∑t∈range N,average (data d s word P).weight (moverCost (HiddenFlow.flow (data d s word P)) t))=
      P.expect (fun ω=>offlineCost d s (word ω)) := by
  let := d.metric
  simp only [average]
  simp_rw [HiddenFlow.expected_mover_cost]
  rw [sum_comm]
  have he (ω : PositiveSupport.Support P.weight) :
      (∑t∈range N,dist ((data d s word P).request t ω)
        ((data d s word P).position t ω ((data d s word P).chosen t ω)))=
          offlineCost d s (word ω) := by
    simp only [dist_comm]
    change (∑t∈range N,(d.distance
      (HiddenHistory.location s (history d s (word ω)) t (HiddenHistory.next s (history d s (word ω)) t).2)
      (HiddenHistory.next s (history d s (word ω)) t).1 : ℝ))=_
    rw [HiddenHistory.paid_sum,List.take_of_length_le (by rw [history_length]; exact hb ω),history_cost]
  simp_rw [←mul_sum,he]
  exact PositiveSupport.weighted_sum P.weight P.nonneg (fun ω=>offlineCost d s (word ω))

end UniformKServer.OfflineLaw

namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeRounding
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance configEqOL : DecidableEq (Fin k→X) := fun a b=>Classical.propDecidable (a=b)

theorem literal_valid (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public) (s : Fin k→X) :
    RealFlow.Valid (lawFlow (N:=N) (J:=J) A D hk hdiam ω₀ hpublic s)
      (fun c r j=>Function.update c j r) PublicInput.allowed s N := by
  convert lawFlow_valid (N:=N) (J:=J) A D hk hdiam ω₀ hpublic s using 1
  rfl

theorem literal_bound (R : ℝ) (hR : 0<R) (base : X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (hdiam : ∀p q : X,dist p q≤40*R) (ω₀ : Ω) (hpublic : D.Public) (s : Fin k→X)
    (hJ : 0<J) (hsmall : ∀p q : X,p≠q → 20*radius (fixedConfig R hR base) J<dist p q) :
    average D.weight (fun ω=>RealFlow.flowCost
      (lawFlow (N:=N) (J:=J) (fixedConfig R hR base) D hk hdiam ω₀ hpublic s)
      (fun c r j=>dist (c j) r) [] (D.transcript N ω))≤
      absoluteRate*(Real.log (k+1))^2*(∑t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
        flowEndpoint (fixedConfig R hR base) k J := by
  convert fixed_lawFlow_bound (N:=N) (J:=J) R hR base D hk hdiam ω₀ hpublic s hJ hsmall using 1
  apply congrArg (average D.weight)
  funext ω
  congr 1
  apply Subsingleton.elim

end UniformKServer.PartitionTree

end

end OAI
