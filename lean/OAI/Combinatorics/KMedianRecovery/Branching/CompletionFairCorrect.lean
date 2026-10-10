import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricArrays
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalCap
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionRealizeMath

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α β : Type*} [LinearOrder α] [AddCommMonoid β]
lemma sum_enum (S : Finset α) (f : α→β) : (∑ i:Fin S.card,f (enum S i))=∑ x∈S,f x := by
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ enum S)).sum = _
  rw [←List.map_ofFn,enum_list,←List.sum_toFinset f (S.sort_nodup (·≤·)),Finset.sort_toFinset]
end MetricKMedianRecovery.SortedIndex
namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open Completion
variable {n q a r b : ℕ} [PseudoMetricSpace (Fin n)]
lemma realize_le_surrogate
    (D F S Q G : Finset (Fin n)) (hS : S⊆F) (hn : S.Nonempty) (hQ : Q⊆S)
    (part : Fin q→Fin a) (o : Fin a→Fin q) (ho : ∀ j,part (o j)=j) (loc : Fin q→Fin n)
    (w : Fin a→Fin n) (radius : Fin a→ℝ) (M : ℝ)
    (assignment : Fin n→Virtual (Fin n) a)
    (hamem : ∀ p,assignment p∈withGhosts (S\Q))
    (hadist : ∀ p,virtualDistance w radius M p (assignment p)=virtualNearest (S\Q) w radius M p)
    (hr : ∀ i,0≤radius i) (hM0 : 0≤M)
    (hloc : ∀ e,loc e∈F) (hball : ∀ e,dist (w (part e)) (loc e)≤radius (part e))
    (hM : ∀ x,∀ f∈F,dist x f≤M)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n)
    (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
    (hred : ∀ i,redLoc i∈S\Q) (hblue : ∀ i,blueLoc i∈S\Q)
    (hRB : ∀ i j,redLoc i≠blueLoc j)
    (hG : G⊆S\Q) (hGR : ∀ i,redLoc i∉G) (hGB : ∀ i,blueLoc i∉G)
    (hdest : ∀ i,blueDest i∈F) (c k : ℕ) (hdestCount : (Finset.univ.image blueDest).card≤c)
    (hcount : a+c≤Q.card+k+b) (hk : k≤r) (K : ℝ)
    (hK : (∑ i,assignmentWeight D assignment (blueLoc i)*dist (blueLoc i) (blueDest i))≤K)
    (base : Fin D.card→ℚ) (distance : Fin D.card→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (hbase : ∀ i,(base i:ℝ)=virtualNearest (S\Q) w radius M (SortedIndex.enum D i))
    (hdistance : ∀ i e,(distance i e:ℝ)=dist (SortedIndex.enum D i) (loc e))
    (hweight : ∀ i,(weight i:ℝ)=assignmentWeight D assignment (redLoc i))
    (hredBase : ∀ i,(redBase i:ℝ)=virtualNearest G w radius M (redLoc i))
    (hredDistance : ∀ i e,(redDistance i e:ℝ)=dist (redLoc i) (loc e))
    (xs : List (Fin q)) (hX : Categorical.PartitionFeasible part xs.toFinset) :
    let T:=BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k
    let U:=Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs T
    U⊆F ∧ U.card=S.card ∧ ∃ hU:U.Nonempty,
      (∑ p∈D,distanceTo U hU p)≤
        surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
          (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) xs.toFinset := by
  let T:=BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k
  have hT : T.card=k := by rw [BinaryRationalSort.indexSet_card,Nat.min_eq_left hk]
  have hc : a+c≤Q.card+k+Fintype.card (Fin b) := by simpa only [Fintype.card_fin] using hcount
  have hh:=Canonical.realize_spec D F S Q G hS hn hQ part o ho loc w radius M assignment hamem hadist hr hM0 hloc hball hM
    redLoc blueLoc blueDest hredInj hblueInj hred hblue hRB hG hGR hGB hdest hdestCount hc K hK xs hX T hT
  obtain ⟨hF,hcard,hU,hcost⟩:=hh
  refine ⟨hF,hcard,hU,?_⟩
  have hclients : (∑ i:Fin D.card,cappedCost (base i:ℝ) (fun e=>(distance i e:ℝ)) xs.toFinset)=
      ∑ p∈D,cappedCost (virtualNearest (S\Q) w radius M p) (fun e=>dist p (loc e)) xs.toFinset := by
    simp_rw [hbase,hdistance]
    exact SortedIndex.sum_enum D (fun p => cappedCost (virtualNearest (S\Q) w radius M p) (fun e=>dist p (loc e)) xs.toFinset)
  have hreds : (∑ i∈T,assignmentWeight D assignment (redLoc i)*
      cappedCost (virtualNearest G w radius M (redLoc i)) (fun e=>dist (redLoc i) (loc e)) xs.toFinset)=
      bottomSum k (fun i=>(weight i:ℝ)*cappedCost (redBase i:ℝ) (fun e=>(redDistance i e:ℝ)) xs.toFinset) := by
    have hh:=BinaryRationalSort.indexSet_sum (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k
    simp only [Rat.cast_mul,BinaryCompletion.capped_cast] at hh
    simpa only [hweight,hredBase,hredDistance] using hh
  exact hcost.trans_eq (by rw [surrogate,hclients,←hreds])
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

end OAI
