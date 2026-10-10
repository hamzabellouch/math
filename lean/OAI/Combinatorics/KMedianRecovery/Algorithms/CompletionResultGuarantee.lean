import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchChecksCorrect
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionFairCorrect

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open Completion Categorical FiniteSampling
variable {n q a r b : ℕ} [PseudoMetricSpace (Fin n)]
lemma result_guarantee
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
    (hp : Function.Surjective part) (hw : ∀ i,0≤weight i) :
    (∀ bits, result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits ⊆ F ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).card=S.card ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).Nonempty) ∧
    ∀ X, PartitionFeasible part X →
      average (fun bits=> realCost D (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits)) ≤
      (38/100:ℝ)*surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) ∅ +
      (62/100:ℝ)*surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) X := by
  have hh : ∀ bits,
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits)⊆F ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).card=S.card ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).Nonempty ∧
      realCost D (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits) ≤
        surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ))
        (BinaryCompletionAlgorithm.choices k base distance weight redBase redDistance part hp
          (binarySeedEquiv (Fin q) a (Explicit.exponent a) (Explicit.samples q a) bits)).toFinset := by
    intro bits
    have hh:=realize_le_surrogate D F S Q G hS hn hQ part o ho loc w radius M assignment hamem hadist hr hM0 hloc hball hM
      redLoc blueLoc blueDest hredInj hblueInj hred hblue hRB hG hGR hGB hdest c k hdestCount hcount hk K hK
      base distance weight redBase redDistance hbase hdistance hweight hredBase hredDistance
      (BinaryCompletionAlgorithm.choices k base distance weight redBase redDistance part hp
        (binarySeedEquiv (Fin q) a (Explicit.exponent a) (Explicit.samples q a) bits))
      (BinaryCompletionAlgorithm.choices_feasible k base distance weight redBase redDistance part hp _)
    obtain ⟨hF,hc,hn,hcost⟩:=hh
    refine ⟨hF,hc,hn,?_⟩
    unfold realCost
    split_ifs with hnon
    · exact hcost
    · exact False.elim (hnon hn)
  refine ⟨fun bits=>⟨(hh bits).1,(hh bits).2.1,(hh bits).2.2.1⟩,?_⟩
  intro X hX
  exact (average_mono (fun bits=>(hh bits).2.2.2)).trans
    (BinaryCompletionAlgorithm.choices_expected K k base distance weight redBase redDistance part hp hw X hX)
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

end OAI
