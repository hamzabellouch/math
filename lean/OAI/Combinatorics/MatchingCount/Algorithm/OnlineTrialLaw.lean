import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineTrial
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineRequestLaw
import OAI.Combinatorics.MatchingCount.Probability.OnlineLayerLaw

namespace OAI

namespace MatchingFPRAS.OnlineTree
open PhysicalStream

lemma foldM_append_mean {A B : Type} (f : A×B→Experiment B) (as bs : List A) (b : B) (h : B→ℚ) :
    (foldM f (as++bs) b).mean h=(foldM f as b).mean (fun c=>(foldM f bs c).mean h) := by
  induction as generalizing b with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,foldM,Experiment.mean_bind,ih]
end MatchingFPRAS.OnlineTree

namespace MatchingFPRAS.OnlineTrial
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule OnlineStage
open Transport UnitRefresh Enlargement

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable def represent {j : ℕ} (p : Trial.Parameters G) (L : FiniteTrial.Layer p j) (x : L.Ω) : State :=
  ((fixedData p (L.state x),p.S),repr (product p L x))
lemma advance_source {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j)
    (xs : Fin p.S→RationalSource.Marked s.activity p.K) :
    advance (fixedData p s,vectorRep (s.update p.hn xs).scale)=fixedData p (s.update p.hn xs) := by
  unfold advance fixedData data
  simp only [List.replicate_succ]

lemma carry_represent {j : ℕ} (p : Trial.Parameters G) (hj : j≤p.K) (L : FiniteTrial.Layer p j)
    (x : (L.append p hj).Ω) :
    carry (represent p L x.1,
      (repr ((L.state x.1).ratioEstimate (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2)),
        vectorRep ((L.state x.1).update p.hn (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2)).scale))=
      represent p (L.append p hj) x := by
  unfold carry represent
  dsimp only
  rw [advance_source,mul_repr (product_nonneg p L _) ((L.state x.1).ratioEstimate_nonneg x.2),←product_append]
  rfl

lemma step_mean {j : ℕ} (p : Trial.Parameters G) (hj : j≤p.K) (L : FiniteTrial.Layer p j)
    (x : L.Ω) (h : State→ℚ) :
    (step (represent p L x)).mean h=
      qaverage (fun b=>h (represent p (L.append p hj) ⟨x,(L.state x).drawStage p hj b⟩)) := by
  unfold step
  rw [Experiment.mean_map]
  have hp : prepare (represent p L x).1 = (fixedData p (L.state x),(p.S,fixedRequest p (L.state x))) := by
    change (fixedData p (L.state x),(p.S,sourceRequest (fixedData p (L.state x),p.S)))=_
    rw [sourceRequest_source]
  rw [hp]
  change (transition p (L.state x)).mean (fun y=>h (carry (represent p L x,y)))=_
  rw [transition_mean p hj]
  apply qaverage_congr
  intro b
  have hc := carry_represent p hj L ⟨x,(L.state x).drawStage p hj b⟩
  dsimp only at hc ⊢
  exact congrArg h hc

lemma sweep_mean (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K) (h : State→ℚ) :
    (sweep (List.replicate j false,represent p (FiniteTrial.firstLayer p) PUnit.unit)).mean h=
      qaverage (fun b=>h (represent p (FiniteTrial.layers p j hj) (FiniteTrial.drawLayer p j hj b))) := by
  induction j generalizing h with
  | zero =>
    change h (represent p (FiniteTrial.firstLayer p) PUnit.unit)=qaverage (fun _=>h (represent p (FiniteTrial.firstLayer p) PUnit.unit))
    rw [qaverage_const]
  | succ j ih =>
    change (OnlineTree.foldM body (List.replicate (j+1) false) _).mean h=_
    rw [List.replicate_add,OnlineTree.foldM_append_mean]
    simp only [List.replicate_one,OnlineTree.foldM,body,Experiment.mean_bind,Experiment.mean]
    change (sweep (List.replicate j false,represent p (FiniteTrial.firstLayer p) PUnit.unit)).mean (fun x=>(step x).mean h)=_
    rw [ih (by omega)]
    rw [mean_layer_succ p hj (fun x=>h (represent p (FiniteTrial.layers p (j+1) hj) x))]
    apply qaverage_congr
    intro b
    exact step_mean p (by omega) (FiniteTrial.layers p j (by omega)) (FiniteTrial.drawLayer p j (by omega) b) h
end MatchingFPRAS.OnlineTrial

end OAI
