import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialLoops
import OAI.Analysis.MatrixSigning.Realization.OptimizeRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialSearch
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCoordinates

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

instance poly_optView : PolyTime optView := by unfold optView;apply poly_reindex
instance poly_optB : PolyTime optB := by unfold optB;apply poly_then
instance poly_optF : PolyTime optF := by unfold optF;apply poly_then
instance poly_optScalars : PolyTime optScalars := by unfold optScalars;apply poly_then
instance poly_optDelta : PolyTime optDelta := by unfold optDelta;apply poly_then
instance poly_optRest : PolyTime optRest := by unfold optRest;apply poly_then
instance poly_optRadius : PolyTime optRadius := by unfold optRadius;apply poly_both
instance poly_optUpper : PolyTime optUpper := by unfold optUpper;apply poly_then
instance poly_optLevel : PolyTime optLevel := by unfold optLevel;apply poly_add
instance poly_optLevelPencil : PolyTime optLevelPencil := by unfold optLevelPencil;apply poly_congr
instance poly_optStateView : PolyTime optStateView := by unfold optStateView;apply poly_reindex
instance poly_osP : PolyTime osP := by unfold osP;apply poly_then
instance poly_osK : PolyTime osK := by unfold osK;apply poly_then
instance poly_osY : PolyTime osY := by unfold osY;apply poly_then
instance poly_isPSD : PolyTime isPSD := by unfold isPSD;apply poly_congr
instance poly_witnessStateView : PolyTime witnessStateView := by unfold witnessStateView;apply poly_reindex
instance poly_witnessEvaluation : PolyTime witnessEvaluation := by unfold witnessEvaluation;apply poly_changeOutput
instance poly_witnessNone : PolyTime witnessNone := by unfold witnessNone;apply poly_then
instance poly_osFeasible : PolyTime osFeasible := by
  unfold osFeasible
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_changeOutput
  · infer_instance

lemma RunsPoly.then_with {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
    {F : α → β} {G : β → γ} {ι : Type*} {L : ι → ℕ}
    {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a)
    (hs : IsPoly L (fun i => (eb (F (a i))).length) → RunsPoly L s (fun i => F (a i))) :
    RunsPoly L (r.then s) a := hr.then (hs hr.output)

def OptParams.searchCount (p : OptParams) : ℕ := RationalSDP.searchFuel p.n p.r p.R
variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_optCandidate (a : ι → OptParams×ℕ)
    (ha : IsPoly L (fun i => (prodCode optCode natCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.searchCount)) : RunsPoly L optCandidate a := by
  unfold optCandidate
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hout
  apply runsPoly_search
  · exact hout
  · exact hn

def candidateResource (p : OptParams×ℕ) : ℕ := (optCode p.1).length+p.2+p.1.searchCount
lemma candidate_cost_bound : ∃q : NaturalPolynomial,∀p,optCandidate.cost p≤q.eval (candidateResource p) := by
  have hw : IsPoly candidateResource (fun p => (optCode p.1).length) :=
    (isPoly_self candidateResource).mono (fun _ => by unfold candidateResource;omega)
  have hk : IsPoly candidateResource (fun p => (natCode p.2).length) :=
    (isPoly_self candidateResource).mono (fun _ => by simp only [natCode,List.length_replicate];unfold candidateResource;omega)
  have hn : IsPoly candidateResource (fun p => p.1.searchCount) :=
    (isPoly_self candidateResource).mono (fun _ => by unfold candidateResource;omega)
  exact (runsPoly_optCandidate id (isPoly_pair hw hk) hn).cost
lemma candidate_length_bound : ∃q : NaturalPolynomial,∀p,
    (vectorCode (List.ofFn (p.1.B.levelCandidate p.1.f p.1.delta p.1.r p.1.R p.1.U p.2))).length≤q.eval (candidateResource p) := by
  obtain ⟨p,hp⟩ := candidate_cost_bound
  refine ⟨3*X+1+p,?_⟩
  intro a
  have h := optCandidate.output_length a
  have hc := hp a
  simp only [prodCode_length,natCode,List.length_replicate] at h
  change _≤3*candidateResource a+1+p.eval (candidateResource a)
  unfold candidateResource at *
  omega
lemma runsPoly_osNext (a : ι → OptState)
    (ha : IsPoly L (fun i => (optStateCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).p.searchCount)) : RunsPoly L osNext a := by
  unfold osNext
  apply RunsPoly.changeOutput
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.ite (RunsPoly.of_poly _ a ha) (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hout
  apply runsPoly_optCandidate
  · exact hout
  · exact hn

def nextResource (s : OptState) : ℕ := (optStateCode s).length+s.p.searchCount
lemma osNext_cost_bound : ∃q : NaturalPolynomial,∀s,osNext.cost s≤q.eval (nextResource s) := by
  exact (runsPoly_osNext id ((isPoly_self nextResource).mono (fun _ => Nat.le_add_right _ _))
    ((isPoly_self nextResource).mono (fun _ => Nat.le_add_left _ _))).cost

lemma optimize_is_candidate (p : OptParams) (k : ℕ) : ∃j≤k,
    p.B.optimize p.f p.delta p.r p.R p.U k=p.B.levelCandidate p.f p.delta p.r p.R p.U j := by
  induction k with
  | zero => exact ⟨0,le_rfl,rfl⟩
  | succ k ih =>
      unfold RationalSDP.Pencil.optimize
      dsimp only
      split_ifs
      · obtain ⟨j,hj,he⟩ := ih
        exact ⟨j,by omega,he⟩
      · exact ⟨k+1,le_rfl,rfl⟩

lemma runsPoly_optInit (a : ι → OptParams)
    (ha : IsPoly L (fun i => (optCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).searchCount)) : RunsPoly L optInit a := by
  unfold optInit
  apply RunsPoly.changeOutput
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hout
  apply runsPoly_optCandidate
  · exact hout
  · exact hn

lemma opt_iterate_size_bound : ∃q : NaturalPolynomial,∀p k,
    (optStateCode (OptState.next^[k] p.init)).length≤q.eval ((optCode p).length+k+p.searchCount) := by
  obtain ⟨q,hq⟩ := candidate_length_bound
  refine ⟨4*X+2+q,?_⟩
  intro p k
  obtain ⟨j,hj,he⟩ := optimize_is_candidate p k
  have h : _≤q.eval ((optCode p).length+k+p.searchCount) := (hq (p,j)).trans (q.eval_mono (by change (optCode p).length+j+p.searchCount≤_;omega))
  dsimp only at h
  rw [opt_iterate]
  simp only [optStateCode,optStateData,optStateDataCode,prodCode_length,natCode,List.length_replicate]
  rw [he]
  change _≤4*((optCode p).length+k+p.searchCount)+2+q.eval ((optCode p).length+k+p.searchCount)
  omega

lemma optimize_loop_cost_bound : ∃q : NaturalPolynomial,∀p k,
    osNext.iterate.cost (k,p.init)≤q.eval ((optCode p).length+k+p.searchCount) := by
  obtain ⟨q,hq⟩ := opt_iterate_size_bound
  obtain ⟨r,hr⟩ := osNext_cost_bound
  refine ⟨3*X+X*(r.comp (q+X)+2)+3,?_⟩
  intro p k
  let T := (optCode p).length+k+p.searchCount
  have hk : k≤T := by unfold T;omega
  have ht := iterate_ticks_bound osNext p.init k (r.eval (q.eval T+T)) (by
    intro i hi
    apply (hr _).trans (r.eval_mono ?_)
    unfold nextResource
    have hs : _≤q.eval T := (hq p i).trans (q.eval_mono (by unfold T;omega))
    have hp : (OptState.next^[i] p.init).p=p := by rw [opt_iterate]
    rw [hp]
    have hn : p.searchCount≤T := by unfold T;omega
    omega)
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1)
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change 3*k+2+IterateRoutine.loopTicks osNext.cost OptState.next k p.init≤3*T+T*(r.eval (q.eval T+T)+2)+3
  omega

lemma runsPoly_optimize (a : ι → OptParams×ℕ)
    (ha : IsPoly L (fun i => (prodCode optCode natCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.searchCount)) : RunsPoly L optimize a := by
  have hp : IsPoly L (fun i => (optCode (a i).1).length) := ha.mono (fun i => le_prodCode_left (a i))
  have hk : IsPoly L (fun i => (a i).2) := ha.mono (fun i => by simpa only [natCode,List.length_replicate] using le_prodCode_right (ea:=optCode) (eb:=natCode) (a i))
  have hi := (RunsPoly.of_poly (first optCode natCode) a ha).then (runsPoly_optInit _ hp hn)
  have hin := (RunsPoly.of_poly (second optCode natCode) a ha).both hi
  obtain ⟨q,hq⟩ := optimize_loop_cost_bound
  have hlo : RunsPoly L osNext.iterate (fun i => ((a i).2,(a i).1.init)) :=
    ⟨hin.output,(((hp.add hk).add hn).eval q).mono (fun i => hq (a i).1 (a i).2)⟩
  unfold optimize
  apply RunsPoly.congr
  exact (hin.then hlo).then_poly osY
end CurrentKS.Realization

end OAI
