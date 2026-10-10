import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.GuardBits
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineGuard
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineTrialLaw

namespace OAI

namespace MatchingFPRAS.OnlineGuard
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule OnlineStage
open Transport UnitRefresh Enlargement Variation TreeTyped.Numbered
open scoped Classical

noncomputable local instance {n : ℕ} [Nontrivial (Fin n)] (w : Fin n→Fin n→ℝ) (K : ℕ) :
    Fintype (SourceMarked w K) := Fintype.ofFinite _
attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma guard_many_mean (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G p.K) (h : Bool→ℚ) :
    (test (fixedData p s,p.S)).mean h=
      qaverage (fun b=>h (decide (FiniteTrial.guardPass p s (s.drawGuard p b)))) := by
  classical
  have hD : 0<FiniteTrial.sourceD (G:=G) p.K := by
    rw [FiniteTrial.sourceD_eq]; exact Enlargement.sourceD_one p.K
  have hq : 0<copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K) := by
    simpa only [copies,vertexCount,FiniteTrial.sourceD_eq,Trial.Parameters.q,Trial.Parameters.N,Trial.Parameters.D] using p.q_pos
  let raw := realRawDraw s.activity p.K (FiniteTrial.sourceD (G:=G) p.K) (denominator p)
    s.activity_pos hD (s.cap le_rfl) hq p.even (1/denominator p)
  have hr : imageLaw raw=(s.runLaw p le_rfl).mass := by
    rw [realRawDraw_law]
    dsimp only [FiniteTrial.ScaleState.runLaw]
    apply finiteLaw_parameters
    · exact FiniteTrial.sourceD_eq p.K
    · simp only [denominator,Nat.cast_mul,Nat.cast_ofNat]
  have hp : imageLaw (fun bs : Fin 16→Raw s.activity p.K (FiniteTrial.sourceD (G:=G) p.K)
      (denominator p) (1/denominator p)=>fun i=>raw (bs i))=imageLaw (s.drawGuard p) := by
    rw [imageLaw_componentwise,hr,FiniteTrial.ScaleState.drawGuard_law]
    rfl
  unfold test
  rw [Experiment.mean_map,sourceRequest_source]
  unfold fixedRequest
  simp only [Trial.Parameters.N]
  rw [OnlineSample.mean_many]
  apply Eq.trans _ (qaverage_eq_of_imageLaw_eq _ _ hp (fun x=>h (decide (FiniteTrial.guardPass p s x))))
  apply qaverage_congr
  intro bs
  apply congrArg h
  have hcert (b : Raw s.activity p.K (FiniteTrial.sourceD (G:=G) p.K) (denominator p) (1/denominator p)) :
      sparseCertificate (fixedData p s,OnlineSample.sampleRep
        (fun i=>index (orderedEnum (BagEdge (RationalSource.bags s.activity p.K)) i)) b)=
      TreeFraction.repr (s.certificate p.K (raw b)) := by
    have hc:=sparseCertificate_source p.hn p.even s p.K (FiniteTrial.sourceD (G:=G) p.K)
      hD (s.cap le_rfl)
      (List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
      (List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
      (by simpa using hq) b.1 (fun e=>b.2 ((orderedEnum _).symm e))
    dsimp only at hc
    simp only [List.map_ofFn] at hc
    change sparseCertificate (fixedData p s,_) = _ at hc
    rw [generated_eq_raw] at hc
    rw [FiniteTrial.ScaleState.certificate,realRawDraw_inverse]
    simpa only [OnlineSample.sampleRep,OnlineSample.scanRep,OnlineSample.localRep,
      List.map_ofFn,Function.comp_def,Equiv.symm_apply_apply,NumericLadder.localBitsRep] using hc
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [accept,List.any_eq_true,List.mem_ofFn,FiniteTrial.guardPass]
  constructor
  · rintro ⟨x,⟨i,rfl⟩,hi⟩
    rw [hcert,positive_repr (s.certificate_range p.K _).1,decide_eq_true_eq] at hi
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    refine ⟨_,⟨i,rfl⟩,?_⟩
    rw [hcert,positive_repr (s.certificate_range p.K _).1,decide_eq_true_eq]
    exact hi

lemma checked_mean (p : Trial.Parameters G) (x : (FiniteTrial.layers p p.K le_rfl).Ω) (h : Fraction→ℚ) :
    (checked (OnlineTrial.represent p (FiniteTrial.layers p p.K le_rfl) x)).mean h=
      qaverage (fun b=>h (TreeFraction.repr (FiniteTrial.guardedOutput p ⟨x,((FiniteTrial.layers p p.K le_rfl).state x).drawGuard p b⟩))) := by
  unfold checked OnlineTrial.represent
  rw [Experiment.mean_map,guard_many_mean]
  apply qaverage_congr
  intro b
  simp only [finish,decide_eq_true_eq,FiniteTrial.guardedOutput,OnlineTrial.product,FiniteTrial.output]
  split_ifs <;> rfl

lemma trial_mean (p : Trial.Parameters G) (h : Fraction→ℚ) :
    (trial (List.replicate p.K false,OnlineTrial.represent p (FiniteTrial.firstLayer p) PUnit.unit)).mean h=
      qaverage (fun b=>h (TreeFraction.repr (FiniteTrial.guardedBitOutput p b))) := by
  unfold trial
  rw [Experiment.mean_bind,OnlineTrial.sweep_mean p p.K le_rfl]
  simp_rw [checked_mean]
  change _=qaverage ((fun c : (Fin (p.K*FiniteTrial.stageBits p)→Bool)×(Fin (FiniteTrial.guardBits p)→Bool)=>
    h (TreeFraction.repr (FiniteTrial.guardedOutput p ⟨FiniteTrial.drawLayer p p.K le_rfl c.1,
      ((FiniteTrial.layers p p.K le_rfl).state (FiniteTrial.drawLayer p p.K le_rfl c.1)).drawGuard p c.2⟩))) ∘
      pairBitsEquiv (p.K*FiniteTrial.stageBits p) (FiniteTrial.guardBits p))
  rw [qaverage_equiv,qaverage_prod]
end MatchingFPRAS.OnlineGuard

end OAI
