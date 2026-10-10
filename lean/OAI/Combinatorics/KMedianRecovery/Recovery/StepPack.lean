import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.StepMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
attribute [local irreducible] BinaryFiniteMachine.continuation BinaryFiniteCross.run
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
  (Q₀ : Finset (Label (Fin m))) (v z b : ℚ) (n q precision k : ℕ) (s : State (Fin m))
local notation "xx" => pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q b precision k s
lemma bf_pack (i : ℕ) : bf i xx=field i (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) := by
  simp only [bf,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,Option.getD_some]
lemma sf_pack (i : ℕ) : sf i xx=field i (stateBits s) := by
  simp only [sf,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma mapped_pack : mappedFree xx=setBits s.mapFree ∧ mappedPrefix xx=historyBits s.mapPrefix := by
  simp only [mappedFree,mappedPrefix,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryCoupled.mapFree_pack,BinaryCoupled.mapPrefix_pack,and_self]
lemma Q_pack : Q xx=setBits (after ∅ s.mapPrefix) := by
  dsimp only [Q]
  rw [(mapped_pack distance loc F Q₀ v z b n q precision k s).2]
  simpa only [setBits,BinaryLabel.orderedSort,Finset.sort_empty,labels,List.map_nil,encode] using BinaryFiniteMachine.after_pack ∅ s.mapPrefix
lemma power_pack : power xx=BinaryRational.encode ((1+v^2)^q) := by
  simp only [power,bf_pack]
  simp only [pack,BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryPhaseCount.power_pack]
lemma base_pack : base xx=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original)
    (after ∅ s.mapPrefix) v ((1+v^2)^q) s.lam' := by
  simp only [base,bf_pack,sf_pack,Q_pack,power_pack]
  simp only [BinaryFiniteContext.pack,stateBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma tails_pack (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
    (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : H xx=labels H₀ ∧ T xx=historyBits T₀ ∧ G xx=labels G₀ ∧ U xx=historyBits U₀ := by
  simp only [H,T,G,U,sf_pack]
  simp only [stateBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,hT,hU,
    BinaryCoupled.historyBits_cons,head_cons,tail_cons,and_self]
lemma W_pack (G₀ : List (Label (Fin m))) (U₀ : List (List (Label (Fin m)))) (hU : s.U=G₀::U₀) :
    W xx=historyBits (FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
      (F.image original) v s.lam' (q+1) n (after ∅ s.mapPrefix∪G₀.toFinset)) := by
  have hg : G xx=labels G₀ := by
    simp only [G,sf_pack]
    simp only [stateBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,hU,
      BinaryCoupled.historyBits_cons,head_cons]
  have hbase : contBase xx=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original)
      (after ∅ s.mapPrefix∪G₀.toFinset) v ((1+v^2)^q) s.lam' := by
    simp only [contBase,QG,bf_pack,sf_pack,Q_pack,power_pack,hg,BinaryFiniteContext.union_list_pack]
    simp only [BinaryFiniteContext.pack,stateBits,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [W,hbase]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  change BinaryFiniteMachine.continuation (pairBits (List.replicate n true,pairBits (List.replicate (q+1) true,_)))=_
  exact BinaryFiniteMachine.continuation_pack ..
lemma ctx_pack : ctx xx=BinaryCross.ctxBits (F.image original) (after ∅ s.mapPrefix) k := by
  simp only [ctx,bf_pack,Q_pack]
  simp only [pack,BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryCross.ctxBits]
lemma a_pack : a xx=(s.a F).bits := by
  simp only [a,Q_pack,sf_pack,bf_pack]
  simp only [stateBits,BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFiniteMachine.after_pack,BinaryFiniteContext.countInter_pack,State.a]
lemma banks_pack : banks xx=setBits (CanonicalCoupledMerge.banks F s.mapFree q) := by
  simp only [banks,bankInput,bf_pack,(mapped_pack distance loc F Q₀ v z b n q precision k s).1]
  simp only [qbits,pack,BinaryFiniteContext.pack,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,List.length_replicate]
  exact BinaryFiniteContext.banks_pack F s.mapFree q
lemma keys_pack : key xx=(3*q).bits ∧ spare xx=(3*q+1).bits ∧ leafKey xx=(3*q+2).bits := by
  simp only [key,spare,leafKey,qbits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,List.length_replicate,
    value_bits,and_self]
local notation "WW" => (fun G₀ : List (Label (Fin m)) => FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
  (F.image original) v s.lam' (q+1) n (after ∅ s.mapPrefix∪List.toFinset G₀))
lemma c_pack (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
    (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : c xx=(CanonicalMergeCrossing.finalCount (F.image original) (after ∅ s.mapPrefix) G₀ (WW G₀)).bits := by
  unfold c
  rw [ctx_pack,(tails_pack distance loc F Q₀ v z b n q precision k s H₀ G₀ T₀ U₀ hT hU).2.2.1,W_pack distance loc F Q₀ v z b n q precision k s G₀ U₀ hU]
  exact BinaryCross.finalCount_pack ..
lemma crossInput_pack (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
    (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : crossInput xx=BinaryFiniteCross.pack
      (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (after ∅ s.mapPrefix) v ((1+v^2)^q) s.lam')
      (3*q) (3*q+1) k n q H₀ G₀ T₀ (WW G₀) := by
  obtain ⟨hh,ht,hg,_⟩:=tails_pack distance loc F Q₀ v z b n q precision k s H₀ G₀ T₀ U₀ hT hU
  obtain ⟨hk,hs,_⟩:=keys_pack distance loc F Q₀ v z b n q precision k s
  simp only [crossInput,base_pack,hk,hs,hh,ht,hg,W_pack distance loc F Q₀ v z b n q precision k s G₀ U₀ hU]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFiniteCross.pack]
lemma finishInput_pack (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
    (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : finishInput xx=encode
      [setBits s.mapFree,BinaryRational.encode s.lam',historyBits (s.mapPrefix++[G₀]),historyBits (WW G₀)] := by
  obtain ⟨_,_,hg,_⟩:=tails_pack distance loc F Q₀ v z b n q precision k s H₀ G₀ T₀ U₀ hT hU
  obtain ⟨hb,hp⟩:=mapped_pack distance loc F Q₀ v z b n q precision k s
  simp only [finishInput,prefixG,hb,hp,hg,W_pack distance loc F Q₀ v z b n q precision k s G₀ U₀ hU,sf_pack]
  simp only [stateBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [BinaryCoupled.historyBits_append,BinaryCoupled.historyBits_cons]
  rfl
lemma advanceInput_pack (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
    (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : advanceInput xx=encode
      [stateBits s,labels G₀,historyBits (WW G₀),historyBits U₀] := by
  obtain ⟨_,_,hg,hu⟩:=tails_pack distance loc F Q₀ v z b n q precision k s H₀ G₀ T₀ U₀ hT hU
  simp only [advanceInput,hg,hu,W_pack distance loc F Q₀ v z b n q precision k s G₀ U₀ hU]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma fallbackInput_pack : fallbackInput xx=encode [setBits s.B,BinaryRational.encode s.lam,historyBits s.P,historyBits (m:=m) []] := by
  simp only [fallbackInput,sf_pack]
  simp only [stateBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open PhaseSequence PhaseMergeCompletion PhaseMergeInvariant PhaseCoupledMerge PhaseMergeRefinement CanonicalMergeCrossing
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma cross_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (Q₀ : Finset (Label (Fin m))) (v z b : ℚ) (n q precision k : ℕ) (s : State (Fin m))
    (eta lo hi : ℝ) (h : Certified loc F v eta lo hi q (n+1) k s)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m)))) (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) :
    BinaryFiniteCross.run (crossInput (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q b precision k s))=
      BinaryCross.resultBits (FiniteLabelCrossing.run (fun j=>original (loc j)) (rows distance) (F.image original)
        (after ∅ s.mapPrefix) v s.lam' q n k (copy (3*q)) (copy (3*q+1)) H₀ G₀ T₀
        (FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance) (F.image original)
          v s.lam' (q+1) n (after ∅ s.mapPrefix∪G₀.toFinset))) := by
  rw [crossInput_pack distance loc F Q₀ v z b n q precision k s H₀ G₀ T₀ U₀ hT hU]
  have hTr:=h.new_tail
  rw [hT] at hTr
  obtain ⟨hH,hHr,_⟩:=Runs.cons_iff.mp hTr
  have hUr:=h.old_tail
  rw [hU] at hUr
  obtain ⟨_,hGr,_⟩:=Runs.cons_iff.mp hUr
  have hG:=aligned_phase h hv hv1 hlo G₀ U₀ hU
  have hdis:=disjoint_map h.disjoint h.inj h.fixed
  have hp:=h.new_prefix
  have hcopy : ∀ i∈F.image original,copy (3*q) i∉F.image original∪s.mapFree := by
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    exact fresh F s.mapFree (3*q) h.before_map i 0
  have hdist : ∀ i∈F.image original,∀ j,dist (original (loc j)) i=dist (original (loc j)) (copy (3*q) i) := by
    intro x hx j
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist,copy_dist]
  have hz : (((1+v^2)^q:ℚ):ℝ)=(1+(v:ℝ)^2)^q := by push_cast; rfl
  have hc:=FiniteLabelContinuation.correct_completion (fun j=>original (loc j)) (rows distance)
    (rows_spec loc distance hmetric) (F.image original) v ((1+v^2)^q) s.lam' hv hv1 (by rw [hz]; positivity)
  exact BinaryFiniteCross.run_pack distance (fun j=>original (loc j)) (F.image original) s.mapFree
    (after ∅ s.mapPrefix) v s.lam' eta (3*q) (3*q+1) k n q hc hv hv1
    ((hlo.trans_le h.low).trans_le h.price) heta hp.after_subset hdis hp.row hcopy hdist H₀ G₀ T₀ _ hHr hGr
    ⟨PhaseMergeSurgery.prefix_exact_eta hH.1 heta,hH.2⟩ hG
lemma run_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (Q₀ : Finset (Label (Fin m))) (v z M : ℚ) (N n q precision k : ℕ) (s : State (Fin m))
    (eta lo hi : ℝ) (h : Certified loc F v eta lo hi q (n+1) k s)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q (20*N*M) precision k s)=
      outcomeBits (CanonicalCoupledMerge.step loc distance F v M N precision q n k s) := by
  obtain ⟨H₀,T₀,hT⟩ : ∃ H T,s.T=H::T := by
    cases ht : s.T with
    | nil=>have hh:=h.new_tail.1; rw [ht] at hh; simp only [List.length_nil] at hh; omega
    | cons H T=>exact ⟨H,T,rfl⟩
  obtain ⟨G₀,U₀,hU⟩ : ∃ G U,s.U=G::U := by
    cases ht : s.U with
    | nil=>have hh:=h.old_tail.1; rw [ht] at hh; simp only [List.length_nil] at hh; omega
    | cons G U=>exact ⟨G,U,rfl⟩
  let x:=pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q (20*N*M) precision k s
  have hne : nonempty x=true := by
    simp only [nonempty,x,sf_pack,stateBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      hT,hU,BinaryCoupled.historyBits_cons,cons_ne_nil,decide_false,Bool.not_false,Bool.true_and]
  have hc:=c_pack distance loc F Q₀ v z (20*N*M) n q precision k s H₀ G₀ T₀ U₀ hT hU
  have ha:=a_pack distance loc F Q₀ v z (20*N*M) n q precision k s
  have hkey : field 5 x=k.bits := by simp only [x,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hs : sandwiched x=decide (PhaseCountCrossing.Sandwich k (s.a F)
      (CanonicalMergeCrossing.finalCount (F.image original) (after ∅ s.mapPrefix) G₀
        (FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance) (F.image original)
          v s.lam' (q+1) n (after ∅ s.mapPrefix∪G₀.toFinset)))) := by
    apply Bool.eq_iff_iff.mpr
    simp only [sandwiched,show a x=_ from ha,show c x=_ from hc,hkey,value_bits,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    rfl
  have hcross:=cross_pack distance loc hmetric F Q₀ v z (20*N*M) n q precision k s eta lo hi h hv hv1 hlo heta H₀ G₀ T₀ U₀ hT hU
  have hr : resolveInput x=BinaryResolve.pack
      (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (after ∅ s.mapPrefix) v ((1+v^2)^q) s.lam')
      n q (3*q+2) (20*N*M) k precision (CanonicalCoupledMerge.banks F s.mapFree q) s.mapPrefix
      (FiniteLabelCrossing.run (fun j=>original (loc j)) (rows distance) (F.image original)
        (after ∅ s.mapPrefix) v s.lam' q n k (copy (3*q)) (copy (3*q+1)) H₀ G₀ T₀
        (FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance) (F.image original)
          v s.lam' (q+1) n (after ∅ s.mapPrefix∪G₀.toFinset))) := by
    simp only [resolveInput,Function.comp_apply,x]
    simp only [base_pack,(keys_pack distance loc F Q₀ v z (20*N*M) n q precision k s).2.2,
      banks_pack,(mapped_pack distance loc F Q₀ v z (20*N*M) n q precision k s).2,hcross,
      ]
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryResolve.pack]
  change run x=_
  simp only [run,hne,ite_true,active]
  rw [show c x=_ from hc,hkey,hs,hr]
  simp only [value_bits,decide_eq_true_eq]
  rw [BinaryResolve.run_pack]
  simp only [CanonicalCoupledMerge.step,hT,hU]
  split_ifs
  · rw [show finishInput x=_ from finishInput_pack distance loc F Q₀ v z (20*N*M) n q precision k s H₀ G₀ T₀ U₀ hT hU,BinaryCoupled.finish_pack]
    rfl
  · rfl
  · rw [show advanceInput x=_ from advanceInput_pack distance loc F Q₀ v z (20*N*M) n q precision k s H₀ G₀ T₀ U₀ hT hU,BinaryCoupled.advance_pack]
    rfl
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
