import Mathlib
import OAI.Probability.ParisiFinite.PacketLabel

namespace OAI

/-! Shape. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin
namespace CausalStage
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

 

structure Shape (s : CausalStage b n κ) (q : ControlSignature) : Prop where
  word : TraceWord.forget s.trace=q.word
  causal : q.Causal n
  centers : ∀i,combination (fun j => (s.frame.frame.formal j : SeededTree.Level n))
    (s.coefficients i)=q.center b n i

theorem visibility_shape (s : CausalStage b n κ) (q : ControlSignature)
    (hs : s.Shape q) (i : PacketLabel) :
    s.frame.frame.visibility s.trace (s.coefficients i) Z=q.visibility b n i := by
  unfold CausalFrame.visibility CausalFrame.centerModel
  rw [s.frame.op_model s.trace s.valid,hs.word,hs.centers i,q.center_step b n hs.causal i]
  change q.visibility b (n+1) i=q.visibility b n i
  exact q.visibility_step b n hs.causal i

theorem visible_shape (s : CausalStage b n κ) (q : ControlSignature)
    (hs : s.Shape q) (hv : q.Visible b n) : s.visible := by
  intro i
  rw [s.visibility_shape q hs i]
  exact hv i

theorem record_formal (s : CausalStage b n κ) (hb : 0<b) :
    (fun j => ((s.record hb).frame.frame.formal j : SeededTree.Level (n+1)))=
      Sum.elim (fun j => (SeededTree.empty n).toLinearIsometry (s.frame.frame.formal j : SeededTree.Level n))
      (fun _ : Unit => ((SeededTree.circuit (TraceWord.forget s.trace) (n+1)).insertion : SeededTree.Level (n+1))) := by
  funext j
  cases j <;> rfl

theorem record_combination (s : CausalStage b n κ) (hb : 0<b) (c : κ → ℂ) :
    combination (fun j => ((s.record hb).frame.frame.formal j : SeededTree.Level (n+1)))
      (Sum.elim c 0)= (SeededTree.empty n).toLinearIsometry
        (combination (fun j => (s.frame.frame.formal j : SeededTree.Level n)) c) := by
  rw [s.record_formal hb,combination_sum_zero]
  simp only [combination,map_sum,map_smul]

theorem shape_record (s : CausalStage b n κ) (hb : 0<b) (q : ControlSignature)
    (hs : s.Shape q) : (s.record hb).Shape q where
  word := by simpa only [record,TraceWord.forget_reindex] using hs.word
  causal := q.causal_succ hs.causal
  centers i := by
    change combination (fun j => ((s.record hb).frame.frame.formal j : SeededTree.Level (n+1)))
      (Sum.elim (s.coefficients i) 0)=_
    rw [s.record_combination hb,hs.centers i,q.center_step b n hs.causal i]

theorem shape_initial (b : ℝ) (hb : 0<b) : ((initial b hb) : CausalStage b 2 (PEmpty.{1} ⊕ Unit)).Shape (ControlSignature.initial b) where
  word := rfl
  causal := ⟨by rfl,by simp [ControlSignature.initial]⟩
  centers i := by
    change combination (Sum.elim PEmpty.elim.{_,1}
      (fun _ : Unit => ((SeededTree.circuit [] 2).insertion : SeededTree.Level 2)))
      (Sum.elim PEmpty.elim.{_,1} (fun _ => initialCoefficient b i))=_
    simp only [combination,Fintype.sum_sum_type,Fintype.sum_empty,zero_add,Fintype.sum_unique,
      Sum.elim_inr,ControlSignature.center,ControlSignature.initial,ControlSignature.centerTail,add_zero]

theorem shape_cost (s : CausalStage b n κ) (hb : 0<b) (q : ControlSignature)
    (hs : s.Shape q) (a : ℝ) : (s.cost hb a).Shape (q.cost a) where
  word := by
    change .cost a::TraceWord.forget (s.trace.map (TraceGate.reindex Sum.inl))=_
    rw [TraceWord.forget_reindex,hs.word]
    rfl
  causal := q.causal_cost hs.causal a
  centers i := (s.shape_record hb q hs).centers i

theorem record_echo_combination (s : CausalStage b n κ) (hb : 0<b) (t : ℝ) (i : PacketLabel) :
    combination (fun j => ((s.record hb).frame.frame.formal j : SeededTree.Level (n+1)))
      (s.echoCoefficients t i)= (SeededTree.empty n).toLinearIsometry
        (combination (fun j => (s.frame.frame.formal j : SeededTree.Level n)) (s.coefficients i)) +
      echoCoefficient t i • ((SeededTree.circuit (TraceWord.forget s.trace) (n+1)).insertion : SeededTree.Level (n+1)) := by
  rw [s.record_formal hb]
  simp only [echoCoefficients,combination,Fintype.sum_sum_type,Fintype.sum_unique,Sum.elim_inl,Sum.elim_inr,
    map_sum,map_smul]

theorem echo_center_shape (s : CausalStage b n κ) (hb : 0<b) (q : ControlSignature)
    (hs : s.Shape q) (t : ℝ) (i : PacketLabel) :
    combination (fun j => ((s.record hb).frame.frame.formal j : SeededTree.Level (n+1)))
      (s.echoCoefficients t i)=(q.echo t).center b (n+1) i := by
  rw [s.record_echo_combination hb t i,hs.centers i,q.center_step b n hs.causal i,hs.word]
  simp only [ControlSignature.center,ControlSignature.echo,ControlSignature.centerTail]
  abel

theorem echo_visible_shape (s : CausalStage b n κ) (hb : 0<b) (q : ControlSignature)
    (hs : s.Shape q) (t : ℝ) (hv : (q.echo t).Visible b (n+1)) : s.echoVisible hb t := by
  intro i
  unfold CausalFrame.visibility CausalFrame.centerModel
  have hvalid : TraceWord.Valid (s.record hb).frame.history (s.echoTrace t) := (s.record hb).valid
  rw [(s.record hb).frame.op_model (s.echoTrace t) hvalid,s.echo_center_shape hb q hs t i]
  have hw : TraceWord.forget (s.echoTrace t)=(q.echo t).word := by
    simp only [echoTrace,TraceWord.forget, List.map_cons, TraceGate.forget]
    change .seed (echoAngles t)::TraceWord.forget (s.trace.map (TraceGate.reindex Sum.inl))=_
    rw [TraceWord.forget_reindex,hs.word]
    rfl
  rw [hw,(q.echo t).center_step b (n+1) (q.causal_echo hs.causal t) i]
  change (q.echo t).visibility b (n+2) i≠0
  rw [(q.echo t).visibility_step b (n+1) (q.causal_echo hs.causal t) i]
  exact hv i

theorem exists_shaped_mixer (s : CausalStage b n κ) (hb : 0<b) (q : ControlSignature)
    (hs : s.Shape q) (a : ℝ) (hv : q.Visible b n) :
    ∃s' : CausalStage b (n+1) (κ ⊕ Unit),s'.Shape (q.mixer a) := by
  obtain ⟨K,c,s',htrace,hword,hcent,hcoeff,hframe⟩ := s.exists_mixer hb a (s.visible_shape q hs hv)
  refine ⟨s',?_,q.causal_mixer hs.causal a,?_⟩
  · rw [htrace]
    change .mixer a::TraceWord.forget (s.trace.map (TraceGate.reindex Sum.inl))=_
    rw [TraceWord.forget_reindex,hs.word]
    rfl
  · intro i
    rw [hframe,hcoeff i]
    exact (s.shape_record hb q hs).centers i

theorem exists_shaped_echo (s : CausalStage b n κ) (hb : 0<b) (q : ControlSignature)
    (hs : s.Shape q) (t : ℝ) (ht : t≠0) (hv : q.Visible b n)
    (hv' : (q.echo t).Visible b (n+1)) :
    ∃s' : CausalStage b (n+1) (κ ⊕ Unit),s'.Shape (q.echo t) := by
  obtain ⟨K,L,a,c,s',htrace,hword,hcent,hcoeff,hframe⟩ := s.exists_echo hb t ht
    (s.visible_shape q hs hv) (s.echo_visible_shape hb q hs t hv')
  refine ⟨s',?_,q.causal_echo hs.causal t,?_⟩
  · rw [htrace]
    change .seed (echoAngles t)::TraceWord.forget (s.trace.map (TraceGate.reindex Sum.inl))=_
    rw [TraceWord.forget_reindex,hs.word]
    rfl
  · intro i
    rw [hframe,hcoeff]
    exact s.echo_center_shape hb q hs t i

end CausalStage
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin

namespace IndexedControl
open SeededTree
variable {M : ℕ}

def depth : List (IndexedGate M) → ℕ
  | [] => 2
  | _::w => depth w+1

def History : List (IndexedGate M) → Type
  | [] => PEmpty ⊕ Unit
  | _::w => History w ⊕ Unit

instance historyFintype : (w : List (IndexedGate M)) → Fintype (History w)
  | [] => inferInstanceAs (Fintype (PEmpty ⊕ Unit))
  | _::w => @instFintypeSum (History w) Unit (historyFintype w) inferInstance

def signature (b : ℝ) (x : Fin M → ℝ) : List (IndexedGate M) → ControlSignature
  | [] => .initial b
  | .mixer i::w => (signature b x w).mixer (x i)
  | .cost i::w => (signature b x w).cost (x i)
  | .seed i::w => (signature b x w).echo (indexedTime i x)

theorem depth_eq (w : List (IndexedGate M)) : depth w=w.length+2 := by
  induction w with
  | nil => rfl
  | cons g w ih => simp only [depth,List.length_cons,ih]

theorem signature_causal (b : ℝ) (x : Fin M → ℝ) (w : List (IndexedGate M)) :
    (signature b x w).Causal (depth w) := by
  induction w with
  | nil => exact ⟨by rfl,by simp [signature,ControlSignature.initial]⟩
  | cons g w ih =>
    cases g with
    | mixer i => exact (signature b x w).causal_mixer ih (x i)
    | cost i => exact (signature b x w).causal_cost ih (x i)
    | seed i => exact (signature b x w).causal_echo ih (indexedTime i x)

theorem signature_word (b : ℝ) (x : Fin M → ℝ) (w : List (IndexedGate M)) :
    (signature b x w).word=SeededTree.evalWord (indexedWord w++initializationParam b) x := by
  induction w with
  | nil => simp [signature,ControlSignature.initial,indexedWord,eval_initializationParam]
  | cons g w ih =>
    cases g with
    | mixer i => simpa only [signature,ControlSignature.mixer,indexedWord,List.map_cons,
        List.cons_append,SeededTree.evalWord,List.map_cons,IndexedGate.param,SeededTree.ParamGate.eval] using congrArg (List.cons (.mixer (x i))) ih
    | cost i => simpa only [signature,ControlSignature.cost,indexedWord,List.map_cons,
        List.cons_append,SeededTree.evalWord,List.map_cons,IndexedGate.param,SeededTree.ParamGate.eval] using congrArg (List.cons (.cost (x i))) ih
    | seed i =>
      have he : CausalStage.echoAngles (indexedTime i x)=(fun q : Fin 2 => if q=0 then 0 else x i) := by
        funext q
        unfold CausalStage.echoAngles indexedTime
        split_ifs <;> ring
      simpa only [signature,ControlSignature.echo,he,indexedWord,List.map_cons,
        List.cons_append,SeededTree.evalWord,List.map_cons,IndexedGate.param,SeededTree.ParamGate.eval] using
        congrArg (List.cons (.seed (fun q : Fin 2 => if q=0 then 0 else x i))) ih

def nonzero (x : Fin M → ℝ) : IndexedGate M → Prop
  | .seed i => indexedTime i x≠0
  | _ => True

def Admissible (b : ℝ) (x : Fin M → ℝ) : List (IndexedGate M) → Prop
  | [] => (signature b x []).Visible b (depth (M:=M) [])
  | g::w => Admissible b x w ∧ (signature b x (g::w)).Visible b (depth (g::w)) ∧ nonzero x g

theorem Admissible.visible {b : ℝ} {x : Fin M → ℝ} {w : List (IndexedGate M)}
    (h : Admissible b x w) : (signature b x w).Visible b (depth w) := by
  cases w with
  | nil => exact h
  | cons g w => exact h.2.1

 

theorem compile (b : ℝ) (hb : 0<b) (x : Fin M → ℝ) (w : List (IndexedGate M))
    (hw : Admissible b x w) :
    ∃s : CausalStage b (depth w) (History w),s.Shape (signature b x w) := by
  induction w with
  | nil => exact ⟨CausalStage.initial b hb,CausalStage.shape_initial b hb⟩
  | cons g w ih =>
    obtain ⟨s,hs⟩ := ih hw.1
    cases g with
    | mixer i => exact s.exists_shaped_mixer hb _ hs (x i) hw.1.visible
    | cost i => exact ⟨s.cost hb (x i),s.shape_cost hb _ hs (x i)⟩
    | seed i => exact s.exists_shaped_echo hb _ hs (indexedTime i x) hw.2.2 hw.1.visible hw.2.1

theorem exists_word_close (b : ℝ) (hb : 0<b) (x : Fin M → ℝ) (w : List (IndexedGate M))
    (hw : Admissible b x w) {ε : ℝ} (hε : 0<ε) :
    ∃v : List PointedTree.Gate,
      |ordinaryValue v-SeededTree.value (SeededTree.evalWord (indexedWord w++initializationParam b) x)|<ε := by
  obtain ⟨s,hs⟩ := compile b hb x w hw
  obtain ⟨v,hv⟩ := s.exists_word_close hb hε
  rw [hs.word,signature_word b x w] at hv
  exact ⟨v,hv⟩

end IndexedControl
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin

namespace ControlSignature

theorem center_echo (q : ControlSignature) (b t : ℝ) (n : ℕ) (i : PacketLabel) :
    (q.echo t).center b n i=q.center b n i+
      CausalStage.echoCoefficient t i • ((SeededTree.circuit q.word n).insertion : SeededTree.Level n) := by
  simp only [echo,center,centerTail]
  abel

theorem visibility_stable (q : ControlSignature) (b : ℝ) {n N : ℕ}
    (hq : q.Causal n) (hN : n≤N) (i : PacketLabel) : q.visibility b N i=q.visibility b n i := by
  induction N,hN using Nat.le_induction with
  | base => rfl
  | @succ N hN ih =>
    have hc : q.Causal N := ⟨hq.1.trans hN,fun p hp => (hq.2 p hp).trans hN⟩
    rw [q.visibility_step b N hc i,ih]

end ControlSignature

namespace IndexedControl
open SeededTree
variable {M : ℕ}

theorem echoCoefficient_half (i : PacketLabel) (j : Fin M) (x : Fin M → ℝ) :
    CausalStage.echoCoefficient (indexedTime j x) i=if i.2=0 then -(x j:ℂ) else (x j:ℂ) := by
  unfold CausalStage.echoCoefficient indexedTime
  split_ifs <;> push_cast <;> ring

theorem echoCoefficient_analytic (i : PacketLabel) (j : Fin M) (x : Fin M → ℝ) :
    AnalyticAt ℝ (fun u => CausalStage.echoCoefficient (indexedTime j u) i) x := by
  simp only [echoCoefficient_half]
  have h := (Complex.ofRealCLM.analyticAt _).comp
    ((ContinuousLinearMap.proj j : (Fin M → ℝ) →L[ℝ] ℝ).analyticAt x)
  split_ifs
  · exact h.neg
  · exact h

theorem signature_insertion_regular (b : ℝ) (w : List (IndexedGate M)) (n : ℕ)
    (x : Fin M → ℝ) :
    PacketRegular x n (fun u => ((circuit (signature b u w).word n).insertion : SeededTree.Level n)) := by
  simp only [signature_word]
  apply circuit_insertion_packetRegular
  intro g hg
  rcases List.mem_append.mp hg with hg|hg
  · exact indexedWord_regular w x g hg
  · exact initializationParam_regular b x g hg

theorem center_regular (b : ℝ) (w : List (IndexedGate M)) (n : ℕ)
    (i : PacketLabel) (x : Fin M → ℝ) :
    PacketRegular x n (fun u => (signature b u w).center b n i) := by
  induction w with
  | nil =>
    have he : PacketRegular x n (fun _ : Fin M → ℝ => ((circuit [] n).insertion : SeededTree.Level n)) :=
      circuit_insertion_packetRegular [] (by simp) n
    simpa only [signature,ControlSignature.initial,ControlSignature.center,
      ControlSignature.centerTail,add_zero] using
      PacketRegular.smul n (z := fun _ : Fin M → ℝ => CausalStage.initialCoefficient b i) analyticAt_const he
  | cons g w ih =>
    cases g with
    | mixer j => exact ih
    | cost j => exact ih
    | seed j =>
      simp only [signature,ControlSignature.center_echo]
      exact PacketRegular.add n ih (PacketRegular.smul n (echoCoefficient_analytic i j x)
        (signature_insertion_regular b w n x))

theorem visibility_analytic (b : ℝ) (w : List (IndexedGate M)) (n : ℕ)
    (i : PacketLabel) (x : Fin M → ℝ) :
    AnalyticAt ℝ (fun u => (signature b u w).visibility b n i) x := by
  have h := PacketRegular.inner n (signature_insertion_regular b w n x) (center_regular b w n i x)
  exact (show AnalyticAt ℝ (fun _ : Fin M → ℝ => (-2:ℝ)) x from analyticAt_const).mul
    ((Complex.imCLM.analyticAt _).comp h)

theorem center_zero (b : ℝ) (w : List (IndexedGate M)) (n : ℕ) (i : PacketLabel) :
    (signature b 0 w).center b n i=CausalStage.initialCoefficient b i •
      ((circuit [] n).insertion : SeededTree.Level n) := by
  induction w with
  | nil => simp [signature,ControlSignature.initial,ControlSignature.center,ControlSignature.centerTail]
  | cons g w ih =>
    cases g with
    | mixer j => exact ih
    | cost j => exact ih
    | seed j => simpa only [signature,ControlSignature.center_echo,echoCoefficient_half,Pi.zero_apply,
        Complex.ofReal_zero,neg_zero,ite_self,zero_smul,add_zero] using ih

def sign (i : Fin 2) : ℝ := if i=0 then 1 else -1

theorem sign_ne_zero (i : Fin 2) : sign i≠0 := by
  unfold sign
  split_ifs <;> norm_num

theorem visibility_zero (b : ℝ) (w : List (IndexedGate M)) (n : ℕ) (i : PacketLabel) :
    (signature b 0 w).visibility b n i=4*b*sign i.1*Real.exp (-8*b^2) := by
  unfold ControlSignature.visibility
  rw [center_zero,signature_word,evalWord_append,eval_initializationParam,
    circuit_zero_prefix _ _ (indexedWord_zero w),inner_smul_right]
  have he : ⟪((circuit (initializationWord b) n).insertion : SeededTree.Level n),
      ((circuit [] n).insertion : SeededTree.Level n)⟫_ℂ=Complex.I*(Real.exp (-8*b^2):ℂ) :=
    inner_initialization_initial n b
  rw [he]
  unfold CausalStage.initialCoefficient sign
  split_ifs <;> simp only [Complex.mul_im,Complex.mul_re,Complex.I_im,Complex.I_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,mul_zero,zero_mul,
    zero_add] <;> norm_num <;> ring

theorem visibility_zero_ne (b : ℝ) (hb : 0<b) (w : List (IndexedGate M)) (n : ℕ) (i : PacketLabel) :
    (signature b 0 w).visibility b n i≠0 := by
  rw [visibility_zero]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hb)) (sign_ne_zero _))
    (ne_of_gt (Real.exp_pos _))

end IndexedControl
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin
namespace IndexedControl
open SeededTree
variable {M : ℕ}

 

def stages : List (IndexedGate M) → List (List (IndexedGate M))
  | [] => [[]]
  | g::w => (g::w)::stages w

theorem mem_stages_self (w : List (IndexedGate M)) : w∈stages w := by
  cases w <;> exact List.mem_cons_self

theorem admissible_of_stages (b : ℝ) (x : Fin M → ℝ) (w : List (IndexedGate M))
    (hv : ∀u∈stages w,(signature b x u).Visible b (depth u))
    (hn : ∀i,x i≠0) : Admissible b x w := by
  induction w with
  | nil => exact hv [] (mem_stages_self [])
  | cons g w ih =>
    refine ⟨ih (fun u hu => hv u (List.mem_cons_of_mem _ hu)),hv (g::w) (mem_stages_self _),?_⟩
    cases g with
    | mixer i => trivial
    | cost i => trivial
    | seed i => exact div_ne_zero (hn i) (by norm_num)

 

theorem exists_admissible (b : ℝ) (hb : 0<b) (w : List (IndexedGate M)) (x : Fin M → ℝ)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) :
    ∃u : Fin M → ℝ,dist u x<δ ∧
      |SeededTree.value (SeededTree.evalWord (indexedWord w++initializationParam b) u)-
        SeededTree.value (SeededTree.evalWord (indexedWord w++initializationParam b) x)|<ε ∧
      Admissible b u w := by
  classical
  let I := (Fin (stages w).length × PacketLabel) ⊕ Fin M
  let f : I → (Fin M → ℝ) → ℝ := fun j =>
    match j with
    | .inl (k,i) => fun u => (signature b u ((stages w).get k)).visibility b (depth ((stages w).get k)) i
    | .inr k => fun u => u k
  have hf : ∀j,AnalyticOnNhd ℝ (f j) Set.univ := by
    intro j u hu
    cases j with
    | inl p => exact visibility_analytic b ((stages w).get p.1) _ p.2 u
    | inr k => exact (ContinuousLinearMap.proj k : (Fin M → ℝ) →L[ℝ] ℝ).analyticAt u
  have hn : ∀j,∃u,f j u≠0 := by
    intro j
    cases j with
    | inl p => exact ⟨0,visibility_zero_ne b hb ((stages w).get p.1) _ p.2⟩
    | inr k => exact ⟨fun _ => 1,by norm_num [f]⟩
  have he : ContinuousAt (fun u => SeededTree.value
      (SeededTree.evalWord (indexedWord w++initializationParam b) u)) x := by
    apply (analyticAt_value _ _).continuousAt
    intro g hg
    rcases List.mem_append.mp hg with hg|hg
    · exact indexedWord_regular w x g hg
    · exact initializationParam_regular b x g hg
  obtain ⟨u,hu,he,hf⟩ := AnalyticVisibility.exists_perturbation f hf hn _ x he hε hδ
  refine ⟨u,hu,he,admissible_of_stages b u w ?_ (fun i => hf (.inr i))⟩
  intro v hv i
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hv
  simpa only [f,hk] using hf (.inl (k,i))

 

theorem exists_ordinary_approx (b : ℝ) (hb : 0<b) (w : List (IndexedGate M)) (x : Fin M → ℝ)
    {ε : ℝ} (hε : 0<ε) :
    ∃v : List PointedTree.Gate,
      |ordinaryValue v-SeededTree.value (SeededTree.evalWord (indexedWord w++initializationParam b) x)|<ε := by
  obtain ⟨u,hu,he,hw⟩ := exists_admissible b hb w x (half_pos hε) (show (0:ℝ)<1 by norm_num)
  obtain ⟨v,hv⟩ := exists_word_close b hb u w hw (half_pos hε)
  refine ⟨v,?_⟩
  have hh := abs_sub_le (ordinaryValue v)
    (SeededTree.value (SeededTree.evalWord (indexedWord w++initializationParam b) u))
    (SeededTree.value (SeededTree.evalWord (indexedWord w++initializationParam b) x))
  linarith

end IndexedControl
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeededTree
open CoherentFock PointedTree RootSpin

 

theorem circuit_suffix_congr (w u v : List SeededTree.Gate)
    (hu : ∀n,circuit u n=circuit v n) (n : ℕ) : circuit (w++u) n=circuit (w++v) n := by
  induction w generalizing n with
  | nil => exact hu n
  | cons g w ih =>
    cases g with
    | mixer a => exact congrArg (fun U => U.followedBy (EvenUnitary.mixer n a)) (ih n)
    | seed a => exact congrArg (fun U => U.followedBy (EvenUnitary.seed n a)) (ih n)
    | cost a =>
      cases n with
      | zero => exact ih 0
      | succ n =>
        change (circuit (w++u) (n+1)).followedBy (EvenUnitary.cost n (circuit (w++u) n) a)=_
        rw [ih (n+1),ih n]
        rfl

theorem value_congr_circuit (w u : List SeededTree.Gate) (h : ∀n,circuit w n=circuit u n) : value w=value u := by
  rw [value_eq_height w (w.length+u.length) (Nat.le_add_right _ _),
    value_eq_height u (w.length+u.length) (Nat.le_add_left _ _),h]

def cancelInitialization (b : ℝ) : List SeededTree.Gate :=
  .mixer (-Real.pi/4)::initializationWord b

theorem cancelInitialization_zero (n : ℕ) : circuit (cancelInitialization 0) n=EvenUnitary.ident n := by
  have ha : initializationAngles 0=fun _ => 0 := by funext q; simp [initializationAngles]
  unfold cancelInitialization initializationWord
  rw [ha]
  simp only [circuit,EvenUnitary.seed_zero,EvenUnitary.followedBy_ident]
  apply EvenUnitary.ext
  apply LinearIsometryEquiv.ext
  intro v
  change SpinOperators.act (R (-Real.pi/4)) (SpinOperators.act (R (Real.pi/4)) v)=v
  change ((SpinOperators.act (R (-Real.pi/4))).comp (SpinOperators.act (R (Real.pi/4)))) v=v
  rw [←SpinOperators.act_mul,R_add,show -Real.pi/4+Real.pi/4=0 by ring,R_zero,SpinOperators.act_one]
  rfl

theorem value_cancelInitialization_zero (w : List SeededTree.Gate) :
    value (w++cancelInitialization 0)=value w := by
  apply value_congr_circuit
  intro n
  simpa only [List.append_nil] using circuit_suffix_congr w (cancelInitialization 0) [] cancelInitialization_zero n

def constantGate : SeededTree.Gate → SeededTree.ParamGate ℝ
  | .mixer a => .mixer (fun _ => a)
  | .cost a => .cost (fun _ => a)
  | .seed a => .seed (fun q _ => a q)

theorem constantGate_eval (g : SeededTree.Gate) (b : ℝ) : (constantGate g).eval b=g := by cases g <;> rfl

theorem constantGate_regular (g : SeededTree.Gate) (b : ℝ) : (constantGate g).regular b := by
  cases g with
  | mixer a => exact analyticAt_const
  | cost a => exact analyticAt_const
  | seed a => exact fun _ => analyticAt_const

def initializationCurve (w : List SeededTree.Gate) : List (SeededTree.ParamGate ℝ) :=
  w.map constantGate++[.mixer (fun _ => -Real.pi/4),.mixer (fun _ => Real.pi/4),
    .seed (fun q b => if q=0 then -2*b else 0)]

theorem initializationCurve_eval (w : List SeededTree.Gate) (b : ℝ) :
    SeededTree.evalWord (initializationCurve w) b=w++cancelInitialization b := by
  unfold initializationCurve
  rw [evalWord_append]
  have hm : SeededTree.evalWord (w.map constantGate) b=w := by
    simp only [SeededTree.evalWord,List.map_map,Function.comp_def,constantGate_eval]
    exact List.map_id w
  rw [hm]
  rfl

theorem initializationCurve_regular (w : List SeededTree.Gate) (b : ℝ) :
    ∀g∈initializationCurve w,g.regular b := by
  intro g hg
  rcases List.mem_append.mp hg with hg|hg
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hg
    exact constantGate_regular g b
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl
    · exact analyticAt_const
    · exact analyticAt_const
    · intro q
      change AnalyticAt ℝ (fun b : ℝ => if q=0 then -2*b else 0) b
      split_ifs
      · exact (analyticAt_const.mul analyticAt_id)
      · exact analyticAt_const

 

theorem exists_small_initialization (w : List SeededTree.Gate) {ε : ℝ} (hε : 0<ε) :
    ∃b : ℝ,0<b ∧ |value (w++cancelInitialization b)-value w|<ε := by
  have hc : ContinuousAt (fun b => value (w++cancelInitialization b)) 0 := by
    simpa only [initializationCurve_eval] using
      (analyticAt_value (initializationCurve w) (initializationCurve_regular w 0)).continuousAt
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ/2,half_pos hδ,?_⟩
  have hd : dist (δ/2) (0:ℝ)<δ := by rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)]; linarith
  have h := hclose hd
  simpa only [value_cancelInitialization_zero,Real.dist_eq] using h

end SeededTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin
namespace IndexedControl
open SeededTree
variable {M : ℕ}

def promote : IndexedGate M → IndexedGate (M+1)
  | .mixer i => .mixer i.castSucc
  | .cost i => .cost i.castSucc
  | .seed i => .seed i.castSucc

def extendedAngles (x : Fin M → ℝ) : Fin (M+1) → ℝ := Fin.lastCases (-Real.pi/4) x

def extendedWord (w : List (IndexedGate M)) : List (IndexedGate (M+1)) :=
  w.map promote++[.mixer (Fin.last M)]

theorem promote_eval (g : IndexedGate M) (x : Fin M → ℝ) :
    (promote g).param.eval (extendedAngles x)=g.param.eval x := by
  cases g <;> simp [promote,IndexedGate.param,SeededTree.ParamGate.eval,extendedAngles]

theorem promote_word_eval (w : List (IndexedGate M)) (x : Fin M → ℝ) :
    SeededTree.evalWord (indexedWord (w.map promote)) (extendedAngles x)=
      SeededTree.evalWord (indexedWord w) x := by
  simp only [indexedWord,SeededTree.evalWord,List.map_map,Function.comp_def,promote_eval]

theorem extended_initialized_eval (w : List (IndexedGate M)) (x : Fin M → ℝ) (b : ℝ) :
    SeededTree.evalWord (indexedWord (extendedWord w)++initializationParam b) (extendedAngles x)=
      SeededTree.evalWord (indexedWord w) x++cancelInitialization b := by
  rw [evalWord_append,eval_initializationParam]
  change SeededTree.evalWord (indexedWord (w.map promote++[.mixer (Fin.last M)])) (extendedAngles x)++_=_
  rw [show indexedWord (w.map promote++[.mixer (Fin.last M)])=
    indexedWord (w.map promote)++indexedWord [.mixer (Fin.last M)] from List.map_append,
    evalWord_append,promote_word_eval]
  simp only [indexedWord,SeededTree.evalWord,List.map_cons,List.map_nil,IndexedGate.param,
    SeededTree.ParamGate.eval,extendedAngles,Fin.lastCases_last,List.append_assoc,List.cons_append,
    List.nil_append,cancelInitialization]

 

theorem seed_removal (w : List (IndexedGate M)) (x : Fin M → ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃v : List PointedTree.Gate,
      |ordinaryValue v-SeededTree.value (SeededTree.evalWord (indexedWord w) x)|<ε := by
  obtain ⟨b,hb,he⟩ := exists_small_initialization (SeededTree.evalWord (indexedWord w) x) (half_pos hε)
  obtain ⟨v,hv⟩ := exists_ordinary_approx b hb (extendedWord w) (extendedAngles x) (half_pos hε)
  rw [extended_initialized_eval] at hv
  refine ⟨v,?_⟩
  have h := abs_sub_le (ordinaryValue v)
    (SeededTree.value (SeededTree.evalWord (indexedWord w) x++cancelInitialization b))
    (SeededTree.value (SeededTree.evalWord (indexedWord w) x))
  linarith

end IndexedControl
end SeedInitialization

end

end OAI
