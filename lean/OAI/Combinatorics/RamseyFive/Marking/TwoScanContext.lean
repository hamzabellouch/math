import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.MarkingClasses
import OAI.Combinatorics.RamseyFive.Entropy.ClassExtraction

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance scanContextDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
variable {K V κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N : ℕ}

omit [Finite K] in
theorem marking_posterior_domains (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) :
    ∀ x,0<fiber (withMessage p markingMessage) (c,m) x→
      ∀ i∈unspecified m,x i∈markingDomain m i := by
  intro x hx i hi
  obtain ⟨hp,he⟩:=fiber_withMessage_support p markingMessage c m hm x hx
  subst m
  exact marking_decodes hdim x (hf c x hp) (hc c x hp) i hi

lemma marking_posterior_cap (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) (i : Fin N) (hi : i∈unspecified m) :
    entropy (map (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i))≤
      Real.log (153*(Nat.card K:ℝ)^4) := by
  apply entropy_support_cap
  have hs : support (map (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i)) ⊆
      markingDomain m i := by
    intro z hz
    have hzpos : 0 < map (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i) z :=
      (mem_support _ _).mp hz
    obtain ⟨x,hx,rfl⟩:=map_positive (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i) z hzpos
    exact marking_posterior_domains hdim p hf hc c m hm x hx i hi
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (markingDomain_card hdim m i)

lemma marking_deficit_nonneg (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) :
    0≤activeDeficit (fiber (withMessage p markingMessage) (c,m)) (unspecified m)
      (Real.log (153*(Nat.card K:ℝ)^4)) := by
  have hfix := unionMessage_fixedOutside p twoScanTypes
    (fun x=>expensiveSet x (Nat.card K)) (fun x=>reverseExpensive x (Nat.card K)) c m hm
  have hh:=hfix.entropy_le_sum
  have hb : (∑ i∈unspecified m,entropy (map (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i)))≤
      ((unspecified m).card:ℝ)*Real.log (153*(Nat.card K:ℝ)^4) := by
    calc
      _ ≤ ∑ i∈unspecified m,Real.log (153*(Nat.card K:ℝ)^4) :=
        Finset.sum_le_sum fun i hi=>marking_posterior_cap hdim p hf hc c m hm i hi
      _ = _ := by simp
  exact sub_nonneg.mpr (hh.trans hb)

theorem marking_expected_deficit (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (S : κ→Fin N→Finset (FlagPair K V)) (cap J B L : ℝ) (hcap : 1≤cap)
    (hS : ∀ c i,((S c i).card:ℝ)≤cap)
    (hsupp : ∀ c x,0<p (c,x)→∀ i,x i∈S c i)
    (hΔ : 0≤Real.log cap-J) (hent : (N:ℝ)*J-entropy (second p)≤B)
    (hctx : entropy (first p)≤L) :
    mean (first (withMessage p markingMessage))
      (fun z=>activeDeficit (fiber (withMessage p markingMessage) z) (unspecified z.2) J)≤
      B+L+(N:ℝ)*Real.log 800+
      (800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))))*(Real.log cap-J) := by
  have hh:=union_deficit_bound p twoScanTypes (fun x=>expensiveSet x (Nat.card K))
    (fun x=>reverseExpensive x (Nat.card K)) S cap J hcap hS hsupp
  have hmean : mean (second p) (fun x=>((expensiveSet x (Nat.card K)∪reverseExpensive x (Nat.card K)).card:ℝ))≤
      800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))) := by
    apply (mean_mono_pos (second p) (g:=fun _=>_) _).trans_eq (mean_const _ _)
    intro x hx
    obtain ⟨c,_,hc'⟩:=Finset.sum_pos_iff_of_nonneg (fun c _=>p.nonneg (c,x)) |>.mp hx
    exact unionExpensive_bound hdim x (hc c x hc') _ (by
      exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  have hm:=mul_le_mul_of_nonneg_right hmean hΔ
  simp only [Fintype.card_fin] at hh
  exact hh.trans (by linarith)
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N l : ℕ}
local instance markedClassFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance markedClassPointDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance markedClassDualDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

def expensiveBound (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] : ℝ :=
  800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
    Real.log (1+Fintype.card (ℙ K V)))

omit [Finite K] in
lemma positive_marked_context (p : Law (κ×(Fin N→FlagPair K V)))
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) :
    ∃ x,0<p (c,x) ∧ markingMessage x=m := by
  obtain ⟨x,_,hx⟩:=Finset.sum_pos_iff_of_nonneg
    (fun x _=>(withMessage p markingMessage).nonneg ((c,m),x)) |>.mp hm
  exact ⟨x,withMessage_support p markingMessage c m x hx⟩

lemma marked_cheap_count (hdim : finrank K V=5) (p : Law (κ×(Fin N→FlagPair K V)))
    (hcons : ∀ c x,0<p (c,x)→TupleConsistent x)
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) :
    (N:ℝ)-expensiveBound K V≤(unspecified m).card := by
  obtain ⟨x,hx,rfl⟩:=positive_marked_context p c m hm
  have hcard:=unspecified_card twoScanTypes (fun x=>expensiveSet x (Nat.card K))
    (fun x=>reverseExpensive x (Nat.card K)) x
  have hex:=unionExpensive_bound hdim x (hcons c x hx) (Nat.card K)
    (by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  simp only [Fintype.card_fin] at hcard
  unfold markingMessage expensiveBound
  linarith

def markedCode (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (c : κ×UnionTranscript (Fin N) (FlagPair K V)) := markingClass hdim width hw c.2

theorem marking_fixed_class (hdim : finrank K V=5) (p : Law (κ×(Fin N→FlagPair K V)))
    (hcons : ∀ c x,0<p (c,x)→TupleConsistent x)
    (width : ℝ) (hw : 0≤width) (l : ℕ)
    (hsize : 39*(l:ℝ)+expensiveBound K V≤N) :
    ∃ a : SlotClass,(1:ℝ)/39≤eventMass (first (withMessage p markingMessage))
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a) := by
  have hn : Nonempty SlotClass:=⟨.inl 0⟩
  obtain ⟨a,ha⟩:=fixed_large_class (first (withMessage p markingMessage))
    (fun c=>unspecified c.2) (markedCode hdim width hw) l (by
      intro c hm
      rw [slotClass_card]
      have hh:=marked_cheap_count hdim p hcons c.1 c.2 hm
      exact_mod_cast (show 39*(l:ℝ)≤(unspecified c.2).card by linarith))
  refine ⟨a,?_⟩
  norm_num only [slotClass_card] at ha
  exact ha

def markedClassLaw (hdim : finrank K V=5) (p : Law (κ×(Fin N→FlagPair K V)))
    (hl : l≤N) (width : ℝ) (hw : 0≤width) (a : SlotClass)
    (hE : 0<eventMass (first (withMessage p markingMessage))
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a)) :=
  selectByContext
    (conditionContext (withMessage p markingMessage)
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a) hE)
    (fun c=>(selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a c : Fin l→Fin N))

lemma markedClassLaw_deficit (hdim : finrank K V=5) (p : Law (κ×(Fin N→FlagPair K V)))
    (hinc : ∀ c x,0<p (c,x)→TupleIncident x)
    (hcons : ∀ c x,0<p (c,x)→TupleConsistent x)
    (hl : l≤N) (width : ℝ) (hw : 0≤width) (a : SlotClass)
    (hE : 0<eventMass (first (withMessage p markingMessage))
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a)) :
    mean (first (markedClassLaw hdim p hl width hw a hE))
      (fun c=>(l:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)-
        entropy (fiber (markedClassLaw hdim p hl width hw a hE) c))≤
    mean (first (withMessage p markingMessage))
      (fun c=>activeDeficit (fiber (withMessage p markingMessage) c) (unspecified c.2)
        (Real.log (153*(Nat.card K:ℝ)^4)))/
      eventMass (first (withMessage p markingMessage))
        (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a) := by
  apply selectedClass_deficit hl (withMessage p markingMessage)
  · intro c hc
    exact marking_deficit_nonneg hdim p hinc hcons c.1 c.2 hc
  · intro c hc
    exact unionMessage_fixedOutside p twoScanTypes (fun x=>expensiveSet x (Nat.card K))
      (fun x=>reverseExpensive x (Nat.card K)) c.1 c.2 hc
  · intro c hc i hi
    exact marking_posterior_cap hdim p hinc hcons c.1 c.2 hc i hi
end SharpRamseyFive.Marking

end

end OAI
