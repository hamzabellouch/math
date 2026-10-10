import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.WindowReadiness
import OAI.Combinatorics.RamseyFive.Marking.SurvivingWindowCode
import OAI.Combinatorics.RamseyFive.Geometry.EmptyVariableTree

namespace OAI

namespace SharpRamseyFive.Windows
open FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {w r : ℕ}
local instance deletionTargetDE : DecidableEq (Fin w×Fin (2*r)) := Classical.decEq _

def goodWindowSet (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r) : Finset (Fin w) :=
  Finset.univ.filter (fun v=>∀b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0)
def survivingWindowSet (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r)
    (drop : Fin w→ℝ) (k : ℝ) : Finset (Fin w) :=
  (goodWindowSet bad sel).filter (fun v=>drop v≤k)
lemma mem_goodWindowSet (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r) (v : Fin w) :
    v∈goodWindowSet bad sel ↔ ∀b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0 := by
  simp only [goodWindowSet,Finset.mem_filter,Finset.mem_univ,true_and]
lemma mem_survivingWindowSet (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r)
    (drop : Fin w→ℝ) (k : ℝ) (v : Fin w) :
    v∈survivingWindowSet bad sel drop k ↔
      (∀b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0) ∧ drop v≤k := by
  simp only [survivingWindowSet,Finset.mem_filter,mem_goodWindowSet]

theorem ineligible_middle_count (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r)
    (drop : Fin w→ℝ) (k : ℝ) :
    ((Finset.univ.filter fun i : Fin w×Fin (2*r)=>
      ¬(i.1∈survivingWindowSet bad sel drop k ∧ bad (Sum.inr i)=0)).card:ℝ)≤
      (∑v,∑t,if windowReady bad sel v t then (0:ℝ) else 1)+
      (2*r:ℝ)*((goodWindowSet bad sel).filter fun v=>k<drop v).card := by
  rw [←Finset.sum_boole,Fintype.sum_prod_type]
  have hp (v : Fin w) (t : Fin (2*r)) :
      (if ¬(v∈survivingWindowSet bad sel drop k ∧ bad (Sum.inr (v,t))=0) then (1:ℝ) else 0)≤
      (if windowReady bad sel v t then 0 else 1)+
        (if v∈goodWindowSet bad sel ∧ k<drop v then 1 else 0) := by
    by_cases hg : ∀b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0
    · by_cases hd : drop v≤k <;> by_cases ht : bad (Sum.inr (v,t))=0 <;>
        simp [mem_survivingWindowSet,mem_goodWindowSet,windowReady,hg,hd,ht,
          true_and,and_true,and_false,not_true_eq_false,
          not_false_eq_true] <;> split_ifs <;> (first | (solve | norm_num) | linarith)
    · simp only [mem_survivingWindowSet,mem_goodWindowSet,windowReady,hg,
        false_and,and_false,not_false_eq_true,ite_true,ite_false,add_zero,le_refl]
  calc
    _ ≤ ∑v,∑t,((if windowReady bad sel v t then (0:ℝ) else 1)+
        (if v∈goodWindowSet bad sel ∧ k<drop v then (1:ℝ) else 0)) :=
      Finset.sum_le_sum (fun v _=>Finset.sum_le_sum (fun t _=>hp v t))
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,←Finset.mul_sum]
      congr 1
      congr 1
      rw [Finset.sum_boole]
      congr 2
      ext v
      simp

theorem reciprocal_loss_aggregate {Ω : Type*} [Fintype Ω] (p : Law Ω)
    (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r) (drop : Fin w→ℝ) (k B : ℝ)
    (kept : Ω→Fin w×Fin (2*r)→Prop) (hB : 0≤B)
    (hkeep : ∀v∈survivingWindowSet bad sel drop k,∀t,bad (Sum.inr (v,t))=0→
      mean p (fun z=>if kept z (v,t) then 0 else 1)≤B) :
    mean p (fun z=>((Finset.univ.filter (fun i : Fin w×Fin (2*r)=>
      i.1∈survivingWindowSet bad sel drop k ∧ bad (Sum.inr i)=0 ∧ kept z i))ᶜ.card:ℝ))≤
      (∑v,∑t,if windowReady bad sel v t then (0:ℝ) else 1)+
      (2*r:ℝ)*((goodWindowSet bad sel).filter fun v=>k<drop v).card+
      (w*(2*r):ℝ)*B := by
  let eligible := fun i : Fin w×Fin (2*r)=>i.1∈survivingWindowSet bad sel drop k ∧ bad (Sum.inr i)=0
  have hh:=retained_filter_loss p eligible kept B hB (fun i hi=>hkeep i.1 hi.1 i.2 hi.2)
  have hi:=ineligible_middle_count bad sel drop k
  have he : (Fintype.card (Fin w×Fin (2*r)):ℝ)=(w*(2*r):ℝ) := by simp
  rw [he] at hh
  simp only [eligible,and_assoc] at hh
  exact hh.trans (add_le_add hi le_rfl)
end
end SharpRamseyFive.Windows

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance allWindowProp (P : Prop) : Decidable P := Classical.propDecidable P
local instance allWindowTDE (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance allWindowBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance allWindowIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V))) ]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
  {s : ℝ} (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

def allWindowLevelLaw : Law (WindowLevelsData (K:=K) (V:=V) E.card) :=
  if hE : E.Nonempty then survivingLevelLaw p u sel E hE (W hE) else uniformType _

def allWindowEncoded (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card) :
    VariableTreeMessage f r t (Finset.univ,Finset.univ) :=
  if hE : E.Nonempty then
    survivingEncoded f r p u sel E hE (W hE) σ hσ hq hd c δ τ P hδ t z
  else variableTreeEmpty f r t (Finset.univ,Finset.univ)

def allWindowExperiment : Law ((Slots w n→FlagPair K V)×
    (WindowLevelsData (K:=K) (V:=V) E.card×VariableTreeTape f r w)) :=
  adaptiveLaw p (fun _=>adaptiveLaw (allWindowLevelLaw p u sel E W) (fun _=>variableTreeLaw f r w))

def allWindowFailure (v : Fin w) (t : Fin (2*n)) : ℝ :=
  mean (allWindowExperiment f r p u sel E W) (fun z=>
    if z.1 (middleSlot v t)∉variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd c δ τ P hδ z.2.2 z.2.1)
      (survivorRank E v) then 1 else 0)

omit [Nonempty (Fin n)] in
lemma allWindowFailure_nonempty (hE : E.Nonempty) (v : Fin w) (t : Fin (2*n)) :
    allWindowFailure f r p u sel E W σ hσ hq hd c δ τ P hδ v t=
      survivingTargetFailure f r p u sel E hE (W hE) σ hσ hq hd c δ τ P hδ v t := by
  simp only [allWindowFailure,allWindowExperiment,allWindowLevelLaw,allWindowEncoded,
    dite_eq_left hE,survivingTargetFailure,survivingExperiment]

def allWindowPositions (bad : Slots w n→ℝ) (t : VariableTreeTape f r w)
    (z : (Slots w n→FlagPair K V)×WindowLevelsData (K:=K) (V:=V) E.card) :
    Finset (Fin w×Fin (2*n)) :=
  Finset.univ.filter fun i=>i.1∈E ∧ bad (Sum.inr i)=0 ∧
    z.1 (Sum.inr i)∈variableTreeDomain f r t (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd c δ τ P hδ t z.2) (survivorRank E i.1)

omit [Nonempty (Fin n)] in
theorem allWindow_loss (bad : Slots w n→ℝ) (drop : Fin w→ℝ) (k B : ℝ)
    (hE : E=survivingWindowSet bad sel drop k) (hB : 0≤B)
    (hh : ∀v∈E,∀t,bad (middleSlot v t)=0→
      allWindowFailure f r p u sel E W σ hσ hq hd c δ τ P hδ v t≤B) :
    mean (allWindowExperiment f r p u sel E W) (fun z=>
      ((allWindowPositions f r p u sel E W σ hσ hq hd c δ τ P hδ bad z.2.2 (z.1,z.2.1))ᶜ.card:ℝ))≤
      (∑v,∑t,if windowReady bad sel v t then (0:ℝ) else 1)+
      (2*n:ℝ)*((goodWindowSet bad sel).filter fun v=>k<drop v).card+(w*(2*n):ℝ)*B := by
  let kept := fun (z : (Slots w n→FlagPair K V)×
    (WindowLevelsData (K:=K) (V:=V) E.card×VariableTreeTape f r w)) (i : Fin w×Fin (2*n))=>
    z.1 (Sum.inr i)∈variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd c δ τ P hδ z.2.2 z.2.1) (survivorRank E i.1)
  have hk (v : Fin w) (hv : v∈survivingWindowSet bad sel drop k) (t : Fin (2*n))
      (ht : bad (Sum.inr (v,t))=0) :
      mean (allWindowExperiment f r p u sel E W) (fun z=>if kept z (v,t) then 0 else 1)≤B := by
    have hv' : v∈E := by rwa [hE]
    have hb:=hh v hv' t ht
    unfold allWindowFailure at hb
    convert hb using 1
    congr 1
    funext z
    dsimp only [kept,middleSlot]
    split_ifs <;> simp_all
  have h:=reciprocal_loss_aggregate (allWindowExperiment f r p u sel E W) bad sel drop k B kept hB (by
    intro v hv t ht
    convert hk v hv t ht using 1
    congr 1
    funext z
    by_cases hb : kept z (v,t) <;> simp only [hb,ite_true,ite_false])
  simpa only [allWindowPositions,hE,kept] using h
end
end SharpRamseyFive.Marking

end OAI
