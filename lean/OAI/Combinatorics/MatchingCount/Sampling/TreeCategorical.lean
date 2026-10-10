import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCounts
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeFraction
import OAI.Combinatorics.MatchingCount.Machines.TreeListMore

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def sum (xs : List Fraction) : Fraction := xs.foldl (fun a b=>add (b,a)) (0,1)
def sumRealizer : Realizer sum :=
  (composition (pair (identity (A:=List Fraction)) (constant (0,1))) (fold addRealizer)).congr (fun _=>rfl)

lemma fold_den (xs : List Fraction) (a : Fraction) (ha : 0<a.2) :
    0<(xs.foldl (fun a b=>add (b,a)) a).2 := by
  induction xs generalizing a with
  | nil => exact ha
  | cons _ _ ih => exact ih _ (normalize_den_pos _)
lemma fold_val (xs : List Fraction) (a : Fraction) (ha : 0<a.2)
    (hx : ∀ b∈xs,0<b.2) :
    val (xs.foldl (fun a b=>add (b,a)) a)=val a+(xs.map val).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hab : 0<(add (b,a)).2 := normalize_den_pos _
    rw [List.foldl_cons,ih _ hab (fun c hc=>hx c (by simp [hc])),
      add_val b a (Nat.ne_of_gt (hx b (by simp))) (Nat.ne_of_gt ha)]
    simp only [List.map_cons,List.sum_cons]
    ring
lemma sum_den (xs : List Fraction) : 0<(sum xs).2 := fold_den xs (0,1) (by decide)
lemma sum_val (xs : List Fraction) (hx : ∀ b∈xs,0<b.2) :
    val (sum xs)=(xs.map val).sum := by
  rw [sum,fold_val xs (0,1) (by decide) hx]
  simp [val]

def cumulativeFraction (x : List Fraction×ℕ) : Fraction := sum (x.1.take x.2)
def cumulativeFractionRealizer : Realizer cumulativeFraction := (composition (take (0,1)) sumRealizer).congr (fun _=>rfl)
lemma cumulativeFraction_val {r : ℕ} (p : Fin r → ℚ) (hp : ∀ i,0≤p i) (n : ℕ) :
    val (cumulativeFraction (List.ofFn (fun i=>repr (p i)),n))=FiniteChoice.cumulative p n := by
  rw [cumulativeFraction,sum_val]
  · simp only [List.map_take,List.map_ofFn,Function.comp_apply,val_repr (hp _),List.sum_take_ofFn,
      FiniteChoice.cumulative,Finset.sum_filter]
  · intro b hb
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hb)
    subst b
    exact (p i).pos

end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.TreeTyped

def bitValue : Realizer StackAddition.value :=
  (composition (composition (pair (reverse (A:=Bool)) (constant (1,0)))
    (fold mulStepRealizer)) second).congr (by
      intro bs
      change (bs.reverse.foldl (fun z b=>mulStep (b,z)) (1,0)).2=_
      rw [mulStep_fold]
      simp)

def bitDenominator (bs : List Bool) : ℕ := bs.foldl (fun a _=>2*a) 1
lemma bitDenominator_eq (bs : List Bool) : bitDenominator bs=2^bs.length := by
  have h : ∀ a,bs.foldl (fun a _=>2*a) a=a*2^bs.length := by
    induction bs with
    | nil => intro a; simp
    | cons _ _ ih => intro a; simp only [List.foldl_cons,ih,List.length_cons,pow_succ]; ring
  simpa [bitDenominator] using h 1

def bitDenominatorRealizer : Realizer bitDenominator :=
  (composition (pair (identity (A:=List Bool)) (constant 1))
    (fold (composition second double))).congr (fun _=>rfl)
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction

def predicate (x : (List Fraction×Fraction)×ℕ) : Bool :=
  TreeFraction.less (x.1.2,cumulativeFraction (x.1.1,x.2+1))
def predicateRealizer : Realizer predicate := by
  let C : Realizer (fun x : (List Fraction×Fraction)×ℕ=>cumulativeFraction (x.1.1,x.2+1)) :=
    (composition (pair first.fst (composition second successor)) cumulativeFractionRealizer).congr (fun _=>rfl)
  exact (composition (pair first.snd C) lessRealizer).congr (fun _=>rfl)

def choose (x : List Fraction×Fraction) : ℕ :=
  listMin ((List.range x.1.length).filter (fun i=>predicate (x,i)),x.1.length)

def chooseRealizer : Realizer choose := by
  let rs : Realizer (fun x : List Fraction×Fraction=>List.range x.1.length) :=
    composition (composition first listLength) range
  let good := composition (pair identity rs) (filterWith predicateRealizer)
  exact (composition (pair good (composition first listLength)) listMinRealizer).congr (fun _=>rfl)

lemma choose_eq {r K : ℕ} (p : Fin r → ℚ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (hK : 0<K) (J : Fin K) :
    choose (List.ofFn (fun i=>repr (p i)),(J.val,K))=(FiniteChoice.choose p hs hK J).val := by
  let j := FiniteChoice.choose p hs hK J
  have hpred (i : ℕ) : predicate ((List.ofFn (fun i=>repr (p i)),(J.val,K)),i)=
      decide ((J.val:ℚ)/K<FiniteChoice.cumulative p (i+1)) := by
    rw [predicate,less_val (J.val,K) (cumulativeFraction (List.ofFn (fun i=>repr (p i)),i+1)) hK (sum_den _),cumulativeFraction_val p hp]
    rfl
  unfold choose
  simp only [List.length_ofFn]
  apply le_antisymm
  · apply listMin_le
    simp only [List.mem_filter,List.mem_range,hpred,decide_eq_true_eq]
    exact ⟨j.isLt,FiniteChoice.choose_upper p hs hK J⟩
  · apply le_listMin j.isLt.le
    intro i hi
    simp only [List.mem_filter,List.mem_range,hpred,decide_eq_true_eq] at hi
    exact FiniteChoice.choose_le p hs hK J ⟨i,hi.1⟩ hi.2

def chooseBits (x : List Fraction×List Bool) : ℕ :=
  choose (x.1,(StackAddition.value x.2,bitDenominator x.2))
def chooseBitsRealizer : Realizer chooseBits :=
  composition (pair first (pair (composition second bitValue) (composition second bitDenominatorRealizer)))
    chooseRealizer

lemma chooseBits_eq {r k : ℕ} (p : Fin r → ℚ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (bits : Fin k → Bool) :
    chooseBits (List.ofFn (fun i=>repr (p i)),List.ofFn bits)=
      (FiniteChoice.chooseBits p hs k bits).val := by
  have hv' (k : ℕ) (bits : Fin k → Bool) :
      StackAddition.value (List.ofFn bits)=∑ i, (if bits i then 1 else 0)*2^i.val := by
    induction k with
    | zero => simp [StackAddition.value]
    | succ k ih =>
      rw [List.ofFn_succ,StackAddition.value,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
      rw [Finset.mul_sum]
      have hn : (bits 0).toNat=(if bits 0 then 1 else 0) := by cases bits 0 <;> rfl
      rw [hn]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  have hv : StackAddition.value (List.ofFn bits)=(FiniteChoice.tapeIndex k bits).val := by
    rw [FiniteChoice.tapeIndex_value,hv']
  rw [chooseBits,bitDenominator_eq,List.length_ofFn,hv]
  exact choose_eq p hp hs (by positivity) (FiniteChoice.tapeIndex k bits)
end MatchingFPRAS.ExecutableChoice

end OAI
