import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.AdaptiveLaw
import OAI.Combinatorics.MatchingCount.Sampling.RankOrder

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized
open Finset

variable {V : Type} [Fintype V] {m : ℕ}

def RowBound (t : Table) (w : Fin m → ℕ) : Prop := ∀ a r,read t a.val r ≤ w a

def mergeEnvelope (w : Fin m → ℕ) (l p : Fin m) (s : ℕ) : Fin m → ℕ :=
  fun a=>if a=l then 1 else if a=p then 2^s*w l*w p else w a

lemma mergeEnvelope_pos (w : Fin m → ℕ) (hw : ∀ a,1≤w a) (l p : Fin m) (s : ℕ) :
    ∀ a,1 ≤ mergeEnvelope w l p s a := by
  intro a
  unfold mergeEnvelope
  split_ifs
  · exact le_rfl
  · have hl := hw l
    have hp := hw p
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · exact hw a

lemma mergeEnvelope_prod (w : Fin m → ℕ) (l p : Fin m) (h : p≠l) (s : ℕ) :
    (∏ a,mergeEnvelope w l p s a)=2^s*∏ a,w a := by
  have hp : p∈(univ : Finset (Fin m)).erase l := by simp [h]
  rw [←mul_prod_erase univ (mergeEnvelope w l p s) (mem_univ l),
    ←mul_prod_erase (univ.erase l) (mergeEnvelope w l p s) hp,
    ←mul_prod_erase univ w (mem_univ l),←mul_prod_erase (univ.erase l) w hp]
  have he : (∏ a∈(univ.erase l).erase p,mergeEnvelope w l p s a)=
      ∏ a∈(univ.erase l).erase p,w a := by
    apply prod_congr rfl
    intro a ha
    have hal : a≠l := (mem_erase.mp (mem_erase.mp ha).2).1
    have hap : a≠p := (mem_erase.mp ha).1
    simp [mergeEnvelope,hal,hap]
  rw [he]
  simp only [mergeEnvelope,↓reduceIte,h]
  ring

omit [Fintype V] in
lemma entry_rowBound (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (t : Table) (w : Fin m → ℕ)
    (_ : ∀ a,1≤w a) (ht : RowBound t w) :
    ∀ a r,entry bags R parent l a t r ≤
      match parent l with
      | none => w a
      | some p => mergeEnvelope w l p (sharedCount bags R l) a := by
  intro a r
  unfold entry
  cases hp : parent l with
  | none =>
    simp only
    split_ifs with h
    · subst a; exact ht l _
    · exact ht a r
  | some p =>
    simp only
    unfold mergeEnvelope
    split_ifs with h h'
    · exact le_rfl
    · subst a
      calc
        _ ≤ ∑ k∈range (sharedCount bags R l+1),
            (sharedCount bags R l).choose k*w l*w p := by
          apply sum_le_sum
          intro k hk
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (ht l _)) (ht p _)
        _ = 2^(sharedCount bags R l)*w l*w p := by
          rw [←sum_mul,←sum_mul,Nat.sum_range_choose]
    · exact ht a r

omit [Fintype V] in
lemma update_rowBound (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (B : ℕ) (t : Table) (w : Fin m → ℕ)
    (hw : ∀ a,1≤w a) (ht : RowBound t w) :
    RowBound (update bags R parent l B t)
      (match parent l with | none=>w | some p=>mergeEnvelope w l p (sharedCount bags R l)) := by
  intro a r
  rw [update,read_tabulate]
  split_ifs
  · have h := entry_rowBound bags R parent l t w hw ht a r
    cases hh : parent l <;> simpa only [hh] using h
  · exact Nat.zero_le _

lemma sharedCount_le_card (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    sharedCount bags R l≤Fintype.card V := by
  exact (card_le_card (filter_subset _ _)).trans (card_le_univ _)

lemma run_envelope (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (hp : ∀ l p,parent l=some p → p≠l) (ls : List (Fin m)) (R : Finset V)
    (t : Table) (w : Fin m → ℕ) (hw : ∀ a,1≤w a) (ht : RowBound t w) :
    ∃ v : Fin m → ℕ,(∀ a,1≤v a) ∧ RowBound (run bags parent ls R t) v ∧
      (∏ a,v a) ≤ 2^(Fintype.card V*ls.length)*(∏ a,w a) := by
  induction ls generalizing R t w with
  | nil => exact ⟨w,hw,ht,by simp⟩
  | cons l ls ih =>
    let v := match parent l with | none=>w | some p=>mergeEnvelope w l p (sharedCount bags R l)
    have hv : ∀ a,1≤v a := by
      cases hh : parent l with
      | none => simpa [v,hh] using hw
      | some p => simpa only [v,hh] using mergeEnvelope_pos w hw l p (sharedCount bags R l)
    have hvt : RowBound (update bags R parent l (Fintype.card V*ls.length) t) v :=
      update_rowBound bags R parent l _ t w hw ht
    have hprod : (∏ a,v a) ≤ 2^(Fintype.card V)*(∏ a,w a) := by
      cases hh : parent l with
      | none =>
        simp only [v,hh]
        exact Nat.le_mul_of_pos_left _ (by positivity)
      | some p =>
        simp only [v,hh]
        rw [mergeEnvelope_prod w l p (hp l p hh)]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (sharedCount_le_card bags R l))
    obtain ⟨z,hz,hzt,hzp⟩ := ih (trim bags R l) _ v hv hvt
    refine ⟨z,hz,hzt,?_⟩
    apply hzp.trans
    calc
      _ ≤ 2^(Fintype.card V*ls.length)*(2^Fintype.card V*∏ a,w a) := Nat.mul_le_mul_left _ hprod
      _ = _ := by rw [List.length_cons,Nat.mul_add,Nat.mul_one,pow_add]; ring

lemma run_entry_le (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (hp : ∀ l p,parent l=some p → p≠l) (ls : List (Fin m)) (R : Finset V)
    (t : Table) (w : Fin m → ℕ) (hw : ∀ a,1≤w a) (ht : RowBound t w) (a : Fin m) (r : ℕ) :
    read (run bags parent ls R t) a.val r ≤ 2^(Fintype.card V*ls.length)*(∏ a,w a) := by
  obtain ⟨v,hv,hvt,hvp⟩:=run_envelope bags parent hp ls R t w hw ht
  exact (hvt a r).trans ((single_le_prod (fun x _=>hv x) (mem_univ a)).trans hvp)

lemma pairingCount_pow_bound (n : ℕ) : pairingCount n ≤ 2^(n*n) := by
  calc
    _ ≤ n^(n/2) := pairingCount_le_half_power n
    _ ≤ (2^n)^(n/2) := Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) _
    _ = 2^(n*(n/2)) := (pow_mul _ _ _).symm
    _ ≤ 2^(n*n) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.div_le_self _ _))

lemma initial_rowBound (B : ℕ) : RowBound (initial m B) (fun _ : Fin m=>2^(B*B)) := by
  intro a r
  rw [initial,read_tabulate]
  split_ifs with h
  · exact (pairingCount_pow_bound r).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul h h))
  · exact Nat.zero_le _

lemma run_initial_size (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (hp : ∀ l p,parent l=some p → p≠l) (ls : List (Fin m)) (R : Finset V)
    (B : ℕ) (a : Fin m) (r : ℕ) :
    (read (run bags parent ls R (initial m B)) a.val r).size ≤
      Fintype.card V*ls.length+B*B*m+1 := by
  have h := run_entry_le bags parent hp ls R (initial m B) (fun _=>2^(B*B))
    (fun _=>Nat.one_le_iff_ne_zero.mpr (by positivity)) (initial_rowBound B) a r
  simp only [prod_const,card_univ,Fintype.card_fin,←pow_mul,←pow_add] at h
  simpa only [Nat.size_pow] using Nat.size_le_size h

lemma run_initial_product_le (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (hp : ∀ l p,parent l=some p → p≠l) (ls : List (Fin m)) (R : Finset V) (B : ℕ) :
    (∏ a : Fin m,read (run bags parent ls R (initial m B)) a.val 0) ≤
      2^(Fintype.card V*ls.length+B*B*m) := by
  obtain ⟨v,hv,hvt,hvp⟩ := run_envelope bags parent hp ls R (initial m B)
    (fun _=>2^(B*B)) (fun _=>Nat.one_le_iff_ne_zero.mpr (by positivity)) (initial_rowBound B)
  apply (prod_le_prod (fun a _=>hvt a 0)).trans
  simpa only [prod_const,card_univ,Fintype.card_fin,←pow_mul,←pow_add] using hvp

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
