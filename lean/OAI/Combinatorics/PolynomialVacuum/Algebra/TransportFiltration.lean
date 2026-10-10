import OAI.Combinatorics.PolynomialVacuum.Algebra.ExchangeDegrees
import OAI.Combinatorics.PolynomialVacuum.Algebra.TensorActions
import OAI.Combinatorics.PolynomialVacuum.Algebra.SpectatorList

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

 

def CarriedPath {n : ℕ} (c : Fin (n+2)) : List (Fin (n+1)) → Fin (n+2) → Prop
  | [], e => c=e
  | k::ks, e => c=pairLeft k ∧ CarriedPath (pairRight k) ks e

theorem carriedPath_of_range {n : ℕ} (ks : List (Fin (n+1))) (a m : ℕ)
    (h : ks.map Fin.val=List.range' a m) (c e : Fin (n+2))
    (hc : c.val=a) (he : e.val=a+m) : CarriedPath c ks e := by
  induction m generalizing a ks c with
  | zero =>
    have hz : ks=[] := by simpa using congrArg List.length h
    subst ks
    exact Fin.ext (by omega)
  | succ m ih =>
    cases ks with
    | nil => simp at h
    | cons k ks =>
      rw [List.map_cons,List.range'_succ] at h
      obtain ⟨hk,hks⟩:=List.cons.inj h
      refine ⟨Fin.ext (by simpa [pairLeft] using hc.trans hk.symm),?_⟩
      exact ih ks (a+1) hks (pairRight k) (by simp [pairRight,hk]) (by omega)

theorem rightSpectators_path {n : ℕ} (i : Fin (n+1)) :
    CarriedPath (pairRight i) (rightSpectators i) (Fin.last (n+1)) := by
  exact carriedPath_of_range _ (i.val+1) (n-i.val) (rightSpectators_val i) _ _ rfl
    (by have hi:=i.isLt; simp only [Fin.val_last]; omega)

theorem charge_ge_minus_one (s : Spin) : -1 ≤ charge s := by cases s <;> decide

theorem tensorExchange_carried_filtration {N : ℕ} {ι : Type*}
    (a b mark : Fin N) (hab : a≠b) (hma : mark≠a) (hmb : mark≠b)
    (x y : MvPolynomial ι ℂ) (v : ι) (d : ℕ) (W : PolynomialTensor N ι)
    (hx : x.degreeOf v ≤ 1) (hy : y.degreeOf v=0)
    (hd : ∀ s, (W s).degreeOf v ≤ d+1)
    (hf : ∀ s, s mark=Spin.plus → -1 < charge (s a) → (W s).degreeOf v ≤ d)
    (s : Fin N → Spin) (hm : s mark=Spin.plus) (hb : -1 < charge (s b)) :
    (tensorExchange a b x y W s).degreeOf v ≤ d+2 := by
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro ab _
  change (polyExchangeNumerator x y (s a,s b) ab * W (replacePair s a b ab)).degreeOf v ≤ d+2
  by_cases ht : -1 < charge ab.1
  · have hp := hf (replacePair s a b ab)
      (by simpa only [replacePair_other s hma hmb] using hm)
      (by simpa only [replacePair_left s hab] using ht)
    exact (dmul (polyExchange_degree x y _ ab v 1 hx (by omega)) hp).trans (by omega)
  · have hl : charge ab.1 < charge (s b) := by omega
    exact (dmul (polyExchange_carried_loss x y _ ab v hx hy hl) (hd _)).trans (by omega)

theorem transportCup_marked_filtration {n : ℕ} (i : Fin (n+1))
    (ks : List (Fin (n+1))) (c e : Fin (n+2)) (hp : CarriedPath c ks e)
    (hks : ∀ k ∈ ks, i<k) (d : ℕ) (W : PolynomialTensor (n+2) (Fin (n+1)))
    (hd : ∀ s, (W s).degreeOf i ≤ d+1)
    (hf : ∀ s, s (pairLeft i)=Spin.plus → -1 < charge (s c) → (W s).degreeOf i ≤ d) :
    (∀ s, (transportCup i ks W s).degreeOf i ≤ d+2*ks.length+1) ∧
    (∀ s, s (pairLeft i)=Spin.plus → -1 < charge (s e) →
      (transportCup i ks W s).degreeOf i ≤ d+2*ks.length) := by
  induction ks generalizing d W c with
  | nil =>
    simp only [CarriedPath] at hp
    subst e
    simpa [transportCup] using And.intro hd hf
  | cons k ks ih =>
    obtain ⟨rfl,hp⟩:=hp
    have hik : i<k := hks k (by simp)
    have hx : (C T*X i : MvPolynomial (Fin (n+1)) ℂ).degreeOf i ≤ 1 := by
      exact dconst_mul _ (by simp)
    have hy : (X k : MvPolynomial (Fin (n+1)) ℂ).degreeOf i=0 := degreeOf_X_of_ne (ne_of_lt hik)
    have hab : pairLeft k≠pairRight k := by intro h; have:=congrArg Fin.val h; simp [pairLeft,pairRight] at this
    have hma : pairLeft i≠pairLeft k := by intro h; have:=congrArg Fin.val h; simp [pairLeft] at this; exact (ne_of_lt hik) (Fin.ext this)
    have hmb : pairLeft i≠pairRight k := by intro h; have:=congrArg Fin.val h; simp only [pairLeft,pairRight,Fin.val_castSucc,Fin.val_succ] at this; have hh : i.val<k.val := hik; omega
    have h := ih (pairRight k) hp (fun l hl => hks l (by simp [hl])) (d+2)
      (tensorExchange (pairLeft k) (pairRight k) (C T*X i) (X k) W)
      (fun s => (tensorExchange_degree _ _ _ _ _ i (d+1) 1 hx (by omega) hd s).trans (by omega))
      (fun s hm hs => tensorExchange_carried_filtration _ _ _ hab hma hmb _ _ i d W hx hy hd hf s hm hs)
    simpa [transportCup,List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end PolynomialVacuumAlgebra

end OAI
