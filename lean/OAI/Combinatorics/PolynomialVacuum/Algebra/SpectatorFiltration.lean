import OAI.Combinatorics.PolynomialVacuum.Algebra.TransportFiltration

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

def spectatorSlot {n : ℕ} (j : Fin (n+1)) (c : Fin (n+2)) : Fin (n+2) :=
  if j.val<c.val then j.castSucc else j.succ

@[simp] theorem spectatorSlot_last {n : ℕ} (j : Fin (n+1)) :
    spectatorSlot j (Fin.last (n+1))=j.castSucc := by simp [spectatorSlot,j.isLt]
@[simp] theorem spectatorSlot_self_left {n : ℕ} (j : Fin (n+1)) :
    spectatorSlot j (pairLeft j)=pairRight j := by simp [spectatorSlot,pairLeft,pairRight]
@[simp] theorem spectatorSlot_self_right {n : ℕ} (j : Fin (n+1)) :
    spectatorSlot j (pairRight j)=pairLeft j := by simp [spectatorSlot,pairLeft,pairRight]

theorem spectatorSlot_other {n : ℕ} {j k : Fin (n+1)} (hjk : j≠k) :
    spectatorSlot j (pairLeft k)=spectatorSlot j (pairRight k) ∧
    spectatorSlot j (pairLeft k)≠pairLeft k ∧ spectatorSlot j (pairLeft k)≠pairRight k := by
  have hn : j.val≠k.val := fun h => hjk (Fin.ext h)
  by_cases hlt : j.val<k.val
  · have hlt' : j.val<k.val+1 := by omega
    simp only [spectatorSlot,pairLeft,pairRight,Fin.val_castSucc,Fin.val_succ,hlt,hlt',ite_true]
    refine ⟨trivial,?_,?_⟩
    · intro h; exact hjk (Fin.castSucc_injective _ h)
    · intro h
      have hh:=congrArg Fin.val h
      simp only [Fin.val_castSucc,Fin.val_succ] at hh
      omega
  · have hlt' : ¬j.val<k.val+1 := by omega
    simp only [spectatorSlot,pairLeft,pairRight,Fin.val_castSucc,Fin.val_succ,hlt,hlt',ite_false]
    refine ⟨trivial,?_,?_⟩
    · intro h
      have hh:=congrArg Fin.val h
      simp only [Fin.val_castSucc,Fin.val_succ] at hh
      omega
    · intro h; exact hjk (Fin.succ_injective _ h)

theorem tensorExchange_spectator_filtration {N : ℕ} {ι : Type*}
    (a b : Fin N) (_hab : a≠b) (x y : MvPolynomial ι ℂ) (v : ι) (d : ℕ)
    (W : PolynomialTensor N ι) (hx : x.degreeOf v=0) (hy : y.degreeOf v≤1)
    (hd : ∀ s, (W s).degreeOf v ≤ d+1)
    (hf : ∀ s, s b=Spin.plus → (W s).degreeOf v ≤ d)
    (s : Fin N → Spin) (hs : s a=Spin.plus) :
    (tensorExchange a b x y W s).degreeOf v ≤ d+2 := by
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro ab _
  change (polyExchangeNumerator x y (s a,s b) ab * W (replacePair s a b ab)).degreeOf v ≤ d+2
  by_cases ht : ab.2=Spin.plus
  · have hp := hf (replacePair s a b ab) (by simpa only [replacePair_right] using ht)
    exact (dmul (polyExchange_degree x y _ ab v 1 (by omega) hy) hp).trans (by omega)
  · have hl : charge ab.2 < charge (s a) := by
      rw [hs]; cases hh : ab.2 <;> simp_all [charge]
    exact (dmul (polyExchange_spectator_loss x y _ ab v hx hy hl) (hd _)).trans (by omega)

theorem tensorExchange_unaffected_filtration {N : ℕ} {ι : Type*}
    (a b mark : Fin N) (hma : mark≠a) (hmb : mark≠b)
    (x y : MvPolynomial ι ℂ) (v : ι) (d : ℕ) (W : PolynomialTensor N ι)
    (hx : x.degreeOf v=0) (hy : y.degreeOf v=0)
    (hf : ∀ s, s mark=Spin.plus → (W s).degreeOf v ≤ d)
    (s : Fin N → Spin) (hs : s mark=Spin.plus) :
    (tensorExchange a b x y W s).degreeOf v ≤ d := by
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro ab _
  change (polyExchangeNumerator x y (s a,s b) ab * W (replacePair s a b ab)).degreeOf v ≤ d
  have hp := hf (replacePair s a b ab) (by simpa only [replacePair_other s hma hmb] using hs)
  exact (dmul (polyExchange_degree x y _ ab v 0 (le_of_eq hx) (le_of_eq hy)) hp).trans (by omega)

 

theorem transportCup_spectator_filtration {n : ℕ} (i j : Fin (n+1)) (hji : j≠i)
    (ks : List (Fin (n+1))) (c e : Fin (n+2)) (hp : CarriedPath c ks e)
    (d : ℕ) (W : PolynomialTensor (n+2) (Fin (n+1)))
    (hd : ∀ s, (W s).degreeOf j ≤ d+1)
    (hf : ∀ s, s (spectatorSlot j c)=Spin.plus → (W s).degreeOf j ≤ d) :
    (∀ s, (transportCup i ks W s).degreeOf j ≤ d+2*ks.count j+1) ∧
    (∀ s, s (spectatorSlot j e)=Spin.plus →
      (transportCup i ks W s).degreeOf j ≤ d+2*ks.count j) := by
  induction ks generalizing d W c with
  | nil =>
    simp only [CarriedPath] at hp
    subst e
    simpa [transportCup] using And.intro hd hf
  | cons k ks ih =>
    obtain ⟨rfl,hp⟩:=hp
    have hx : (C T*X i : MvPolynomial (Fin (n+1)) ℂ).degreeOf j=0 := by
      exact Nat.eq_zero_of_le_zero (dconst_mul _ (le_of_eq (degreeOf_X_of_ne hji)))
    by_cases hjk : j=k
    · subst k
      have hy : (X j : MvPolynomial (Fin (n+1)) ℂ).degreeOf j≤1 := by simp
      have hab : pairLeft j≠pairRight j := by intro h; have:=congrArg Fin.val h; simp [pairLeft,pairRight] at this
      have hh := ih (pairRight j) hp (d+2)
        (tensorExchange (pairLeft j) (pairRight j) (C T*X i) (X j) W)
        (fun s => (tensorExchange_degree _ _ _ _ _ j (d+1) 1 (by omega) hy hd s).trans (by omega))
        (by
          intro s hs
          simp only [spectatorSlot_self_left] at hf
          simp only [spectatorSlot_self_right] at hs
          exact tensorExchange_spectator_filtration _ _ hab _ _ j d W hx hy hd hf s hs)
      simpa [transportCup,List.count_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    · obtain ⟨he,ha,hb⟩:=spectatorSlot_other hjk
      have hy : (X k : MvPolynomial (Fin (n+1)) ℂ).degreeOf j=0 := degreeOf_X_of_ne hjk
      have hh := ih (pairRight k) hp d
        (tensorExchange (pairLeft k) (pairRight k) (C T*X i) (X k) W)
        (fun s => (tensorExchange_degree _ _ _ _ _ j (d+1) 0 (le_of_eq hx) (le_of_eq hy) hd s).trans (by omega))
        (by
          intro s hs
          exact tensorExchange_unaffected_filtration _ _ _ ha hb _ _ j d W hx hy hf s (he ▸ hs))
      simpa [transportCup,List.count_cons,hjk,Ne.symm hjk] using hh

end PolynomialVacuumAlgebra

end OAI
