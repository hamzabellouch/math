import OAI.Combinatorics.PolynomialVacuum.Algebra.ChargeCombinatorics

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

def ChargeZero {N : ℕ} (ψ : State N) : Prop :=
  ∀ s, (∑ j, charge (s j))≠0 → ψ s=0

@[simp] theorem natCharge_eq_fin (N : ℕ) (s : ℕ → Spin) :
    natCharge N s=∑ j : Fin N, charge (s j.val) := by
  exact (Fin.sum_univ_eq_sum_range (fun j => charge (s j)) N).symm

noncomputable def chargeSector {N : ℕ} (ψ : State N) : NatPolyTensor :=
  fun s => if natCharge N s≠0 then coordinatePolynomial ψ s else 0

@[simp] theorem eval_chargeSector {N : ℕ} (ψ : State N) (X : ℕ → ℂ) (s : ℕ → Spin) :
    evalNatPolyTensor (chargeSector ψ) X s=if natCharge N s≠0 then liftState ψ X s else 0 := by
  simp only [evalNatPolyTensor,chargeSector]; split_ifs <;> simp only [eval_coordinatePolynomial,map_zero]

theorem chargeSector_exchange {N : ℕ} (ψ : State N)
    (hex : LowerExchange (liftState ψ) N) :
    LowerExchange (evalNatPolyTensor (chargeSector ψ)) N := by
  intro j hj X
  funext s
  change (∑ ab : Pair, exchangeNumerator (X j) (X (j+1)) (s j,s (j+1)) ab *
    evalNatPolyTensor (chargeSector ψ) X (replacePair s j (j+1) ab)) =
    exchangeDenominator (X j) (X (j+1)) * evalNatPolyTensor (chargeSector ψ) (swapSite j X) s
  have hterm (ab : Pair) : exchangeNumerator (X j) (X (j+1)) (s j,s (j+1)) ab *
      evalNatPolyTensor (chargeSector ψ) X (replacePair s j (j+1) ab) =
      if natCharge N s≠0 then exchangeNumerator (X j) (X (j+1)) (s j,s (j+1)) ab *
      liftState ψ X (replacePair s j (j+1) ab) else 0 := by
    by_cases hab : charge (s j)+charge (s (j+1))=charge ab.1+charge ab.2
    · have hc : natCharge N (replacePair s j (j+1) ab)=natCharge N s := by
        rw [natCharge_replacePair hj]; omega
      simp only [eval_chargeSector,hc]; split_ifs <;> simp
    · rw [exchange_charge_conservation _ _ _ _ hab]
      split_ifs <;> simp
  simp only [hterm]
  rw [eval_chargeSector]
  split_ifs with hs
  · exact congrFun (hex j hj X) s
  · simp

theorem liftState_charge_zero {N : ℕ} (ψ : State N) (h : ChargeZero ψ)
    (X : ℕ → ℂ) (s : ℕ → Spin) (hs : natCharge N s≠0) : liftState ψ X s=0 := by
  simp only [liftState,liftPolyTensor,h _ (by simpa only [natCharge_eq_fin] using hs),map_zero]

theorem chargeSector_cup {n : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i) (hz : ChargeZero ψ)
    (i : ℕ) (hi : i≤n) (X : ℕ → ℂ) (hX : X (i+1)=T*X i) :
    evalNatPolyTensor (chargeSector Ψ) X=0 := by
  funext s
  rw [eval_chargeSector]
  split_ifs with hs
  · have he := congrFun (hc i hi X hX) s
    change liftState Ψ X s=naturalFusion n i X*(cup (s i,s (i+1))*liftState ψ (skipTwo i X) (skipTwo i s)) at he
    rw [he]
    by_cases hp : charge (s i)+charge (s (i+1))=0
    · have ht : natCharge n (skipTwo i s)≠0 := by rw [natCharge_removePair n i hi,hp,zero_add] at hs; exact hs
      rw [liftState_charge_zero ψ hz _ _ ht,mul_zero,mul_zero]
      rfl
    · simp only [cup,hp,ite_false,mul_zero,zero_mul,Pi.zero_apply]
  · rfl

theorem chargeSector_degree {N b : ℕ} (Ψ : State N) (s : ℕ → Spin) (j : Fin N)
    (h : (Ψ (fun a => s a.val)).degreeOf j≤b) : (chargeSector Ψ s).degreeOf j.val≤b := by
  unfold chargeSector; split_ifs
  · rw [coordinatePolynomial_degree]; exact h
  · simp

theorem chargeSector_minusZero {N : ℕ} (Ψ : State N) (hz : MinusZero Ψ)
    (s : ℕ → Spin) (j : Fin N) (hs : s j.val=Spin.minus) : killSite j.val (chargeSector Ψ s)=0 := by
  unfold chargeSector; split_ifs
  · rw [coordinatePolynomial,killSite_rename_injective _ Fin.val_injective,hz _ _ hs,map_zero]
  · exact map_zero _

theorem ChargeZero_of_sector {N : ℕ} (Ψ : State N) (h : ∀ s, chargeSector Ψ s=0) : ChargeZero Ψ := by
  intro s hs
  apply MvPolynomial.funext
  intro X
  have he := congrArg (eval (extendFinite 0 X)) (h (extendFinite Spin.zero s))
  have ht : natCharge N (extendFinite Spin.zero s)≠0 := by simpa only [natCharge_eq_fin,extendFinite_fin] using hs
  simpa only [chargeSector,ite_eq_left ht,map_zero,eval_coordinatePolynomial,liftState,liftPolyTensor,extendFinite_fin] using he

theorem chargeZero_of_cups {n : ℕ} (Ψ : State (n+4)) (ψ : State (n+2))
    (hex : LowerExchange (liftState Ψ) (n+4))
    (hc : ∀ i≤n+2, CupAt (liftState Ψ) (liftState ψ) (n+2) i)
    (hh : ChargeZero ψ) (hd : ∀ s i, (Ψ s).degreeOf i≤n+3)
    (hp : ∀ s i, s i=Spin.plus → (Ψ s).degreeOf i≤n+2)
    (hz : MinusZero Ψ) : ChargeZero Ψ := by
  apply ChargeZero_of_sector
  apply cup_vanishing_rigidity (m:=n+3) (by omega)
  · exact fun j hj => chargeSector_exchange Ψ hex j (by omega)
  · intro i hi X hX; exact chargeSector_cup Ψ ψ hc hh i (by omega) X hX
  · intro s j hj; exact chargeSector_degree Ψ s ⟨j,by omega⟩ (hd _ _)
  · intro s j hj hs
    exact (chargeSector_degree Ψ s ⟨j,by omega⟩ (hp _ ⟨j,by omega⟩ hs)).trans (by omega)
  · intro s j hj hs; exact chargeSector_minusZero Ψ hz s ⟨j,by omega⟩ hs

end PolynomialVacuumAlgebra

end OAI
