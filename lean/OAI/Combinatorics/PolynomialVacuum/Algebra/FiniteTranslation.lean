import OAI.Combinatorics.PolynomialVacuum.Algebra.AllSizeInduction

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

@[simp] theorem liftState_extend {N : ℕ} (ψ : State N) (X : Fin N → ℂ) (s : Fin N → Spin) :
    liftState ψ (extendFinite 0 X) (extendFinite Spin.zero s)=eval X (ψ s) := by
  simp only [liftState,liftPolyTensor,extendFinite_fin]

theorem finite_minus_zero {N : ℕ} (ψ : State N) (hz : MinusZero ψ)
    (s : Fin N → Spin) (i : Fin N) (X : Fin N → ℂ) (hs : s i=Spin.minus) (hX : X i=0) :
    eval X (ψ s)=0 := by
  have he := congrArg (eval X) (hz s i hs)
  have hsub : @Function.update (Fin N) (fun _ => ℂ) (Classical.decEq _) X i 0=X := by
    funext j
    simp only [Function.update_apply]
    split_ifs with h
    · subst j; exact hX.symm
    · rfl
  simpa only [eval_killSite,hsub,map_zero] using he

theorem finite_exchange {n : ℕ} (ψ : State (n+2)) (hex : LowerExchange (liftState ψ) (n+2))
    (i : Fin (n+1)) (s : Fin (n+2) → Spin) (X : Fin (n+2) → ℂ) :
    (∑ ab : Pair, exchangeNumerator (X (pairLeft i)) (X (pairRight i)) (s (pairLeft i),s (pairRight i)) ab *
      eval X (ψ (Function.update (Function.update s (pairLeft i) ab.1) (pairRight i) ab.2))) =
    exchangeDenominator (X (pairLeft i)) (X (pairRight i)) *
      eval (X ∘ Equiv.swap (pairLeft i) (pairRight i)) (ψ s) := by
  have he := congrFun (hex i.val (by have:=i.isLt; omega) (extendFinite 0 X)) (extendFinite Spin.zero s)
  change (∑ ab : Pair, exchangeNumerator (extendFinite 0 X i.val) (extendFinite 0 X (i.val+1))
    (extendFinite Spin.zero s i.val,extendFinite Spin.zero s (i.val+1)) ab *
    liftState ψ (extendFinite 0 X) (replacePair (extendFinite Spin.zero s) i.val (i.val+1) ab)) =
    exchangeDenominator (extendFinite 0 X i.val) (extendFinite 0 X (i.val+1))*
    liftState ψ (swapSite i.val (extendFinite 0 X)) (extendFinite Spin.zero s) at he
  have hswap : (fun j : Fin (n+2) => swapSite i.val (extendFinite 0 X) j.val)=X ∘ Equiv.swap (pairLeft i) (pairRight i) := by
    funext j
    simp only [swapSite,Function.comp_apply,Equiv.swap_apply_def,Fin.ext_iff,pairLeft,pairRight,Fin.val_castSucc,Fin.val_succ]
    split_ifs
    · exact extendFinite_fin 0 X i.succ
    · exact extendFinite_fin 0 X i.castSucc
    · exact extendFinite_fin 0 X j
  change (∑ ab : Pair, exchangeNumerator (extendFinite 0 X (pairLeft i).val) (extendFinite 0 X (pairRight i).val)
    (extendFinite Spin.zero s (pairLeft i).val,extendFinite Spin.zero s (pairRight i).val) ab *
    eval (fun j : Fin (n+2) => extendFinite 0 X j.val)
      (ψ (fun j : Fin (n+2) => replacePair (extendFinite Spin.zero s) (pairLeft i).val (pairRight i).val ab j.val))) =
    exchangeDenominator (extendFinite 0 X (pairLeft i).val) (extendFinite 0 X (pairRight i).val)*
    eval (fun j : Fin (n+2) => swapSite i.val (extendFinite 0 X) j.val)
      (ψ (fun j : Fin (n+2) => extendFinite Spin.zero s j.val)) at he
  simpa only [replacePair_restrict,extendFinite_fin,hswap] using he

theorem rotationIndex_finite (n : ℕ) (j : Fin (n+1)) :
    rotationIndex n j.val=((finRotate (n+1)).symm j).val := by
  by_cases hj : j=0
  · subst j
    have h : (finRotate (n+1)).symm 0=Fin.last n := (Equiv.symm_apply_eq _).mpr finRotate_last.symm
    rw [h]; simp [rotationIndex]
  · rw [coe_finRotate_symm_of_ne_zero hj]
    simp [rotationIndex,show j.val≠0 from by intro h; exact hj (Fin.ext h)]

theorem natRotate_extend {α : Type*} {n : ℕ} (a : α) (X : Fin (n+1) → α) :
    (fun j : Fin (n+1) => natRotate n (extendFinite a X) j.val)=X ∘ (finRotate (n+1)).symm := by
  funext j
  simp only [natRotate,Function.comp_apply,rotationIndex_finite,extendFinite_fin]

theorem finite_cyclic {n : ℕ} (ψ : State (n+1)) (hcy : NaturalCyclic n (liftState ψ))
    (s : Fin (n+1) → Spin) (X : Fin (n+1) → ℂ) :
    zeta^charge (s 0)*eval X (ψ (s ∘ finRotate (n+1))) =
      eval (X ∘ (finRotate (n+1)).symm) (ψ s) := by
  have he := congrFun (hcy (extendFinite 0 X)) (extendFinite Spin.zero (s ∘ finRotate (n+1)))
  change zeta ^ (-charge (extendFinite Spin.zero (s ∘ finRotate (n+1)) n))*
    liftState ψ (natRotate n (extendFinite 0 X)) (natRotate n (extendFinite Spin.zero (s ∘ finRotate (n+1)))) =
    liftState ψ (extendFinite 0 X) (extendFinite Spin.zero (s ∘ finRotate (n+1))) at he
  have hlast : extendFinite Spin.zero (s ∘ finRotate (n+1)) n=s 0 := by
    change extendFinite Spin.zero (s ∘ finRotate (n+1)) (Fin.last n).val=s 0
    simp only [extendFinite_fin,Function.comp_apply,finRotate_last]
  rw [hlast] at he
  simp only [liftState,liftPolyTensor,natRotate_extend,extendFinite_fin,
    Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] at he
  change zeta ^ (-charge (s 0))*eval (X ∘ (finRotate (n+1)).symm) (ψ s)=eval X (ψ (s ∘ finRotate (n+1))) at he
  rw [← he,← mul_assoc,← zpow_add₀ (by exact pow_ne_zero _ (pow_ne_zero _ q_ne_zero) : zeta≠0)]
  simp

theorem skipTwo_extend {α : Type*} {n : ℕ} (a : α) (X : Fin (n+2) → α) (i : Fin (n+1)) :
    (fun j : Fin n => skipTwo i.val (extendFinite a X) j.val)=X ∘ omitPair i := by
  funext j
  simp only [skipTwo,Function.comp_apply,omitPair]
  have hj : j.val<n+2 := by omega
  have hj2 : j.val+2<n+2 := by omega
  split_ifs <;> simp [extendFinite,hj,hj2]

theorem naturalFusion_finite {n : ℕ} (X : Fin (n+2) → ℂ) (i : Fin (n+1)) :
    naturalFusion n i.val (extendFinite 0 X)=fusionScalar (X (pairLeft i)) (X ∘ omitPair i) := by
  unfold naturalFusion fusionProduct fusionScalar
  rw [← Fin.prod_univ_eq_prod_range]
  have hi : i.val=(pairLeft i).val := rfl
  simp only [hi,extendFinite_fin]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have he := congrFun (skipTwo_extend 0 X i) j
  change (skipTwo i.val (extendFinite 0 X) j.val-t^5*X (pairLeft i))*
    (skipTwo i.val (extendFinite 0 X) j.val-t^6*X (pairLeft i))=_
  rw [he]

theorem finite_cup {n : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i)
    (i : Fin (n+1)) (s : Fin (n+2) → Spin) (X : Fin (n+2) → ℂ)
    (hX : X (pairRight i)=T*X (pairLeft i)) :
    eval X (Ψ s)=fusionScalar (X (pairLeft i)) (X ∘ omitPair i)*
      cup (s (pairLeft i),s (pairRight i))*eval (X ∘ omitPair i) (ψ (s ∘ omitPair i)) := by
  have hXi : extendFinite 0 X (i.val+1)=T*extendFinite 0 X i.val := by
    change extendFinite 0 X (pairRight i).val=T*extendFinite 0 X (pairLeft i).val
    simpa only [extendFinite_fin] using hX
  have he := congrFun (hc i.val (by have:=i.isLt; omega) (extendFinite 0 X) hXi) (extendFinite Spin.zero s)
  change liftState Ψ (extendFinite 0 X) (extendFinite Spin.zero s)=
    naturalFusion n i.val (extendFinite 0 X)*(cup (extendFinite Spin.zero s (pairLeft i).val,
      extendFinite Spin.zero s (pairRight i).val)*liftState ψ (skipTwo i.val (extendFinite 0 X))
      (skipTwo i.val (extendFinite Spin.zero s))) at he
  simpa only [liftState_extend,naturalFusion_finite,extendFinite_fin,liftState,liftPolyTensor,skipTwo_extend,mul_assoc] using he

theorem finite_lastZero {n : ℕ} (Ψ : State (n+1)) (ψ : State n)
    (hz : LastZeroReduction (liftState Ψ) (liftState ψ) n)
    (s : Fin (n+1) → Spin) (X : Fin (n+1) → ℂ)
    (hs : s (Fin.last n)=Spin.zero) (hX : X (Fin.last n)=0) :
    eval X (Ψ s)=(∏ j : Fin n, X j.castSucc)*eval (X ∘ Fin.castSucc) (ψ (s ∘ Fin.castSucc)) := by
  have hsn : extendFinite Spin.zero s n=Spin.zero := by
    change extendFinite Spin.zero s (Fin.last n).val=Spin.zero
    simpa only [extendFinite_fin] using hs
  have hXn : extendFinite 0 X n=0 := by
    change extendFinite 0 X (Fin.last n).val=0
    simpa only [extendFinite_fin] using hX
  have he := hz (extendFinite 0 X) (extendFinite Spin.zero s) hXn (by rw [hsn]; decide)
  rw [hsn,ite_eq_left rfl,liftState_extend] at he
  simp only [prefixProduct,← Fin.prod_univ_eq_prod_range,liftState,liftPolyTensor] at he
  simpa only [Function.comp_def, show ∀ j : Fin n, extendFinite 0 X j.val=X j.castSucc from fun j => extendFinite_fin 0 X j.castSucc,
    show ∀ j : Fin n, extendFinite Spin.zero s j.val=s j.castSucc from fun j => extendFinite_fin Spin.zero s j.castSucc] using he

end PolynomialVacuumAlgebra

end OAI
