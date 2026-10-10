import Mathlib
import OAI.Combinatorics.StripMass.BlockPfaffian

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

def twoCons {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R) : Fin (n+2) → R :=
  Fin.cons x (Fin.cons y a)

@[simp] theorem twoCons_zero {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R) :
    twoCons x y a 0 = x := by simp [twoCons]

@[simp] theorem twoCons_one {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R) :
    twoCons x y a 1 = y := by
  rw [← Fin.succ_zero_eq_one]
  simp only [twoCons, Fin.cons_succ, Fin.cons_zero]

@[simp] theorem twoCons_succ_succ {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R) (i : Fin n) :
    twoCons x y a i.succ.succ = a i := by simp [twoCons]

theorem twoCons_of_ge {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R)
    (i : Fin (n+2)) (hi : 2 ≤ i.val) :
    twoCons x y a i = a ⟨i.val-2,by have := i.isLt; omega⟩ := by
  have he : i = (⟨i.val-2,by have := i.isLt; omega⟩ : Fin n).succ.succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  conv_lhs => rw [he]
  exact twoCons_succ_succ _ _ _ _

 

def augmentTwoIndex (n : ℕ) : Fin ((n+n%2)+2) ≃ Fin ((n+2)+(n+2)%2) :=
  finCongr (by omega)

@[simp] theorem augmentTwoIndex_val {n : ℕ} (i : Fin ((n+n%2)+2)) :
    (augmentTwoIndex n i).val = i.val := rfl

@[simp] theorem augmentTwoIndex_zero (n : ℕ) : augmentTwoIndex n 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem augmentTwoIndex_one (n : ℕ) : augmentTwoIndex n 1 = 1 := by
  apply Fin.ext
  simp [augmentTwoIndex, Nat.mod_eq_of_lt (by omega : 1 < n+2+n%2)]

theorem augmentedNumerator_skew {R : Type*} [CommRing R] {n : ℕ}
    (rr : R) (a : Fin n → R) :
    ∀ i j, augmentedNumerator rr a j i = -augmentedNumerator rr a i j := by
  intro i j
  unfold augmentedNumerator
  split_ifs <;> ring

@[simp] theorem augmentedNumerator_two_zero_one {R : Type*} [CommRing R] {n : ℕ}
    (rr x y : R) (a : Fin n → R) :
    augmentedNumerator rr (twoCons x y a) 0 1 = (x-y)*(x+y+rr) := by
  simp [augmentedNumerator, Nat.mod_eq_of_lt (by omega : 1 < n+2+n%2)]

@[simp] theorem augmentedDenominator_two_zero_one {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) :
    augmentedDenominator dd (twoCons x y a) 0 1 = discriminant dd x y := by
  simp [augmentedDenominator, Nat.mod_eq_of_lt (by omega : 1 < n+2+n%2)]

theorem augmentedNumerator_two_tail {R : Type*} [CommRing R] {n : ℕ}
    (rr x y : R) (a : Fin n → R) (i j : Fin (n+n%2)) :
    augmentedNumerator rr (twoCons x y a)
        (augmentTwoIndex n i.succ.succ) (augmentTwoIndex n j.succ.succ) =
      augmentedNumerator rr a i j := by
  simp only [augmentedNumerator, augmentTwoIndex_val, Fin.val_succ, Nat.add_assoc,
    Nat.reduceAdd, Nat.add_lt_add_iff_right]
  split_ifs <;> rfl

theorem augmentedDenominator_two_tail {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) (i j : Fin (n+n%2)) :
    augmentedDenominator dd (twoCons x y a)
        (augmentTwoIndex n i.succ.succ) (augmentTwoIndex n j.succ.succ) =
      augmentedDenominator dd a i j := by
  simp only [augmentedDenominator, augmentTwoIndex_val, Fin.val_succ, Nat.add_assoc,
    Nat.reduceAdd, Nat.add_lt_add_iff_right]
  split_ifs <;> rfl

 
theorem prod_pad_one {R : Type*} [CommMonoid R] {n m : ℕ} (h : n ≤ m)
    (f : Fin n → R) :
    (∏ i : Fin m, if hi : i.val < n then f ⟨i.val,hi⟩ else 1) = ∏ i : Fin n, f i := by
  classical
  symm
  apply Fintype.prod_of_injective (fun i : Fin n => i.castLE h) (Fin.castLE_injective h)
  · intro i hi
    split_ifs with hlt
    · exfalso
      exact hi ⟨⟨i.val,hlt⟩, Fin.ext rfl⟩
    · rfl
  · intro i
    simp only [Fin.val_castLE, i.isLt, dite_true]

theorem augmentedDenominator_two_zero_tail {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) (i : Fin (n+n%2)) :
    augmentedDenominator dd (twoCons x y a) 0 (augmentTwoIndex n i.succ.succ) =
      if hi : i.val < n then discriminant dd x (a ⟨i.val,hi⟩) else 1 := by
  simp only [augmentedDenominator, Fin.val_zero, augmentTwoIndex_val, Fin.val_succ,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_lt_add_iff_right]
  rw [dite_eq_left (by omega : 0 < n+2)]
  split_ifs <;> rfl

theorem augmentedDenominator_two_one_tail {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) (i : Fin (n+n%2)) :
    augmentedDenominator dd (twoCons x y a) 1 (augmentTwoIndex n i.succ.succ) =
      if hi : i.val < n then discriminant dd y (a ⟨i.val,hi⟩) else 1 := by
  have hv : (1 : Fin ((n+2)+(n+2)%2)).val = 1 := by
    change 1 % ((n+2)+(n+2)%2) = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [augmentedDenominator, hv, augmentTwoIndex_val, Fin.val_succ,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_lt_add_iff_right]
  rw [dite_eq_left (by omega : 1 < n+2)]
  split_ifs <;> rfl

theorem augmentedDenominator_two_cross {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) :
    (∏ i : Fin (n+n%2),
      augmentedDenominator dd (twoCons x y a) 0 (augmentTwoIndex n i.succ.succ) *
      augmentedDenominator dd (twoCons x y a) 1 (augmentTwoIndex n i.succ.succ)) =
      ∏ i : Fin n, discriminant dd x (a i) * discriminant dd y (a i) := by
  simp only [augmentedDenominator_two_zero_tail, augmentedDenominator_two_one_tail]
  have he : (fun i : Fin (n+n%2) =>
      (if hi : i.val < n then discriminant dd x (a ⟨i.val,hi⟩) else 1) *
      (if hi : i.val < n then discriminant dd y (a ⟨i.val,hi⟩) else 1)) =
      (fun i : Fin (n+n%2) => if hi : i.val < n then
        discriminant dd x (a ⟨i.val,hi⟩) * discriminant dd y (a ⟨i.val,hi⟩) else 1) := by
    funext i
    split_ifs <;> simp
  rw [he]
  exact prod_pad_one (n := n) (m := n+n%2) (Nat.le_add_right _ _)
    (fun i => discriminant dd x (a i) * discriminant dd y (a i))


 

 


 

theorem scalarNumerator_eval_cleared {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (a : Fin n → K) :
    MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) =
      clearedPfaffian (2^((n+n%2)/2) * (Nat.factorial ((n+n%2)/2) : K))⁻¹
        (augmentedNumerator (f rr) a) (augmentedDenominator (f dd) a) := by
  rw [scalarNumerator, map_clearedPfaffian, map_augmentedNumerator, map_augmentedDenominator]
  simp only [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    map_inv₀, map_mul, map_pow, map_ofNat, map_natCast]

theorem scalarNumerator_delete {K : Type*} [Field K] [CharZero K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (x y : K) (a : Fin n → K)
    (hzero : discriminant (f dd) x y = 0)
    (hD : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      discriminant (f dd) (twoCons x y a i) (twoCons x y a j) ≠ 0) :
    MvPolynomial.eval₂Hom f (twoCons x y a) (scalarNumerator (n+2) dd rr) =
      (x-y)*(x+y+f rr) * (∏ i : Fin n, discriminant (f dd) x (a i) * discriminant (f dd) y (a i)) *
        MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) := by
  let N : Matrix (Fin ((n+n%2)+2)) (Fin ((n+n%2)+2)) K := fun i j =>
    augmentedNumerator (f rr) (twoCons x y a) (augmentTwoIndex n i) (augmentTwoIndex n j)
  let D : Matrix (Fin ((n+n%2)+2)) (Fin ((n+n%2)+2)) K := fun i j =>
    augmentedDenominator (f dd) (twoCons x y a) (augmentTwoIndex n i) (augmentTwoIndex n j)
  have hN : ∀ i j, N j i = -N i j := fun i j =>
    augmentedNumerator_skew _ _ _ _
  have hDs : ∀ i j, D i j = D j i := fun i j =>
    augmentedDenominator_symm _ _ _ _
  have hD0 : D 0 1 = 0 := by simpa [D] using hzero
  have hDn : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) → D i j ≠ 0 := by
    intro i j hij hp
    change (if hi : i.val < n + 2 then
      if hj : j.val < n + 2 then
        discriminant (f dd) (twoCons x y a ⟨i.val, hi⟩) (twoCons x y a ⟨j.val, hj⟩)
      else 1 else 1) ≠ 0
    by_cases hi : i.val < n + 2
    · by_cases hj : j.val < n + 2
      · rw [dite_eq_left hi, dite_eq_left hj]
        apply hD
        · intro he
          exact hij (Fin.ext (congrArg (fun z : Fin (n+2) => z.val) he))
        · intro he
          apply hp
          simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one] at he ⊢
          omega
      · simpa only [dite_eq_left hi, dite_eq_right hj] using (one_ne_zero : (1 : K) ≠ 0)
    · simpa only [dite_eq_right hi] using (one_ne_zero : (1 : K) ≠ 0)
  have hs : (n+2)+(n+2)%2 = (n+n%2)+2 := by omega
  have ht : (2^(((n+2)+(n+2)%2)/2) * (Nat.factorial (((n+2)+(n+2)%2)/2) : K))⁻¹ =
      (2^(((n+n%2)+2)/2) * (Nat.factorial (((n+n%2)+2)/2) : K))⁻¹ := by rw [hs]
  have hc := clearedPfaffian_cast hs
    (2^(((n+2)+(n+2)%2)/2) * (Nat.factorial (((n+2)+(n+2)%2)/2) : K))⁻¹
      (augmentedNumerator (f rr) (twoCons x y a))
      (augmentedDenominator (f dd) (twoCons x y a))
  change clearedPfaffian _ N D = _ at hc
  rw [scalarNumerator_eval_cleared, ← hc, ht,
    clearedPfaffian_delete_even (by omega : (n+n%2)%2 = 0) N D hN hDs hD0 hDn]
  have hN01 : N 0 1 = (x-y)*(x+y+f rr) := by simp [N]
  have hcross : (∏ i : Fin (n+n%2), D 0 i.succ.succ * D 1 i.succ.succ) =
      ∏ i : Fin n, discriminant (f dd) x (a i) * discriminant (f dd) y (a i) := by
    simpa only [D, augmentTwoIndex_zero, augmentTwoIndex_one] using
      augmentedDenominator_two_cross (f dd) x y a
  rw [hN01, hcross]
  congr 1
  have htail : ∀ i j : Fin n, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0 := by
    intro i j hij
    have h := hD i.succ.succ j.succ.succ
      (by simpa only [ne_eq, Fin.succ_inj] using hij) (by simp)
    simpa only [twoCons_succ_succ] using h
  rw [scalarNumerator_eval f n dd rr a htail]
  congr 1
  · apply Finset.prod_congr rfl
    intro e _
    exact augmentedDenominator_two_tail _ _ _ _ _ _
  · congr 1
    funext i j
    dsimp [N,D]
    rw [augmentedNumerator_two_tail, augmentedDenominator_two_tail, ← augmentedKernel_eq]


 

 


theorem sourceVandermonde_twoCons {R : Type*} [CommRing R] {n : ℕ}
    (x y : R) (a : Fin n → R) :
    sourceVandermonde (twoCons x y a) =
      (x-y) * (∏ i : Fin n, (x-a i)*(y-a i)) * sourceVandermonde a := by
  unfold sourceVandermonde
  apply Eq.trans (prod_upperPair_two (fun i j => twoCons x y a i - twoCons x y a j))
  simp only [twoCons_zero,twoCons_one,twoCons_succ_succ]

 

theorem scalarPolynomial_delete_mul {K : Type*} [Field K] [CharZero K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) (x y : K) (a : Fin n → K)
    (hxy : x ≠ y) (ha : Function.Injective a)
    (hzero : discriminant (f dd) x y = 0)
    (hD : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      discriminant (f dd) (twoCons x y a i) (twoCons x y a j) ≠ 0) :
    (∏ i : Fin n, (x-a i)*(y-a i)) *
        MvPolynomial.eval₂Hom f (twoCons x y a) (scalarPolynomial (n+2) dd rr hdd) =
      (x+y+f rr) * (∏ i : Fin n, discriminant (f dd) x (a i) * discriminant (f dd) y (a i)) *
        MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have h := scalarNumerator_delete f n dd rr x y a hzero hD
  rw [scalarNumerator_eq_vandermonde (n+2) dd rr hdd,
    scalarNumerator_eq_vandermonde n dd rr hdd] at h
  simp only [map_mul, map_sourceVandermonde, MvPolynomial.eval₂Hom_X',
    sourceVandermonde_twoCons] at h
  apply mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.mpr hxy) (sourceVandermonde_ne_zero a ha))
  calc
    _ = ((x-y) * (∏ i : Fin n, (x-a i)*(y-a i)) * sourceVandermonde a) *
        MvPolynomial.eval₂Hom f (twoCons x y a) (scalarPolynomial (n+2) dd rr hdd) := by ring
    _ = _ := h
    _ = _ := by ring

 

theorem scalarPolynomial_delete_roots {K : Type*} [Field K] [CharZero K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) (x y γ σ : K) (a : Fin n → K)
    (ha : Function.Injective (twoCons x y a))
    (hxroot : ∀ z, discriminant (f dd) x z = (z-y)*(z-γ))
    (hyroot : ∀ z, discriminant (f dd) y z = (z-x)*(z-σ))
    (hD : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      discriminant (f dd) (twoCons x y a i) (twoCons x y a j) ≠ 0) :
    MvPolynomial.eval₂Hom f (twoCons x y a) (scalarPolynomial (n+2) dd rr hdd) =
      (x+y+f rr) * (∏ i : Fin n, (a i-γ)*(a i-σ)) *
        MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have hxy : x ≠ y := by
    simpa only [twoCons_zero,twoCons_one] using ha.ne (Fin.zero_ne_one (n := n))
  have hai : Function.Injective a := by
    intro i j he
    have hs := ha (show twoCons x y a i.succ.succ = twoCons x y a j.succ.succ by simpa using he)
    simpa only [Fin.succ_inj] using hs
  have hx : ∀ i, x-a i ≠ 0 := by
    intro i
    apply sub_ne_zero.mpr
    simpa only [twoCons_zero,twoCons_succ_succ] using ha.ne (Fin.succ_ne_zero i.succ).symm
  have hy : ∀ i, y-a i ≠ 0 := by
    intro i
    apply sub_ne_zero.mpr
    simpa only [twoCons_one,twoCons_succ_succ] using ha.ne (Fin.succ_succ_ne_one i).symm
  have hA : (∏ i : Fin n, (x-a i)*(y-a i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => mul_ne_zero (hx i) (hy i))
  have h := scalarPolynomial_delete_mul f n dd rr hdd x y a hxy hai (by simp [hxroot]) hD
  have hB : (∏ i : Fin n, discriminant (f dd) x (a i) * discriminant (f dd) y (a i)) =
      (∏ i : Fin n, (x-a i)*(y-a i)) * ∏ i : Fin n, (a i-γ)*(a i-σ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [hxroot,hyroot]
    ring
  rw [hB] at h
  apply mul_left_cancel₀ hA
  calc
    _ = _ := h
    _ = _ := by ring

end

 

 

noncomputable section

@[simp] theorem cos_six_lambda : Real.cos (6*lambda) = -d := by
  have h : 6*lambda = Real.pi-2*lambda := by simp [lambda]; ring
  rw [h,Real.cos_pi_sub]
  rfl

@[simp] theorem sin_six_lambda : Real.sin (6*lambda) = d := by
  have h : 6*lambda = Real.pi-2*lambda := by simp [lambda]; ring
  rw [h,Real.sin_pi_sub]
  have h2 : 2*lambda = Real.pi/4 := by simp [lambda]; ring
  rw [h2,d,h2,Real.sin_pi_div_four,Real.cos_pi_div_four]

theorem d_sq : d^2 = 1/2 := by
  have h2 : 2*lambda = Real.pi/4 := by simp [lambda]; ring
  rw [d,h2,Real.cos_pi_div_four,div_pow]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem d_ne_zero : d ≠ 0 := by
  intro h
  have := d_sq
  rw [h] at this
  norm_num at this

 
theorem discriminant_cosine_roots (w z : ℝ) :
    discriminant d (Real.cos w) z =
      (z-Real.cos (w-6*lambda))*(z-Real.cos (w+6*lambda)) := by
  rw [Real.cos_sub,Real.cos_add,cos_six_lambda,sin_six_lambda]
  unfold discriminant
  have hw := Real.sin_sq_add_cos_sq w
  nlinarith [sq_nonneg (Real.cos w),d_sq]

 
theorem discriminant_cosine_roots_complex (w : ℝ) (z : ℂ) :
    discriminant (d:ℂ) (Real.cos w) z =
      (z-(Real.cos (w-6*lambda):ℂ))*(z-(Real.cos (w+6*lambda):ℂ)) := by
  have hs : (Real.cos (w-6*lambda):ℂ) + (Real.cos (w+6*lambda):ℂ) =
      -2*(d:ℂ)*(Real.cos w:ℂ) := by
    rw [Real.cos_sub,Real.cos_add,cos_six_lambda,sin_six_lambda]
    push_cast
    ring
  have hp : (Real.cos (w-6*lambda):ℂ)*(Real.cos (w+6*lambda):ℂ) =
      (Real.cos w:ℂ)^2-(d:ℂ)^2 := by
    have h := discriminant_cosine_roots w 0
    have hr : Real.cos (w-6*lambda)*Real.cos (w+6*lambda) = Real.cos w^2-d^2 := by
      simpa [discriminant] using h.symm
    exact_mod_cast hr
  unfold discriminant
  linear_combination z*hs-hp

 

theorem scalarPolynomial_delete_cosine (n : ℕ) (w : ℝ) (a : Fin n → ℂ)
    (ha : Function.Injective (twoCons (Real.cos w:ℂ) (Real.cos (w+6*lambda):ℂ) a))
    (hD : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      discriminant (d:ℂ) (twoCons (Real.cos w:ℂ) (Real.cos (w+6*lambda):ℂ) a i)
        (twoCons (Real.cos w:ℂ) (Real.cos (w+6*lambda):ℂ) a j) ≠ 0) :
    MvPolynomial.eval (twoCons (Real.cos w:ℂ) (Real.cos (w+6*lambda):ℂ) a)
        (scalarPolynomial (n+2) d rho (by exact_mod_cast d_ne_zero)) =
      ((Real.cos w:ℂ)+(Real.cos (w+6*lambda):ℂ)+(rho:ℂ)) *
        (∏ i : Fin n, (a i-(Real.cos (w-6*lambda):ℂ))*(a i-(Real.cos (w+12*lambda):ℂ))) *
          MvPolynomial.eval a (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero)) := by
  apply scalarPolynomial_delete_roots (RingHom.id ℂ) n d rho _ _ _ _ _ a ha
  · intro z
    simpa only [RingHom.id_apply,mul_comm] using discriminant_cosine_roots_complex w z
  · intro z
    have h1 : w+6*lambda-6*lambda = w := by ring
    have h2 : w+6*lambda+6*lambda = w+12*lambda := by ring
    simpa only [RingHom.id_apply,h1,h2] using discriminant_cosine_roots_complex (w+6*lambda) z
  · exact hD


 

 

open Finset
open scoped Classical

 

def LastDegree {K : Type*} [CommRing K] {n : ℕ} (m : ℕ)
    (P : Pairing (n+1) → Polynomial K) : Prop :=
  ∀ p k, (if p.Occupied (Fin.last n) then m ≤ k else m < k) → (P p).coeff k = 0

theorem lastTransform_coeff_succ {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (q : Pairing (n+1)) (k : ℕ) :
    (lastTransform w d c C P q).coeff (k+1) = ∑ p, lastCoefficient w q p *
      (if q.Occupied (Fin.last n) then
        if p.Occupied (Fin.last n) then (P p).coeff k - c * (P p).coeff (k+1)
        else (2*d) * (P p).coeff (k+1)
      else if p.Occupied (Fin.last n) then d * ((P p).coeff k - c * (P p).coeff (k+1))
        else (P p).coeff k + C * (P p).coeff (k+1)) := by
  classical
  simp only [lastTransform, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Occupied (Fin.last n) <;> by_cases hq : q.Occupied (Fin.last n)
  all_goals simp [lastFactor, hp, hq, mul_add, mul_sub, add_mul, sub_mul,
    mul_assoc, Polynomial.coeff_C_mul]

theorem lastTransform_degree {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) {m : ℕ} (hP : LastDegree m P) :
    LastDegree (m+1) (lastTransform w d c C P) := by
  classical
  intro q k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := by
    by_cases hq : q.Occupied (Fin.last n) <;> simp only [hq, ite_true, ite_false] at hk <;>
      exact ⟨k-1, by omega⟩
  rw [lastTransform_coeff_succ]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hq : q.Occupied (Fin.last n) <;> by_cases hp : p.Occupied (Fin.last n)
  all_goals simp only [hq, hp, ite_true, ite_false] at hk ⊢
  all_goals have h₁ : (P p).coeff (j+1) = 0 := hP p (j+1) (by simp [hp]; omega)
  · have h₀ : (P p).coeff j = 0 := hP p j (by simp [hp]; omega)
    simp [h₀, h₁]
  · simp [h₁]
  · have h₀ : (P p).coeff j = 0 := hP p j (by simp [hp]; omega)
    simp [h₀, h₁]
  · have h₀ : (P p).coeff j = 0 := hP p j (by simp [hp]; omega)
    simp [h₀, h₁]

theorem Pairing.padTop_injective {n : ℕ} : Function.Injective (@Pairing.padTop n) := by
  intro p q h
  have := congrArg (fun r => r.restrict Fin.castSuccOrderEmb) h
  simpa [Pairing.padTop, Pairing.restrict_map] using this

 

theorem lastTransform_leading {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) {m : ℕ} (hP : LastDegree m P)
    (q : Pairing n) :
    (lastTransform w d c C P q.padTop).coeff (m+1) =
      (rawColumn w).mulVec (fun p => (P p.padTop).coeff m) q := by
  classical
  rw [lastTransform_coeff_succ]
  simp only [Pairing.padTop_not_occupied_last, ite_false, Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padTop Pairing.padTop_injective
  · intro p hp
    have hp' : p.Occupied (Fin.last n) := by
      by_contra h
      exact hp ⟨p.restrict Fin.castSuccOrderEmb, Pairing.padTop_restrict p h⟩
    have h₀ := hP p m (by simp [hp'])
    have h₁ := hP p (m+1) (by simp [hp'])
    simp [hp', h₀, h₁]
  · intro p
    have h₁ := hP p.padTop (m+1) (by simp)
    simp [lastCoefficient_padTop, h₁]

end

 

 

noncomputable section
open Finset
open scoped Classical

 

def deletionNode {n : ℕ} (i : Fin n) : SpectralField n :=
  variableF i * constF n phase ^ 3

def deletionBeta {n : ℕ} (i : Fin n) : SpectralField n :=
  torusCos (deletionNode i ^ 2 / constF n phase ^ 3)

def nodalWeights {n : ℕ} (i : Fin n) : Fin (n+1) → Weights (SpectralField n) :=
  Fin.snoc (spectralWeights n) (torusWeights (constF n phase ^ 3 / deletionNode i))

 

def nodalScalar {n : ℕ} (i : Fin n) : SpectralField n :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
    (Fin.snoc spectralA (deletionBeta i))
      (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))

def nodalVacuum {n : ℕ} (i : Fin n) (p : Pairing (n+1)) : SpectralField n :=
  nodalScalar i * normalizedVacuum (nodalWeights i) p

 

def rationalVacuum (n : ℕ) (p : Pairing n) : SpectralField n :=
  spectralNormalization n * normalizedVacuum (spectralWeights n) p

 

def rationalNodalPolynomial (n : ℕ) (p : Pairing (n+1)) : Polynomial (SpectralField n) :=
  if p.Occupied (Fin.last n) then
    Lagrange.interpolate univ deletionBeta
      (fun i => nodalVacuum i p / torusSin (deletionNode i))
  else
    Polynomial.C (rationalVacuum n (p.restrict Fin.castSuccOrderEmb)) *
      Lagrange.nodal univ deletionBeta +
        Lagrange.interpolate univ deletionBeta (fun i => nodalVacuum i p)

 

def rationalInterpolant (n : ℕ) (p : Pairing (n+1)) : SpectralField (n+1) :=
  (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1) *
    (rationalNodalPolynomial n p).eval₂ (liftSpectral n) (spectralA (Fin.last n))

 

def rationalInterpolationResidual (n : ℕ) (p : Pairing (n+1)) : SpectralField (n+1) :=
  (∏ i : Fin (n+1), evalLaurent (rowDenominator i)) *
    (((column (spectralWeights (n+1))).mulVec (rationalInterpolant n)) p -
      rationalInterpolant n p)

end
end CriticalStrip.Diagram

end OAI
