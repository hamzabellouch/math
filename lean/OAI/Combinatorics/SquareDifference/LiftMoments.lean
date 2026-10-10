import OAI.Combinatorics.SquareDifference.DualCoordinates

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate

namespace LiftTheory

open Finset

open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

lemma sum_range_two (n : ℕ) (f : ℕ → ℝ) :
    (∑ k∈range (2*n), f k)=∑ k∈range n, (f (2*k)+f (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, sum_range_succ, sum_range_succ,
      ih, sum_range_succ]
    ring

lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2^n := by
  by_cases h : k ≤ n
  · rw [← Nat.sum_range_choose]
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

lemma even_sum_binomial (r : ℕ) (a b : ℝ) :
    ((a+b)^(2*r)+(a-b)^(2*r))/2 =
      ∑ k∈range (r+1), (↑((2*r).choose (2*k)) : ℝ)*(a^2)^(r-k)*(b^2)^k := by
  have he (x : ℝ) : (a+x)^(2*r) =
      ∑ i∈range (2*(r+1)), a^(2*r-i)*x^i*↑((2*r).choose i) := by
    rw [show 2*(r+1)=(2*r+1)+1 by omega, sum_range_succ]
    simp only [Nat.choose_eq_zero_of_lt (by omega : 2*r < 2*r+1), Nat.cast_zero,
      mul_zero, add_zero]
    calc
      _ = (x+a)^(2*r) := by rw [add_comm]
      _ = _ := add_pow x a (2*r)
      _ = _ := sum_congr rfl fun i _ => by ring
  rw [sub_eq_add_neg, he b, he (-b), ← sum_add_distrib, sum_range_two]
  rw [sum_div]
  apply sum_congr rfl
  intro k hk
  have hodd : (-b)^(2*k+1) = -(b^(2*k+1)) := by
    have hv : (-b)^(2*k)=b^(2*k) := by rw [pow_mul, pow_mul, neg_sq]
    rw [pow_succ, pow_succ, hv]
    ring
  have heven : (-b)^(2*k)=b^(2*k) := by rw [pow_mul, pow_mul, neg_sq]
  have hpow : a^(2*r-2*k)=(a^2)^(r-k) := by
    rw [← pow_mul, Nat.mul_sub_left_distrib]
  rw [heven, hodd, hpow, pow_mul b 2 k]
  ring

lemma two_point_moment (r : ℕ) (_hr : 1 ≤ r) (a b : ℝ) :
    ((a+b)^(2*r)+(a-b)^(2*r))/2 ≤ (a^2+(2:ℝ)^(2*r)*b^2)^r := by
  rw [even_sum_binomial]
  rw [add_comm (a^2), add_pow]
  apply sum_le_sum
  intro k hk
  have hkr : k ≤ r := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  have hcoef : (↑((2*r).choose (2*k)) : ℝ) ≤ (2:ℝ)^(2*r*k)*↑(r.choose k) := by
    by_cases hz : k=0
    · simp [hz]
    · have hk1 : 1 ≤ k := by omega
      have hb : (↑((2*r).choose (2*k)) : ℝ) ≤ (2:ℝ)^(2*r) := by
        exact_mod_cast choose_le_two_pow (2*r) (2*k)
      have hc : (1:ℝ) ≤ ↑(r.choose k) := by exact_mod_cast Nat.choose_pos hkr
      have hp : (2:ℝ)^(2*r) ≤ (2:ℝ)^(2*r*k) := by
        apply pow_le_pow_right₀ (by norm_num)
        nlinarith
      exact hb.trans (hp.trans (le_mul_of_one_le_right (by positivity) hc))
  have ha2 := sq_nonneg a
  have hb2 := sq_nonneg b
  calc
    _ ≤ ((2:ℝ)^(2*r*k)*↑(r.choose k))*(a^2)^(r-k)*(b^2)^k := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

lemma expect_pow_zero {X : Type*} [Fintype X] (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (r : ℕ) (_hr : 1 ≤ r)
    (h : (𝔼 x, f x^r) ≤ 0) : ∀ x, f x=0 := by
  have hz : (𝔼 x, f x^r)=0 := le_antisymm h (expect_nonneg (fun x _ => pow_nonneg (hf x) _))
  have hh := (expect_eq_zero_iff_of_nonneg (fun x _ => pow_nonneg (hf x) r)).mp hz
  intro x
  by_contra hne
  exact pow_ne_zero r hne (hh x (mem_univ x))

lemma expect_add_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (r : ℕ) (hr : 1 ≤ r) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : (𝔼 x, f x^r) ≤ A^r) (hb : (𝔼 x, g x^r) ≤ B^r) :
    (𝔼 x, (f x+g x)^r) ≤ (A+B)^r := by
  by_cases hAz : A=0
  · have hz : ∀ x, f x=0 := expect_pow_zero f hf r hr (by rw [hAz, zero_pow (by omega : r≠0)] at ha; exact ha)
    simpa only [hz, hAz, zero_add] using hb
  by_cases hBz : B=0
  · have hz : ∀ x, g x=0 := expect_pow_zero g hg r hr (by rw [hBz, zero_pow (by omega : r≠0)] at hb; exact hb)
    simpa only [hz, hBz, add_zero] using ha
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
  have hAB : 0 < A+B := add_pos hAp hBp
  have hpoint (x : X) : ((f x+g x)/(A+B))^r ≤
      (A/(A+B))*(f x/A)^r+(B/(A+B))*(g x/B)^r := by
    have hc := (convexOn_pow (𝕜 := ℝ) r).2
      (show f x/A∈Set.Ici 0 from div_nonneg (hf x) hA)
      (show g x/B∈Set.Ici 0 from div_nonneg (hg x) hB)
      (show 0 ≤ A/(A+B) from by positivity) (show 0 ≤ B/(A+B) from by positivity)
      (show A/(A+B)+B/(A+B)=1 from by field_simp)
    simp only [smul_eq_mul] at hc
    have he : A/(A+B)*(f x/A)+B/(A+B)*(g x/B)=(f x+g x)/(A+B) := by field_simp
    rwa [he] at hc
  have hmean : (𝔼 x, ((f x+g x)/(A+B))^r) ≤ 1 := by
    calc
      _ ≤ (𝔼 x, (A/(A+B)*(f x/A)^r+B/(A+B)*(g x/B)^r)) :=
        expect_le_expect fun x _ => hpoint x
      _ = A/(A+B)*((𝔼 x, f x^r)/A^r)+B/(A+B)*((𝔼 x, g x^r)/B^r) := by
        simp only [expect_add_distrib, div_pow]
        simp only [div_eq_mul_inv, ← mul_expect, ← expect_mul]
      _ ≤ A/(A+B)*(A^r/A^r)+B/(A+B)*(B^r/B^r) := by gcongr
      _ = 1 := by rw [div_self (pow_ne_zero _ hAz), div_self (pow_ne_zero _ hBz)]; field_simp
  have he : (𝔼 x, ((f x+g x)/(A+B))^r)=(𝔼 x, (f x+g x)^r)/(A+B)^r := by
    simp only [div_pow]
    simp only [div_eq_mul_inv, ← expect_mul]
  rw [he] at hmean
  exact (div_le_one (pow_pos hAB _)).mp hmean

lemma expect_update_bool {J : Type*} [Fintype J] [DecidableEq J]
    (j : J) (f : (J → Bool) → ℝ) :
    (𝔼 x : J → Bool, 𝔼 t : Bool, f (Function.update x j t))=𝔼 x, f x := by
  let e : ((J → Bool) × Bool) ≃ ((J → Bool) × Bool) :=
    { toFun := fun a => (Function.update a.1 j a.2, a.1 j)
      invFun := fun a => (Function.update a.1 j a.2, a.1 j)
      left_inv := by rintro ⟨x,t⟩; simp
      right_inv := by rintro ⟨x,t⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (J → Bool) × Bool => f (Function.update a.1 j a.2))
    (fun a : (J → Bool) × Bool => f a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [Fintype.expect_const] using he

lemma expect_bool (f : Bool → ℝ) : (𝔼 b, f b)=(f true+f false)/2 := by
  simp [expect_eq_sum_div_card]

def boolSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def walsh {J : Type*} [DecidableEq J] (s : Finset J)
    (c : Finset J → ℝ) (x : J → Bool) : ℝ :=
  ∑ U∈s.powerset, c U*∏ j∈U, boolSign (x j)

noncomputable def walshEnergy {J : Type*} [DecidableEq J] (s : Finset J)
    (C : ℝ) (c : Finset J → ℝ) : ℝ := ∑ U∈s.powerset, C^U.card*(c U)^2

lemma walsh_update {J : Type*} [DecidableEq J] (s : Finset J) (c : Finset J → ℝ)
    (x : J → Bool) (j : J) (hj : j∉s) (t : Bool) :
    walsh s c (Function.update x j t)=walsh s c x := by
  apply sum_congr rfl
  intro U hU
  congr 1
  apply prod_congr rfl
  intro k hk
  rw [Function.update_of_ne]
  intro h
  subst k
  exact hj ((mem_powerset.mp hU) hk)

lemma walsh_insert {J : Type*} [DecidableEq J] (s : Finset J) (c : Finset J → ℝ)
    (x : J → Bool) (j : J) (hj : j∉s) :
    walsh (insert j s) c x=walsh s c x+boolSign (x j)*walsh s (fun U => c (insert j U)) x := by
  unfold walsh
  rw [sum_powerset_insert hj, mul_sum]
  congr 1
  apply sum_congr rfl
  intro U hU
  have hjU : j∉U := fun h => hj ((mem_powerset.mp hU) h)
  rw [prod_insert hjU]
  ring

lemma walshEnergy_insert {J : Type*} [DecidableEq J] (s : Finset J)
    (C : ℝ) (c : Finset J → ℝ) (j : J) (hj : j∉s) :
    walshEnergy (insert j s) C c=walshEnergy s C c+C*walshEnergy s C (fun U => c (insert j U)) := by
  unfold walshEnergy
  rw [sum_powerset_insert hj, mul_sum]
  congr 1
  apply sum_congr rfl
  intro U hU
  have hjU : j∉U := fun h => hj ((mem_powerset.mp hU) h)
  rw [card_insert_of_notMem hjU, pow_succ]
  ring

lemma walshEnergy_nonneg {J : Type*} [DecidableEq J] (s : Finset J)
    (C : ℝ) (hC : 0 ≤ C) (c : Finset J → ℝ) : 0 ≤ walshEnergy s C c :=
  sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hC _) (sq_nonneg _)

lemma walsh_hypercontractivity {J : Type*} [Fintype J] [DecidableEq J]
    (s : Finset J) (c : Finset J → ℝ) (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x : J → Bool, (walsh s c x)^(2*r)) ≤ (walshEnergy s ((2:ℝ)^(2*r)) c)^r := by
  induction s using Finset.induction_on generalizing c with
  | empty => simp [walsh, walshEnergy, pow_mul]
  | @insert j s hj ih =>
    let C : ℝ := (2:ℝ)^(2*r)
    let a := walsh s c
    let b := walsh s (fun U => c (insert j U))
    let A := walshEnergy s C c
    let B := walshEnergy s C (fun U => c (insert j U))
    have hC : 0 ≤ C := by positivity
    have hA : 0 ≤ A := walshEnergy_nonneg _ _ hC _
    have hB : 0 ≤ B := walshEnergy_nonneg _ _ hC _
    have ha : (𝔼 x, (a x^2)^r) ≤ A^r := by
      simpa only [a, A, C, ← pow_mul] using ih c
    have hb : (𝔼 x, (C*b x^2)^r) ≤ (C*B)^r := by
      simp only [mul_pow, ← mul_expect]
      exact mul_le_mul_of_nonneg_left (by simpa only [b, B, C, ← pow_mul] using ih (fun U => c (insert j U))) (by positivity)
    have hm := expect_add_pow_le (fun x => a x^2) (fun x => C*b x^2)
      (fun x => sq_nonneg _) (fun x => mul_nonneg hC (sq_nonneg _)) r hr A (C*B)
      hA (mul_nonneg hC hB) ha hb
    rw [walshEnergy_insert s _ c j hj]
    change _ ≤ (A+C*B)^r
    apply le_trans _ hm
    rw [← expect_update_bool j]
    apply expect_le_expect
    intro x _
    rw [expect_bool]
    simp only [walsh_insert s c _ j hj, walsh_update s c x j hj,
      walsh_update s (fun U => c (insert j U)) x j hj, Function.update_self]
    simp only [boolSign, Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul]
    simp only [← sub_eq_add_neg]
    exact two_point_moment r hr (a x) (b x)

lemma expect_update_dep {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (j : J) (f : (∀ j, X j) → ℝ) :
    (𝔼 x : ∀ j, X j, 𝔼 t : X j, f (Function.update x j t))=𝔼 x, f x := by
  let e : ((∀ j, X j) × X j) ≃ ((∀ j, X j) × X j) :=
    { toFun := fun a => (Function.update a.1 j a.2, a.1 j)
      invFun := fun a => (Function.update a.1 j a.2, a.1 j)
      left_inv := by rintro ⟨x,t⟩; simp
      right_inv := by rintro ⟨x,t⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (∀ j, X j) × X j => f (Function.update a.1 j a.2))
    (fun a : (∀ j, X j) × X j => f a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [Fintype.expect_const] using he

def patch {J : Type*} [DecidableEq J] {X : J → Type*}
    (s : Finset J) (x y : ∀ j, X j) (j : J) : X j := if j∈s then y j else x j

lemma patch_empty {J : Type*} [DecidableEq J] {X : J → Type*} (x y : ∀ j, X j) :
    patch ∅ x y=x := by ext j; simp [patch]

lemma patch_univ {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} (x y : ∀ j, X j) : patch univ x y=y := by ext j; simp [patch]

lemma patch_insert_update {J : Type*} [DecidableEq J] {X : J → Type*}
    (s : Finset J) (j : J) (_hj : j∉s) (x y : ∀ j, X j) (t : X j) :
    patch (insert j s) x (Function.update y j t)=Function.update (patch s x y) j t := by
  ext k
  by_cases hk : k=j
  · subst k; simp [patch]
  · simp [patch, hk]

def ExactSupport {J : Type*} [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (U : Finset J)
    (f : (∀ j, X j) → ℝ) : Prop :=
  (∀ j∈U, ∀ x, (𝔼 t : X j, f (Function.update x j t))=0) ∧
  (∀ j∉U, ∀ x t, f (Function.update x j t)=f x)

lemma expect_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (r : ℕ) :
    (𝔼 x, f x)^r ≤ 𝔼 x, f x^r := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hh := (convexOn_pow (𝕜 := ℝ) r).map_sum_le
    (t := univ) (w := fun _ : X => (Fintype.card X : ℝ)⁻¹)
    (p := f) (fun _ _ => by positivity)
    (by simp [hn]) (fun x _ => hf x)
  simpa only [smul_eq_mul, ← mul_sum, expect_eq_sum_div_card, card_univ,
    div_eq_inv_mul] using hh

lemma expect_even_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (r : ℕ) : (𝔼 x, f x)^(2*r) ≤ 𝔼 x, (f x)^(2*r) := by
  have hc := expect_mul_sq_le_sq_mul_sq univ f (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const] at hc
  rw [pow_mul]
  apply (pow_le_pow_left₀ (sq_nonneg _) hc r).trans
  simpa only [← pow_mul] using expect_pow_le (fun x => f x^2) (fun x => sq_nonneg _) r

lemma exactSupport_congr {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (U : Finset J)
    (f : (∀ j, X j) → ℝ) (hf : ExactSupport U f)
    (x y : ∀ j, X j) (hxy : ∀ j∈U, x j=y j) : f x=f y := by
  have hh (s : Finset J) : f (patch s x y)=f x := by
    induction s using Finset.induction_on with
    | empty => rw [patch_empty]
    | @insert j s hj ih =>
      have he : patch (insert j s) x y=Function.update (patch s x y) j (y j) := by
        ext a; by_cases ha : a=j
        · subst a; simp [patch]
        · simp [patch, ha]
      rw [he]
      by_cases hjU : j∈U
      · have hxj : (patch s x y) j = y j := by simp [patch, hj, hxy j hjU]
        rw [← hxj, Function.update_eq_self, ih]
      · rw [hf.2 j hjU, ih]
  simpa only [patch_univ] using (hh univ).symm

def hybrid {J : Type*} {X : J → Type*} (b : J → Bool) (x y : ∀j, X j) (j : J) : X j :=
  if b j then x j else y j

def boolMul (a b : Bool) : Bool := if a then b else !b

lemma boolMul_symm (a b : Bool) : boolMul a b=boolMul b a := by cases a <;> cases b <;> rfl

lemma boolMul_self (a b : Bool) : boolMul a (boolMul a b)=b := by cases a <;> cases b <;> rfl

lemma boolSign_mul (a b : Bool) : boolSign (boolMul a b)=boolSign a*boolSign b := by
  cases a <;> cases b <;> norm_num [boolMul, boolSign]

lemma hybrid_hybrid {J : Type*} {X : J → Type*} (b e : J → Bool) (x y : ∀j, X j) :
    hybrid b (hybrid e x y) (hybrid e y x)=hybrid (fun j => boolMul (e j) (b j)) x y := by
  ext j
  cases hb : b j <;> cases he : e j <;> simp [hybrid, boolMul, hb, he]

def copySwapEquiv {J : Type*} {X : J → Type*} (e : J → Bool) :
    ((∀j, X j) × (∀j, X j)) ≃ ((∀j, X j) × (∀j, X j)) where
  toFun a := (hybrid e a.1 a.2, hybrid e a.2 a.1)
  invFun a := (hybrid e a.1 a.2, hybrid e a.2 a.1)
  left_inv a := by
    apply Prod.ext <;> funext j <;> cases he : e j <;> simp [hybrid, he]
  right_inv a := by
    apply Prod.ext <;> funext j <;> cases he : e j <;> simp [hybrid, he]

lemma expect_copySwap {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀j, Fintype (X j)]
    (e : J → Bool) (F : (∀j, X j) → (∀j, X j) → ℝ) :
    (𝔼 x, 𝔼 y, F (hybrid e x y) (hybrid e y x))=𝔼 x, 𝔼 y, F x y := by
  have hh := Fintype.expect_equiv (copySwapEquiv (X:=X) e)
    (fun a => F (hybrid e a.1 a.2) (hybrid e a.2 a.1))
    (fun a => F a.1 a.2) (fun _ => rfl)
  simpa only [← univ_product_univ, expect_product] using hh

lemma expect_hybrid {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (e : J → Bool) (F : (∀j, X j) → ℝ) :
    (𝔼 x, 𝔼 y, F (hybrid e x y))=𝔼 x, F x := by
  simpa only [Fintype.expect_const] using expect_copySwap e (fun x _ => F x)

def boolMulEquiv {J : Type*} (e : J → Bool) : (J → Bool) ≃ (J → Bool) where
  toFun b j := boolMul (e j) (b j)
  invFun b j := boolMul (e j) (b j)
  left_inv b := by funext j; exact boolMul_self _ _
  right_inv b := by funext j; exact boolMul_self _ _

noncomputable def boolChar {J : Type*} (U : Finset J) (b : J → Bool) : ℝ :=
  ∏ j∈U, boolSign (b j)

lemma boolChar_mul {J : Type*} (U : Finset J) (e b : J → Bool) :
    boolChar U (fun j => boolMul (e j) (b j))=boolChar U e*boolChar U b := by
  simp only [boolChar, boolSign_mul, prod_mul_distrib]

lemma boolChar_sq {J : Type*} (U : Finset J) (b : J → Bool) : boolChar U b^2=1 := by
  have he j : boolSign (b j)^2=1 := by cases hb : b j <;> norm_num [boolSign, hb]
  simp only [boolChar, ← prod_pow, he, prod_const_one]

lemma exactSupport_hybrid_expect {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : Finset J) (f : (∀j, X j) → ℝ) (hf : ExactSupport U f)
    (x : ∀j, X j) (b : J → Bool) :
    (𝔼 y, f (hybrid b x y))=(if ∀ j∈U, b j=true then 1 else (0:ℝ))*f x := by
  classical
  by_cases hb : ∀j∈U, b j=true
  · rw [ite_eq_left hb, one_mul]
    have he y : f (hybrid b x y)=f x := exactSupport_congr U f hf _ _
      (fun j hj => by simp [hybrid, hb j hj])
    simp only [he, Fintype.expect_const]
  · rw [ite_eq_right hb, zero_mul]
    push Not at hb
    obtain ⟨j,hj,hb⟩ := hb
    have hfalse : b j=false := by cases h : b j <;> simp_all
    rw [← expect_update_dep j]
    have he (y : ∀j, X j) (t : X j) :
        hybrid b x (Function.update y j t)=Function.update (hybrid b x y) j t := by
      ext a
      by_cases ha : a=j
      · subst a; simp [hybrid, hfalse]
      · simp [hybrid, Function.update_of_ne ha]
    simp only [he, hf.1 j hj, Fintype.expect_const]

lemma expect_prod_pi {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (f : ∀ j, X j → ℝ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]

lemma expect_prod_pi_finset {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : Finset J) (f : ∀ j, X j → ℝ) :
    (𝔼 x : ∀j, X j, ∏ j∈U, f j (x j))=∏ j∈U, (𝔼 t : X j, f j t) := by
  have he := expect_prod_pi (fun j (t : X j) => if j∈U then f j t else 1)
  simp only [prod_ite_mem, univ_inter] at he
  have hp j : (𝔼 t : X j, if j∈U then f j t else 1)=
      if j∈U then (𝔼 t : X j, f j t) else 1 := by
    by_cases hj : j∈U <;> simp [hj]
  simpa only [hp, prod_ite_mem, univ_inter] using he

lemma bool_indicator_char {J : Type*} [Fintype J] [DecidableEq J]
    (U : Finset J) :
    (𝔼 b : J → Bool, (if ∀j∈U, b j=true then 1 else (0:ℝ))*boolChar U b)=(1/2:ℝ)^U.card := by
  classical
  have he (b : J → Bool) :
      (if ∀j∈U, b j=true then 1 else (0:ℝ))*boolChar U b=
        ∏j∈U, (if b j then (1:ℝ) else 0) := by
    by_cases hb : ∀j∈U, b j=true
    · simp only [ite_eq_left hb, one_mul, boolChar]
      apply prod_congr rfl
      intro j hj
      simp [hb j hj, boolSign]
    · rw [ite_eq_right hb, zero_mul]
      push Not at hb
      obtain ⟨j,hj,hb⟩ := hb
      symm
      apply prod_eq_zero hj
      cases h : b j <;> simp_all
  simp only [he]
  rw [expect_prod_pi_finset U (fun _ (b : Bool) => if b then (1:ℝ) else 0)]
  simp

noncomputable def copyDifference {J : Type*} [Fintype J] [DecidableEq J] (U : Finset J)
    {X : J → Type*} (f : (∀j, X j) → ℝ) (x y : ∀j, X j) : ℝ :=
  (2:ℝ)^U.card*(𝔼 b : J → Bool, f (hybrid b x y)*boolChar U b)

lemma copyDifference_mean {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : Finset J) (f : (∀j, X j) → ℝ) (hf : ExactSupport U f) (x : ∀j, X j) :
    (𝔼 y, copyDifference U f x y)=f x := by
  unfold copyDifference
  rw [← mul_expect, expect_comm]
  simp only [← expect_mul, exactSupport_hybrid_expect U f hf]
  have he b : (if ∀j∈U, b j=true then 1 else (0:ℝ))*f x*boolChar U b=
      ((if ∀j∈U, b j=true then 1 else (0:ℝ))*boolChar U b)*f x := by ring
  simp only [he, ← expect_mul, bool_indicator_char]
  rw [← mul_assoc, ← mul_pow]
  norm_num

lemma copyDifference_swap {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    (U : Finset J) (f : (∀j, X j) → ℝ) (x y : ∀j, X j) (e : J → Bool) :
    copyDifference U f (hybrid e x y) (hybrid e y x)=boolChar U e*copyDifference U f x y := by
  unfold copyDifference
  simp only [hybrid_hybrid]
  have he := Fintype.expect_equiv (boolMulEquiv e)
    (fun b => f (hybrid (fun j => boolMul (e j) (b j)) x y)*boolChar U b)
    (fun b => f (hybrid b x y)*boolChar U (fun j => boolMul (e j) (b j)))
    (fun b => by simp only [boolMulEquiv, Equiv.coe_fn_mk, boolMul_self])
  rw [he]
  simp only [boolChar_mul, ← mul_left_comm (boolChar U e), ← mul_expect]

lemma copyDifference_square {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    (U : Finset J) (f : (∀j, X j) → ℝ) (x y : ∀j, X j) :
    (copyDifference U f x y)^2 ≤ (4:ℝ)^U.card*(𝔼 b : J → Bool, f (hybrid b x y)^2) := by
  have hc := expect_mul_sq_le_sq_mul_sq univ (fun b => f (hybrid b x y)) (boolChar U)
  simp only [boolChar_sq, Fintype.expect_const, mul_one] at hc
  unfold copyDifference
  rw [mul_pow, pow_right_comm, show (2:ℝ)^2=4 by norm_num]
  exact mul_le_mul_of_nonneg_left hc (by positivity)

lemma sum_powerset_family {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (a : Finset J → ℝ) :
    (∑U∈(univ : Finset J).powerset, if U∈F then a U else 0)=∑U∈F, a U := by
  classical
  symm
  calc
    _ = ∑U∈F, if U∈F then a U else 0 := by
      apply sum_congr rfl; intro U hU; rw [ite_eq_left hU]
    _ = _ := sum_subset (fun U _ => mem_powerset.mpr (subset_univ U))
      (fun U _ hU => ite_eq_right hU)

lemma walsh_family {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (a : Finset J → ℝ) (e : J → Bool) :
    walsh univ (fun U => if U∈F then a U else 0) e=∑U∈F, a U*boolChar U e := by
  unfold walsh boolChar
  simp only [ite_mul, zero_mul]
  exact sum_powerset_family _ _

lemma walshEnergy_family {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (a : Finset J → ℝ) (C : ℝ) :
    walshEnergy univ C (fun U => if U∈F then a U else 0)=∑U∈F, C^U.card*(a U)^2 := by
  unfold walshEnergy
  simp only [ite_pow, zero_pow (by omega : (2:ℕ)≠0), mul_ite, mul_zero]
  exact sum_powerset_family _ _

lemma difference_energy_bound {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} (F : Finset (Finset J)) (f : Finset J → (∀j, X j) → ℝ)
    (k : ℕ) (hk : ∀U∈F, U.card ≤ k) (C : ℝ) (hC : 1 ≤ C) (x y : ∀j, X j) :
    walshEnergy univ C (fun U => if U∈F then copyDifference U (f U) x y else 0) ≤
      (4*C)^k*(𝔼 e : J → Bool, ∑U∈F, f U (hybrid e x y)^2) := by
  rw [walshEnergy_family]
  calc
    _ ≤ ∑U∈F, (4*C)^k*(𝔼 e : J → Bool, f U (hybrid e x y)^2) := by
      apply sum_le_sum
      intro U hU
      calc
        _ ≤ C^U.card*((4:ℝ)^U.card*(𝔼 e : J → Bool, f U (hybrid e x y)^2)) :=
          mul_le_mul_of_nonneg_left (copyDifference_square U (f U) x y) (by positivity)
        _ = (4*C)^U.card*(𝔼 e : J → Bool, f U (hybrid e x y)^2) := by
          rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by linarith : 1 ≤ 4*C) (hk U hU))
          (expect_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [← mul_sum, expect_sum_comm]

end SquareDifference
end LiftTheory
end

end OAI
