import OAI.Combinatorics.SquareDifference.RationalLift

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

open Finset

section PairFourier

variable {J : Type*} [Fintype J] [DecidableEq J]
  (p : J → ℕ) [∀j,NeZero (p j)]

noncomputable def residueFourier (F : ResidueSpace p → ℂ) (a : ResidueSpace p) : ℂ :=
  𝔼 x,F x*conj (prodChar p a x)

noncomputable def squareMultiplier (a : ResidueSpace p) : ℂ :=
  𝔼 u : ∀j,(ZMod (p j))ˣ,prodChar p a (fun j => (u j : ZMod (p j))^2)

noncomputable def squarePairForm (F G : ResidueSpace p → ℂ) : ℂ :=
  𝔼 u : ∀j,(ZMod (p j))ˣ,𝔼 x,F x*G (x+(fun j => (u j : ZMod (p j))^2))

lemma residueFourier_polynomial (c : ResidueSpace p → ℂ) (a : ResidueSpace p) :
    residueFourier p (fourierPolynomial p c) a=c a := by
  unfold residueFourier fourierPolynomial
  simp only [sum_mul,mul_assoc,expect_sum_comm]
  simp only [← mul_expect,prodChar_orthogonal,mul_ite,mul_one,mul_zero]
  simp

lemma residueFourier_reconstruction (F : ResidueSpace p → ℂ) :
    fourierPolynomial p (residueFourier p F)=F := by
  funext x
  exact fourierPolynomial_reconstruction p F x

lemma residueFourier_parseval (F : ResidueSpace p → ℂ) :
    (∑a,‖residueFourier p F a‖^2)=𝔼 x,‖F x‖^2 := by
  rw [← fourierPolynomial_parseval p,residueFourier_reconstruction]

lemma pair_polynomial (f g : ResidueSpace p → ℂ) :
    squarePairForm p (fourierPolynomial p f) (fourierPolynomial p g)=
      ∑a,f (-a)*g a*squareMultiplier p a := by
  unfold squarePairForm fourierPolynomial
  simp only [prodChar_add_right,sum_mul,mul_sum,expect_sum_comm]
  have he (u : ∀j,(ZMod (p j))ˣ) (a b : ResidueSpace p) :
      (𝔼 x,f a*prodChar p a x*(g b*(prodChar p b x*
        prodChar p b (fun j => (u j : ZMod (p j))^2))))=
      (f a*g b*prodChar p b (fun j => (u j : ZMod (p j))^2))*(if a=-b then 1 else 0) := by
    have h₁ : (fun x => f a*prodChar p a x*(g b*(prodChar p b x*
          prodChar p b (fun j => (u j : ZMod (p j))^2))))=
        (fun x => (f a*g b*prodChar p b (fun j => (u j : ZMod (p j))^2))*prodChar p (a+b) x) := by
      funext x; rw [prodChar_add]; ring
    rw [h₁,← mul_expect,prodChar_expect]
    simp only [add_eq_zero_iff_eq_neg]
  simp_rw [he]
  have hu (a b : ResidueSpace p) :
      (𝔼 u : ∀j,(ZMod (p j))ˣ,(f a*g b*prodChar p b
        (fun j => (u j : ZMod (p j))^2))*(if a=-b then 1 else 0))=
      if a=-b then f a*g b*squareMultiplier p b else 0 := by
    split_ifs <;> simp only [mul_one,mul_zero,expect_const_zero,← mul_expect,squareMultiplier]
  simp_rw [hu]
  simp

lemma squarePairForm_fourier (F G : ResidueSpace p → ℂ) :
    squarePairForm p F G=∑a,residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a := by
  have h := pair_polynomial p (residueFourier p F) (residueFourier p G)
  rwa [residueFourier_reconstruction,residueFourier_reconstruction] at h

lemma squareMultiplier_product (a : ResidueSpace p) :
    squareMultiplier p a=∏j,(𝔼 u : (ZMod (p j))ˣ,ZMod.stdAddChar (a j*(u : ZMod (p j))^2)) := by
  unfold squareMultiplier prodChar
  simp only [expect_eq_sum_div_card,card_univ,Fintype.card_pi,Nat.cast_prod]
  rw [prod_div_distrib,Fintype.prod_sum]

lemma fourier_pair_tail (F G : ResidueSpace p → ℂ) (s : Finset (ResidueSpace p))
    (m : ResidueSpace p → ℂ) (δ : ℝ) (_hδ : 0≤δ) (hm : ∀a∈s,‖m a‖≤δ) :
    ‖∑a∈s,residueFourier p F (-a)*residueFourier p G a*m a‖^2≤
      δ^2*(𝔼 x,‖F x‖^2)*(𝔼 x,‖G x‖^2) := by
  have hn : ‖∑a∈s,residueFourier p F (-a)*residueFourier p G a*m a‖≤
      δ*∑a∈s,‖residueFourier p F (-a)‖*‖residueFourier p G a‖ := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    simp only [norm_mul]
    calc
      _ ≤ (‖residueFourier p F (-a)‖*‖residueFourier p G a‖)*δ :=
        mul_le_mul_of_nonneg_left (hm a ha) (by positivity)
      _ = _ := by ring
  have hc := sum_mul_sq_le_sq_mul_sq s
    (fun a => ‖residueFourier p F (-a)‖) (fun a => ‖residueFourier p G a‖)
  have hF : (∑a∈s,‖residueFourier p F (-a)‖^2)≤𝔼 x,‖F x‖^2 := by
    apply (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => sq_nonneg _)).trans
    rw [Fintype.sum_equiv (Equiv.neg (ResidueSpace p))
      (fun a => ‖residueFourier p F (-a)‖^2) (fun a => ‖residueFourier p F a‖^2)
      (fun _ => rfl),residueFourier_parseval]
  have hG : (∑a∈s,‖residueFourier p G a‖^2)≤𝔼 x,‖G x‖^2 := by
    rw [← residueFourier_parseval]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => sq_nonneg _)
  have hc' := hc.trans (mul_le_mul hF hG
    (sum_nonneg (fun _ _ => sq_nonneg _)) (expect_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ (δ*∑a∈s,‖residueFourier p F (-a)‖*‖residueFourier p G a‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn _
    _ = δ^2*(∑a∈s,‖residueFourier p F (-a)‖*‖residueFourier p G a‖)^2 := by rw [mul_pow]
    _ ≤ δ^2*((𝔼 x,‖F x‖^2)*(𝔼 x,‖G x‖^2)) := mul_le_mul_of_nonneg_left hc' (sq_nonneg _)
    _ = _ := by ring

end PairFourier

end SquareDifference

namespace SquareDifference

lemma quadratic_gauss_ring {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit (2*a)) :
    ‖∑ m : R, ψ (a*m^2)‖^2 = Fintype.card R := by
  have hz (h : R) : 2*a*h=0 ↔ h=0 := by
    rcases ha with ⟨u, hu⟩
    rw [← hu]
    constructor
    · intro he
      have := congrArg (fun x : R => ↑u⁻¹*x) he
      simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using this
    · rintro rfl; exact mul_zero _
  have he : (∑ m : R, ψ (a*m^2))*conj (∑ n : R, ψ (a*n^2)) = Fintype.card R := by
    calc
      _ = ∑ n : R, ∑ m : R, ψ (a*m^2-a*n^2) := by
        simp only [map_sum, sum_mul, mul_sum, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
      _ = ∑ n : R, ∑ h : R, ψ (a*(h+n)^2-a*n^2) := by
        apply sum_congr rfl
        intro n _
        exact Fintype.sum_equiv (Equiv.subRight n) _ _ (by intro m; simp)
      _ = ∑ h : R, ψ (a*h^2)*(∑ n : R, ψ ((2*a*h)*n)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro h _
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = _ := by
        simp_rw [mul_comm (2*a*_) _, AddChar.sum_mulShift _ hψ, hz]
        simp
  rw [Complex.mul_conj'] at he
  exact_mod_cast he

lemma quadratic_gauss_zmod (q : ℕ) [NeZero q] (a : ℤ)
    (hq : q % 2 = 1) (ha : IsCoprime a (q : ℤ)) :
    ‖∑ m : ZMod q, ZMod.stdAddChar ((a : ZMod q)*m^2)‖^2 = q := by
  have h2 : IsUnit (2 : ZMod q) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    simpa only [Nat.coprime_comm, Nat.coprime_two_right] using (Nat.odd_iff.mpr hq)
  have haa : IsUnit (a : ZMod q) := by
    have h := ha.map (Int.castRingHom (ZMod q))
    apply isCoprime_zero_right.mp
    simpa using h
  simpa using quadratic_gauss_ring ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
    (a : ZMod q) (h2.mul haa)

lemma expect_surjective_addHom {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (φ : G →+ H) (hφ : Function.Surjective φ) (f : H → ℂ) :
    (𝔼 x : G, f (φ x))=𝔼 y : H, f y := by
  have he (x : G) : (𝔼 y : H, f (φ x+y))=𝔼 y : H, f y :=
    Fintype.expect_equiv (Equiv.addLeft (φ x)) _ _ (fun _ => rfl)
  have he' (y : H) : (𝔼 x : G, f (φ x+y))=𝔼 x : G, f (φ x) := by
    obtain ⟨z,rfl⟩ := hφ y
    simpa only [map_add] using
      Fintype.expect_equiv (Equiv.addRight z) (fun x => f (φ x+φ z))
        (fun x => f (φ x)) (fun _ => by simp)
  calc
    _ = 𝔼 y : H, 𝔼 x : G, f (φ x+y) := by simp only [he', Fintype.expect_const]
    _ = 𝔼 x : G, 𝔼 y : H, f (φ x+y) := expect_comm _ _ _
    _ = _ := by simp only [he, Fintype.expect_const]

lemma zmod_factor_zero (m k : ℕ) (hk : k ≠ 0) (b : ℤ) :
    (b : ZMod (m*k))*(k : ZMod (m*k))=0 ↔ (b : ZMod m)=0 := by
  rw [← Int.cast_natCast k, ← Int.cast_mul,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact mul_dvd_mul_iff_right (Int.natCast_ne_zero.mpr hk)

lemma zmod_kernel_factor (m k : ℕ) [NeZero (m*k)] (x : ZMod (m*k))
    (hx : ZMod.castHom (dvd_mul_right m k) (ZMod m) x=0) :
    x*(k : ZMod (m*k))=0 := by
  have hk : k ≠ 0 := by intro he; subst k; simpa using (NeZero.ne (m*0))
  have he : ((x.val : ℤ) : ZMod m)=0 := by
    have hh := congrArg (ZMod.castHom (dvd_mul_right m k) (ZMod m)) (ZMod.natCast_zmod_val x)
    simp only [map_natCast] at hh
    simpa only [Int.cast_natCast] using hh.trans hx
  have hh := (zmod_factor_zero m k hk x.val).mpr he
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hh

lemma quadratic_shift_cancellation {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (a c : R) (w : R → ℂ) (ζ : ℂ) (hζ : ζ ≠ 1)
    (hw : ∀ x, w (x+c)=w x)
    (hphase : ∀ x, w x ≠ 0 → ψ (a*((x+c)^2-x^2))=ζ) :
    ∑ x : R, w x*ψ (a*x^2)=0 := by
  have hs : ∑ x : R, w x*ψ (a*x^2) = ζ*(∑ x : R, w x*ψ (a*x^2)) := by
    calc
      _ = ∑ x : R, w (x+c)*ψ (a*(x+c)^2) :=
        (Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)).symm
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        rw [hw]
        by_cases hx : w x=0
        · simp [hx]
        · have he : a*(x+c)^2=a*((x+c)^2-x^2)+a*x^2 := by ring
          rw [he, AddChar.map_add_eq_mul, hphase x hx]
          ring
  have hz : (1-ζ)*(∑ x : R, w x*ψ (a*x^2))=0 := by linear_combination hs
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hζ))

lemma zmod_fiber_translation (m k : ℕ) [NeZero (m*k)]
    (c : ZMod m) (t : ZMod (m*k))
    (ht : ZMod.castHom (dvd_mul_right m k) (ZMod m) t=0) :
    ∀ x : ZMod (m*k),
      (if ZMod.castHom (dvd_mul_right m k) (ZMod m) (x+t)=c then (1 : ℂ) else 0)=
      if ZMod.castHom (dvd_mul_right m k) (ZMod m) x=c then 1 else 0 := by
  intro x
  rw [map_add, ht, add_zero]

lemma fiber_gauss_zero {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p ∣ k) (a : ℤ) (c : ZMod p)
    (hac : (2 : ZMod p)*(a : ZMod p)*c ≠ 0) :
    ∑ x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (1 : ℂ) else 0)*
        ZMod.stdAddChar ((a : ZMod (p*k))*x^2)=0 := by
  classical
  have hk : k ≠ 0 := NeZero.ne k
  let φ := ZMod.castHom (dvd_mul_right p k) (ZMod p)
  let R := ZMod (p*k)
  have ht : φ (k : R)=0 := by
    dsimp only [φ]
    rw [map_natCast]
    exact (ZMod.natCast_eq_zero_iff k p).mpr hpk
  have ht2 : (k : R)^2=0 := by
    rw [pow_two]
    exact zmod_kernel_factor p k (k : R) ht
  let ζ := ZMod.stdAddChar ((2*(a : R)*(c.val : R))*(k : R))
  have hζ : ζ ≠ 1 := by
    intro he
    have he0 : (2*(a : R)*(c.val : R))*(k : R)=0 := by
      apply ZMod.injective_stdAddChar
      simpa only [AddChar.map_zero_eq_one] using he
    have hzero : ((2*a*(c.val : ℤ) : ℤ) : ZMod p)=0 :=
      (zmod_factor_zero p k hk (2*a*c.val)).mp (by simpa using he0)
    have hzero' : (2 : ZMod p)*(a : ZMod p)*c=0 := by simpa using hzero
    exact hac hzero'
  apply quadratic_shift_cancellation ZMod.stdAddChar (a : R) (k : R) _ ζ hζ
  · exact zmod_fiber_translation p k c (k : R) ht
  · intro x hx
    have hxc : φ x=c := by
      by_contra h
      exact hx (ite_eq_right h)
    have hkern : (x-(c.val : R))*(k : R)=0 := by
      apply zmod_kernel_factor p k
      change φ (x-(c.val : R))=0
      rw [map_sub, map_natCast, ZMod.natCast_zmod_val, hxc, sub_self]
    have hxk : x*(k : R)=(c.val : R)*(k : R) := by linear_combination hkern
    congr 1
    change (a : R)*((x+(k : R))^2-x^2)=(2*(a : R)*(c.val : R))*(k : R)
    calc
      _ = 2*(a : R)*(x*(k : R))+(a : R)*(k : R)^2 := by ring
      _ = _ := by rw [hxk, ht2]; ring

lemma odd_fiber_gauss_zero {p k : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    [NeZero k] (hpk : p ∣ k) (a : ℤ) (ha : (a : ZMod p) ≠ 0)
    (c : ZMod p) (hc : c ≠ 0) :
    ∑ x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (1 : ℂ) else 0)*
        ZMod.stdAddChar ((a : ZMod (p*k))*x^2)=0 := by
  apply fiber_gauss_zero hpk a c
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  exact mul_ne_zero (mul_ne_zero h2 ha) hc

lemma weighted_fiber_sum {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (φ : X → Y) (w : Y → ℂ) (f : X → ℂ) :
    ∑ x, w (φ x)*f x = ∑ c, w c * ∑ x, (if φ x=c then (1 : ℂ) else 0)*f x := by
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]
  simp

lemma gauss_zero_of_fiber {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p ∣ k) (a : ℤ) (w : ZMod p → ℂ)
    (hw : ∀ c, w c ≠ 0 → (2 : ZMod p)*(a : ZMod p)*c ≠ 0) :
    ∑ x : ZMod (p*k), w (ZMod.castHom (dvd_mul_right p k) (ZMod p) x)*
      ZMod.stdAddChar ((a : ZMod (p*k))*x^2)=0 := by
  classical
  rw [weighted_fiber_sum]
  apply sum_eq_zero
  intro c _
  by_cases hc : w c=0
  · rw [hc, zero_mul]
  · rw [fiber_gauss_zero hpk a c (hw c hc), mul_zero]

lemma odd_unit_gauss_zero {p k : ℕ} [Fact p.Prime] [NeZero k]
    (hp : p ≠ 2) (hpk : p ∣ k) (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    ∑ x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x ≠ 0 then (1 : ℂ) else 0)*
      ZMod.stdAddChar ((a : ZMod (p*k))*x^2)=0 := by
  apply gauss_zero_of_fiber hpk a (fun c => if c ≠ 0 then 1 else 0)
  intro c hc
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  exact mul_ne_zero (mul_ne_zero h2 ha) hc0

lemma four_unit_mul_two {a c : ZMod 4} (ha : IsUnit a) (hc : IsUnit c) :
    2*a*c ≠ 0 := by
  rcases ha with ⟨a,rfl⟩
  rcases hc with ⟨c,rfl⟩
  intro hz
  have h := congrArg (fun x : ZMod 4 => x*(↑c⁻¹)*(↑a⁻¹)) hz
  have h2 : (2 : ZMod 4) ≠ 0 := by decide
  apply h2
  simpa only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one, zero_mul] using h

lemma two_unit_gauss_zero {k : ℕ} [NeZero k]
    (hk : 4 ∣ k) (a : ℤ) (ha : IsUnit (a : ZMod 4)) :
    ∑ x : ZMod (4*k),
      (if IsUnit (ZMod.castHom (dvd_mul_right 4 k) (ZMod 4) x) then (1 : ℂ) else 0)*
      ZMod.stdAddChar ((a : ZMod (4*k))*x^2)=0 := by
  classical
  apply gauss_zero_of_fiber hk a (fun c => if IsUnit c then 1 else 0)
  intro c hc
  have hc0 : IsUnit c := by by_contra he; simp [he] at hc
  exact four_unit_mul_two ha hc0

lemma quadratic_gauss_ring_linear {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a b : R) (ha : IsUnit (2*a)) :
    ‖∑ m : R, ψ (a*m^2+b*m)‖^2 = Fintype.card R := by
  have hz (h : R) : 2*a*h=0 ↔ h=0 := by
    rcases ha with ⟨u, hu⟩
    rw [← hu]
    constructor
    · intro he
      have := congrArg (fun x : R => ↑u⁻¹*x) he
      simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using this
    · rintro rfl; exact mul_zero _
  have he : (∑ m : R, ψ (a*m^2+b*m))*conj (∑ n : R, ψ (a*n^2+b*n)) = Fintype.card R := by
    calc
      _ = ∑ n : R, ∑ m : R, ψ ((a*m^2+b*m)-(a*n^2+b*n)) := by
        simp only [map_sum, sum_mul, mul_sum, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
      _ = ∑ n : R, ∑ h : R, ψ ((a*(h+n)^2+b*(h+n))-(a*n^2+b*n)) := by
        apply sum_congr rfl
        intro n _
        exact Fintype.sum_equiv (Equiv.subRight n) _ _ (by intro m; simp)
      _ = ∑ h : R, ψ (a*h^2+b*h)*(∑ n : R, ψ ((2*a*h)*n)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro h _
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = _ := by
        simp_rw [mul_comm (2*a*_) _, AddChar.sum_mulShift _ hψ, hz]
        simp
  rw [Complex.mul_conj'] at he
  exact_mod_cast he

lemma norm_quadratic_expect {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a b : R) (ha : IsUnit (2*a)) :
    ‖𝔼 m : R, ψ (a*m^2+b*m)‖= (Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  have hc : (0:ℝ)<Fintype.card R := Nat.cast_pos.mpr Fintype.card_pos
  have he := congrArg Real.sqrt (quadratic_gauss_ring_linear ψ hψ a b ha)
  rw [Real.sqrt_sq (norm_nonneg _)] at he
  rw [expect_eq_sum_div_card, norm_div, card_univ, Complex.norm_natCast, he,
    Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc]
  congr 1
  norm_num

lemma fourier_weighted_gauss {R I : Type*} [CommRing R] [Fintype R] [DecidableEq R] [Fintype I]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit (2*a))
    (b : I → R) (c : I → ℂ) :
    ‖𝔼 m : R, (∑ i, c i*ψ (b i*m))*ψ (a*m^2)‖ ≤
      (∑ i, ‖c i‖)*(Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  have he : (𝔼 m : R, (∑ i, c i*ψ (b i*m))*ψ (a*m^2))=
      ∑ i, c i*(𝔼 m : R, ψ (a*m^2+b i*m)) := by
    simp only [sum_mul, expect_sum_comm, AddChar.map_add_eq_mul]
    simp only [mul_assoc, ← mul_expect]
    apply sum_congr rfl
    intro i _
    apply congrArg (fun z => c i*z)
    apply expect_congr rfl
    intro m _
    exact mul_comm _ _
  rw [he]
  calc
    _ ≤ ∑ i, ‖c i*(𝔼 m : R, ψ (a*m^2+b i*m))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_quadratic_expect ψ hψ a _ ha, ← sum_mul]

noncomputable def primeSieveWeight (p : ℕ) (x : ZMod p) : ℝ :=
  ((p : ℝ)*(if x=0 then 1 else 0)-1)/(p-1)

lemma primeSieveWeight_fourier {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    (primeSieveWeight p x : ℂ)=(p-1 : ℂ)⁻¹*∑ a∈univ.erase 0, ZMod.stdAddChar (a*x) := by
  classical
  have he : ∑ a : ZMod p, ZMod.stdAddChar (a*x)=
      if x=0 then (p : ℂ) else 0 := by
    simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar p)
  have hs := sum_erase_add (univ : Finset (ZMod p)) (fun a => ZMod.stdAddChar (a*x)) (mem_univ 0)
  rw [zero_mul, AddChar.map_zero_eq_one, he] at hs
  unfold primeSieveWeight
  push_cast
  rw [div_eq_inv_mul]
  congr 1
  by_cases hx : x=0
  · rw [ite_eq_left hx] at hs ⊢
    push_cast
    linear_combination -hs
  · rw [ite_eq_right hx] at hs ⊢
    push_cast
    linear_combination -hs

lemma primeSieveWeight_abs_le {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    |primeSieveWeight p x|≤1 := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_cases hx : x=0
  · simp only [primeSieveWeight, ite_eq_left hx, mul_one, div_self (by linarith : (p:ℝ)-1≠0), abs_one, le_refl]
  · simp only [primeSieveWeight, ite_eq_right hx, mul_zero, zero_sub, neg_div, abs_neg,
      abs_of_pos (div_pos (by norm_num) (by linarith))]
    rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
    apply (div_le_one (by linarith)).mpr
    have hp2 : (2:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).two_le
    linarith

lemma primeSieveWeight_mean_zero {p : ℕ} [Fact p.Prime] :
    (𝔼 x : ZMod p, primeSieveWeight p x)=0 := by
  classical
  have hp0 : (p : ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [primeSieveWeight, ← expect_div, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  rw [expect_eq_sum_div_card]
  simp [ZMod.card, hp0]

lemma primeSieveWeight_unit_density {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    1-primeSieveWeight p x=(p : ℝ)/(p-1)*(if x≠0 then 1 else 0) := by
  have hp : (p : ℝ)-1≠0 := by
    have h : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  unfold primeSieveWeight
  by_cases hx : x=0
  · simp only [hx, ite_true, ne_eq, not_true_eq_false, ite_false, mul_one, mul_zero, div_self hp, sub_self]
  · simp only [ite_eq_right hx, ite_eq_left hx, mul_zero, zero_sub, mul_one]
    field_simp
    ring

noncomputable def zmodScaleHom (p k : ℕ) : ZMod p →+ ZMod (p*k) :=
  ZMod.lift p ⟨{ toFun := fun z : ℤ => (k : ZMod (p*k))*(z : ZMod (p*k))
                 map_zero' := by simp
                 map_add' := by intros; simp only [Int.cast_add, mul_add] }, by
    change (k : ZMod (p*k))*((p : ℤ) : ZMod (p*k))=0
    rw [Int.cast_natCast]
    rw [← Nat.cast_mul, mul_comm k p, ZMod.natCast_self]⟩

lemma zmodScaleHom_int (p k : ℕ) (z : ℤ) :
    zmodScaleHom p k (z : ZMod p)=(k : ZMod (p*k))*(z : ZMod (p*k)) :=
  ZMod.lift_coe p _ z

lemma zmodScaleHom_nat (p k z : ℕ) :
    zmodScaleHom p k (z : ZMod p)=(k : ZMod (p*k))*(z : ZMod (p*k)) := by
  simpa only [Int.cast_natCast] using zmodScaleHom_int p k (z : ℤ)

lemma zmodScaleHom_injective (p k : ℕ) [NeZero p] (hk : k≠0) : Function.Injective (zmodScaleHom p k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have he : ((x.val : ℤ) : ZMod p)=0 := (zmod_factor_zero p k hk (x.val : ℤ)).mp (by
    rw [mul_comm ((x.val : ℤ) : ZMod (p*k)) (k : ZMod (p*k)), ← zmodScaleHom_int, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hx)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using he

lemma zmodScaleHom_mul {p k : ℕ} [NeZero p] [NeZero k] (t : ZMod p) (x : ZMod (p*k)) :
    zmodScaleHom p k (t*(ZMod.castHom (dvd_mul_right p k) (ZMod p) x))=
      zmodScaleHom p k t*x := by
  have ht := ZMod.natCast_zmod_val t
  have hx := ZMod.natCast_zmod_val x
  conv_lhs => rw [← ht, ← hx]
  simp only [map_natCast, ← Nat.cast_mul]
  rw [← Int.cast_natCast, zmodScaleHom_int]
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [ZMod.natCast_zmod_val, ← mul_assoc, ← zmodScaleHom_nat p k t.val,
    ZMod.natCast_zmod_val]

lemma zmodScale_primitive {p k : ℕ} [Fact p.Prime] (hk : k≠0)
    (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom (zmodScaleHom p k)).IsPrimitive := by
  have : NeZero k := ⟨hk⟩
  apply AddChar.IsPrimitive.of_ne_one
  intro he
  have hh := congrArg (fun χ : AddChar (ZMod p) ℂ => χ 1) he
  simp only [AddChar.compAddMonoidHom_apply, AddChar.one_apply] at hh
  have hz := (hψ.zmod_char_eq_one_iff (p*k) _).mp hh
  have h1 : (1 : ZMod p)=0 := zmodScaleHom_injective p k hk (by simpa using hz)
  exact one_ne_zero h1

lemma primeSieveWeight_fourier_char {p : ℕ} [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) (x : ZMod p) :
    (primeSieveWeight p x : ℂ)=(p-1 : ℂ)⁻¹*∑ a∈univ.erase 0, ψ (a*x) := by
  classical
  have he : ∑ a : ZMod p, ψ (a*x)=if x=0 then (p : ℂ) else 0 := by
    simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift x hψ
  have hs := sum_erase_add (univ : Finset (ZMod p)) (fun a => ψ (a*x)) (mem_univ 0)
  rw [zero_mul, AddChar.map_zero_eq_one, he] at hs
  unfold primeSieveWeight
  push_cast
  rw [div_eq_inv_mul]
  congr 1
  by_cases hx : x=0
  · rw [ite_eq_left hx] at hs ⊢
    push_cast
    linear_combination -hs
  · rw [ite_eq_right hx] at hs ⊢
    push_cast
    linear_combination -hs

end SquareDifference
end LiftTheory
end

end OAI
