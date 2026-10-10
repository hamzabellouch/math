import OAI.Algebra.AuslanderReiten.Algebras.BaseAlgebra
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Exact.Basic

namespace OAI

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

def fixedRight (p : C) : Submodule C C where
  carrier := {a | a * p = a}
  zero_mem' := zero_mul p
  add_mem' {a b} ha hb := by
    change a * p = a at ha
    change b * p = b at hb
    change (a + b) * p = a + b
    rw [add_mul, ha, hb]
  smul_mem' c a ha := by
    change (c * a) * p = c * a
    rw [mul_assoc, ha]

def rightMultiply (p : C) : C →ₗ[C] C where
  toFun a := a * p
  map_add' a b := add_mul a b p
  map_smul' c a := mul_assoc c a p

def projection (p : C) (hp : p * p = p) : C →ₗ[C] fixedRight q p where
  toFun a := ⟨a * p, by change (a * p) * p = a * p; rw [mul_assoc, hp]⟩
  map_add' a b := Subtype.ext (add_mul a b p)
  map_smul' c a := Subtype.ext (mul_assoc c a p)

theorem projection_surjective (p : C) (hp : p * p = p) :
    Function.Surjective (projection q p hp) := by
  intro a
  exact ⟨a, Subtype.ext a.property⟩

theorem projective_fixedRight (p : C) (hp : p * p = p) :
    Module.Projective C (fixedRight q p) := by
  apply Module.Projective.of_split (fixedRight q p).subtype (projection q p hp)
  apply LinearMap.ext
  intro a
  exact Subtype.ext a.property

theorem finite_fixedRight (p : C) (hp : p * p = p) :
    Module.Finite k (fixedRight q p) :=
  Module.Finite.of_surjective ((projection q p hp).restrictScalars k)
    (projection_surjective q p hp)

abbrev E : Submodule C C := fixedRight q (basisVector q e)

abbrev F : Submodule C C := fixedRight q (basisVector q f)

instance : Module.Projective C (E q) :=
  projective_fixedRight q _ (by simpa [multiplicationTable] using basis_mul q e e)
instance : Module.Projective C (F q) :=
  projective_fixedRight q _ (by simpa [multiplicationTable] using basis_mul q f f)

instance : Module.Finite k (E q) :=
  finite_fixedRight q _ (by simpa [multiplicationTable] using basis_mul q e e)
instance : Module.Finite k (F q) :=
  finite_fixedRight q _ (by simpa [multiplicationTable] using basis_mul q f f)

def rightBetween (p r z : C) (hz : z * r = z) :
    fixedRight q p →ₗ[C] fixedRight q r where
  toFun a := ⟨(a : C) * z, by change ((a : C) * z) * r = (a : C) * z; rw [mul_assoc, hz]⟩
  map_add' a b := Subtype.ext (add_mul (a : C) (b : C) z)
  map_smul' c a := Subtype.ext (mul_assoc c (a : C) z)

def ell (r : k) : C := basisVector q x + r • basisVector q y

@[simp] theorem ell_right_e (r : k) : ell q r * basisVector q e = ell q r := by
  simp [ell, add_mul, basis_mul, multiplicationTable]

def dU : E q →ₗ[C] F q :=
  rightBetween q _ _ (basisVector q u)
    (by simpa [multiplicationTable] using basis_mul q u f)

def dEll (r : k) : E q →ₗ[C] E q := rightBetween q _ _ (ell q r) (ell_right_e q r)

@[simp] theorem coe_dU (a : E q) : (dU q a : C) = (a : C) * basisVector q u := rfl
@[simp] theorem coe_dEll (r : k) (a : E q) : (dEll q r a : C) = (a : C) * ell q r := rfl

private theorem E_coeff_zero (a : E q) (i : Letter)
    (hi : i = u ∨ i = v ∨ i = f ∨ i = n) : (a : C).coeff i = 0 := by
  have h := congrArg (fun b : C => b.coeff i) a.property
  rcases hi with rfl | rfl | rfl | rfl <;> simpa [product] using h.symm

@[simp] theorem E_coeff_u (a : E q) : (a : C).coeff u = 0 := E_coeff_zero q a u (by simp)
@[simp] theorem E_coeff_v (a : E q) : (a : C).coeff v = 0 := E_coeff_zero q a v (by simp)
@[simp] theorem E_coeff_f (a : E q) : (a : C).coeff f = 0 := E_coeff_zero q a f (by simp)
@[simp] theorem E_coeff_n (a : E q) : (a : C).coeff n = 0 := E_coeff_zero q a n (by simp)

theorem E_expand (a : E q) : (a : C) =
    (a : C).coeff e • basisVector q e + (a : C).coeff x • basisVector q x +
    (a : C).coeff y • basisVector q y + (a : C).coeff z • basisVector q z +
    (a : C).coeff t • basisVector q t + (a : C).coeff j • basisVector q j := by
  ext i
  cases i <;> simp

theorem mul_u_formula (a : E q) : (a : C) * basisVector q u =
    (a : C).coeff e • basisVector q u +
    ((a : C).coeff x + (a : C).coeff y) • basisVector q v +
    ((1 + q) * (a : C).coeff t) • basisVector q n := by
  ext i
  cases i <;> simp [product]

theorem mul_ell_formula (r : k) (a : E q) : (a : C) * ell q r =
    (a : C).coeff e • ell q r +
    (q * r * (a : C).coeff x + (a : C).coeff y) • basisVector q z +
    ((1 + q ^ 2 * r) * (a : C).coeff t) • basisVector q j := by
  ext i
  cases i <;> simp [product, ell] <;> ring

section CharacteristicTwo

variable [CharP k 2]

theorem mul_u_eq_zero_iff (hq : 1 + q ≠ 0) (a : E q) :
    (a : C) * basisVector q u = 0 ↔
      (a : C).coeff e = 0 ∧ (a : C).coeff t = 0 ∧ (a : C).coeff y = (a : C).coeff x := by
  rw [mul_u_formula]
  constructor
  · intro h
    have he := congrArg (fun b : C => b.coeff u) h
    have ht := congrArg (fun b : C => b.coeff n) h
    have hy := congrArg (fun b : C => b.coeff v) h
    simp only [coeff_add, coeff_smul, coeff_basisVector, coeff_zero] at he ht hy
    simp only [reduceCtorEq, ↓reduceIte, mul_zero, mul_one, add_zero, zero_add] at he ht hy
    exact ⟨he, (mul_eq_zero.mp ht).resolve_left hq, (CharTwo.add_eq_zero.mp hy).symm⟩
  · rintro ⟨he, ht, hy⟩
    simp [he, ht, hy, CharTwo.add_self_eq_zero]

theorem mul_ell_eq_zero_iff (r : k) (hr : 1 + q ^ 2 * r ≠ 0) (a : E q) :
    (a : C) * ell q r = 0 ↔
      (a : C).coeff e = 0 ∧ (a : C).coeff t = 0 ∧
      (a : C).coeff y = q * r * (a : C).coeff x := by
  rw [mul_ell_formula]
  constructor
  · intro h
    have he := congrArg (fun b : C => b.coeff x) h
    have ht := congrArg (fun b : C => b.coeff j) h
    have hy := congrArg (fun b : C => b.coeff z) h
    simp [ell] at he ht hy
    exact ⟨he, ht.resolve_left hr, (CharTwo.add_eq_zero.mp hy).symm⟩
  · rintro ⟨he, ht, hy⟩
    simp [he, ht, hy, CharTwo.add_self_eq_zero]

end CharacteristicTwo

def ellPreimage (r α β γ : k) : E q :=
  ⟨α • basisVector q e + β • basisVector q y + (γ / (1 + q ^ 2 * r)) • basisVector q t, by
    change (_ : C) * basisVector q e = _
    simp [add_mul, basis_mul, multiplicationTable]⟩

theorem ellPreimage_spec (r α β γ : k) (hr : 1 + q ^ 2 * r ≠ 0) :
    (ellPreimage q r α β γ : C) * ell q r =
      α • ell q r + β • basisVector q z + γ • basisVector q j := by
  rw [mul_ell_formula]
  have hγ : (1 + q ^ 2 * r) * (γ / (1 + q ^ 2 * r)) = γ := by
    rw [mul_comm, div_mul_cancel₀ γ hr]
  simp [ellPreimage, hγ]

section Exactness

variable [CharP k 2]

theorem uKernel_expand (hq : 1 + q ≠ 0) (a : E q)
    (ha : (a : C) * basisVector q u = 0) :
    (a : C) = (a : C).coeff x • ell q 1 +
      (a : C).coeff z • basisVector q z + (a : C).coeff j • basisVector q j := by
  obtain ⟨he, ht, hy⟩ := (mul_u_eq_zero_iff q hq a).mp ha
  ext i
  cases i <;> simp [ell, he, ht, hy]

theorem ellKernel_expand (r : k) (hr : 1 + q ^ 2 * r ≠ 0) (a : E q)
    (ha : (a : C) * ell q r = 0) :
    (a : C) = (a : C).coeff x • ell q (q * r) +
      (a : C).coeff z • basisVector q z + (a : C).coeff j • basisVector q j := by
  obtain ⟨he, ht, hy⟩ := (mul_ell_eq_zero_iff q r hr a).mp ha
  ext i
  cases i <;> simp [ell, he, ht, hy]
  ring

@[simp] theorem ell_one_mul_u : ell q 1 * basisVector q u = 0 := by
  ext i
  cases i <;> simp [ell, product, CharTwo.add_self_eq_zero]

@[simp] theorem ell_successor_mul (r : k) : ell q (q * r) * ell q r = 0 := by
  ext i
  cases i <;> simp [ell, product, CharTwo.add_self_eq_zero]

theorem dU_comp_dEll_one : (dU q).comp (dEll q 1) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change ((a : C) * ell q 1) * basisVector q u = 0
  rw [mul_assoc, ell_one_mul_u, mul_zero]

theorem dEll_comp_successor (r : k) : (dEll q r).comp (dEll q (q * r)) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change ((a : C) * ell q (q * r)) * ell q r = 0
  rw [mul_assoc, ell_successor_mul, mul_zero]

theorem exact_dU (hq : 1 + q ≠ 0) (hq2 : 1 + q ^ 2 ≠ 0) :
    Function.Exact (dEll q 1) (dU q) := by
  intro a
  constructor
  · intro ha
    have ha' : (a : C) * basisVector q u = 0 := congrArg Subtype.val ha
    refine ⟨ellPreimage q 1 ((a : C).coeff x) ((a : C).coeff z) ((a : C).coeff j), ?_⟩
    apply Subtype.ext
    change (_ : C) * ell q 1 = (a : C)
    rw [ellPreimage_spec q 1 _ _ _ (by simpa using hq2)]
    exact (uKernel_expand q hq a ha').symm
  · rintro ⟨b, rfl⟩
    exact DFunLike.congr_fun (dU_comp_dEll_one q) b

theorem exact_dEll (r : k) (hr : 1 + q ^ 2 * r ≠ 0)
    (hnext : 1 + q ^ 2 * (q * r) ≠ 0) :
    Function.Exact (dEll q (q * r)) (dEll q r) := by
  intro a
  constructor
  · intro ha
    have ha' : (a : C) * ell q r = 0 := congrArg Subtype.val ha
    refine ⟨ellPreimage q (q * r) ((a : C).coeff x) ((a : C).coeff z) ((a : C).coeff j), ?_⟩
    apply Subtype.ext
    change (_ : C) * ell q (q * r) = (a : C)
    rw [ellPreimage_spec q (q * r) _ _ _ hnext]
    exact (ellKernel_expand q r hr a ha').symm
  · rintro ⟨b, rfl⟩
    exact DFunLike.congr_fun (dEll_comp_successor q r) b

end Exactness

end ArExplicit.Resolution

end OAI
