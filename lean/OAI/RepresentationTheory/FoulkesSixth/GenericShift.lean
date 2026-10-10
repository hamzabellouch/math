import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.PolynomialSpan

namespace OAI

noncomputable section

namespace Foulkes.GenericShift
open MvPolynomial
open Foulkes.PolynomialSpan

variable {A : Type*} [CommRing A]

abbrev Poly (A : Type*) [CommRing A] (m n : ℕ) := MvPolynomial (Fin m × Fin n) A

def shift {m n : ℕ} (u v : Fin m) : Derivation A (Poly A m n) (Poly A m n) :=
  mkDerivation A fun ij => if ij.1 = u then X (v, ij.2) else 0

@[simp] lemma shift_X {m n : ℕ} (u v : Fin m) (ij : Fin m × Fin n) :
    shift (A := A) u v (X ij) = if ij.1 = u then X (v, ij.2) else 0 := by
  simp [shift]

lemma derivation_sum_apply {ι : Type*} {m n : ℕ}
    (s : Finset ι) (D : ι → Derivation A (Poly A m n) (Poly A m n)) (f : Poly A m n) :
    (∑ k ∈ s, D k) f = ∑ k ∈ s, D k f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => simp [Finset.sum_insert hx, ih]

lemma shift_eq_sum {m n : ℕ} (u v : Fin m) :
    shift (A := A) (n := n) u v = ∑ k : Fin n, (X (v, k) : Poly A m n) •
      (pderiv (u, k) : Derivation A (Poly A m n) (Poly A m n)) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨r, k⟩
  simp only [shift_X, derivation_sum_apply, Derivation.smul_apply, pderiv_X]
  by_cases h : r = u
  · subst r
    simp [Pi.single_apply, Prod.mk.injEq]
  · simp [Prod.mk.injEq, h]

lemma mapCoeffs_shift [Algebra ℂ A] {m n : ℕ}
    (l : A →ₗ[ℂ] ℂ) (u v : Fin m) (f : Poly A m n) :
    mapCoeffs l (shift u v f) = shift u v (mapCoeffs l f) := by
  simp only [shift_eq_sum, derivation_sum_apply, Derivation.smul_apply,
    smul_eq_mul, mapCoeffs_sum, mapCoeffs_X_mul, mapCoeffs_pderiv]

lemma mapCoeffs_shift_pow [Algebra ℂ A] {m n : ℕ}
    (l : A →ₗ[ℂ] ℂ) (u v : Fin m) (f : Poly A m n) (L : ℕ) :
    mapCoeffs l (((shift u v).toLinearMap ^ L) f) =
      ((shift u v).toLinearMap ^ L) (mapCoeffs l f) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simpa only [pow_succ', Module.End.mul_apply, Derivation.coeFn_coe, mapCoeffs_shift] using
      congrArg (shift u v) ih

def rowLinear {m n : ℕ} (u : Fin m) (c : Fin n → A) : Poly A m n :=
  ∑ k, c k • X (u, k)

@[simp] lemma shift_rowLinear {m n : ℕ} (u v w : Fin m) (c : Fin n → A) :
    shift u v (rowLinear w c) = if w = u then rowLinear v c else 0 := by
  simp [rowLinear, map_sum, shift_X]

lemma pow_apply_mul_of_left_zero {B : Type*} [CommRing B] [Algebra A B]
    (D : Derivation A B B) {g : B} (hg : D g = 0) (f : B) (L : ℕ) :
    (D.toLinearMap ^ L) (g * f) = g * (D.toLinearMap ^ L) f := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [pow_succ', Module.End.mul_apply, ih, Derivation.coeFn_coe, D.leibniz, hg,
      smul_eq_mul, mul_zero, add_zero]

lemma pow_apply_pow {B : Type*} [CommRing B] [Algebra A B]
    (D : Derivation A B B) {f g : B} (hf : D f = g) (hg : D g = 0)
    (j L : ℕ) (hL : L ≤ j) :
    (D.toLinearMap ^ L) (f ^ j) = j.descFactorial L • (g ^ L * f ^ (j - L)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hLj : L ≤ j := Nat.le_trans (Nat.le_succ L) hL
    rw [pow_succ', Module.End.mul_apply, ih hLj, Derivation.coeFn_coe, map_nsmul]
    have hkill : D (g ^ L) = 0 := by simp [D.leibniz_pow, hg]
    rw [D.leibniz, hkill, smul_zero, add_zero, D.leibniz_pow, hf]
    simp only [smul_eq_mul, nsmul_eq_mul]
    rw [Nat.descFactorial_succ]
    have hsub : j - L - 1 = j - (L + 1) := by omega
    rw [hsub, pow_succ]
    push_cast
    ring

lemma derivation_prod_zero {B ι : Type*} [CommRing B] [Algebra A B]
    (D : Derivation A B B) (s : Finset ι) (f : ι → B)
    (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, D.leibniz, h i (by simp),
      ih (fun k hk => h k (Finset.mem_insert_of_mem hk))]
    simp

def mixedProduct {B ι : Type*} [CommRing B] [Fintype ι] [DecidableEq ι]
    (x y : ι → B) (j L : ℕ) (s : Finset ι) : B :=
  ∏ i, if i ∈ s then y i ^ L * x i ^ (j - L) else x i ^ j

lemma pow_apply_mixedProduct {B ι : Type*} [CommRing B] [Algebra A B] [Fintype ι] [DecidableEq ι]
    (D : Derivation A B B) (x y : ι → B) (j L : ℕ) (s : Finset ι) (u : ι)
    (hu : u ∉ s) (hL : L ≤ j)
    (hx : ∀ i, D (x i) = if i = u then y i else 0)
    (hy : ∀ i, D (y i) = 0) :
    (D.toLinearMap ^ L) (mixedProduct x y j L s) =
      j.descFactorial L • mixedProduct x y j L (insert u s) := by
  classical
  let F (i : ι) := if i ∈ s then y i ^ L * x i ^ (j - L) else x i ^ j
  let H : B := ∏ i ∈ Finset.univ.erase u, F i
  have hH : D H = 0 := by
    apply derivation_prod_zero
    intro i hi
    have hne : i ≠ u := (Finset.mem_erase.mp hi).1
    dsimp [F]
    split_ifs <;> simp [D.leibniz, D.leibniz_pow, hx, hy, hne]
  have he : mixedProduct x y j L s = H * (x u) ^ j := by
    rw [mixedProduct, ← Finset.mul_prod_erase Finset.univ F (a := u) (by simp)]
    simp [F, hu, H, mul_comm]
  have hf : mixedProduct x y j L (insert u s) = H * ((y u) ^ L * (x u) ^ (j - L)) := by
    let G (i : ι) := if i ∈ insert u s then y i ^ L * x i ^ (j - L) else x i ^ j
    rw [mixedProduct, ← Finset.mul_prod_erase Finset.univ G (a := u) (by simp)]
    have hge : (∏ i ∈ Finset.univ.erase u, G i) = H := by
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ u := (Finset.mem_erase.mp hi).1
      simp [F, G, hne]
    rw [hge]
    simp [G, mul_comm]
  rw [he, pow_apply_mul_of_left_zero D hH,
    pow_apply_pow D (f := x u) (g := y u) (by simp [hx]) (hy u) j L hL, hf]
  simp only [nsmul_eq_mul]
  ring

def rowWeight {m n : ℕ} (u : Fin m) (ij : Fin m × Fin n) : ℕ :=
  if ij.1 = u then 1 else 0

lemma rowLinear_homogeneous {m n : ℕ} (u w : Fin m) (c : Fin n → A) :
    (rowLinear u c).IsWeightedHomogeneous (rowWeight w) (if u = w then 1 else 0) := by
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  exact (weightedHomogeneousSubmodule A (rowWeight w) _).smul_mem _
    (isWeightedHomogeneous_X (R := A) (rowWeight w) (u, k))

def family {a n : ℕ} (c : Fin a → Fin n → A) (j L : ℕ) (s : Finset (Fin a)) :
    Poly A (a + 1) n :=
  mixedProduct (fun i => rowLinear i.castSucc (c i))
    (fun i => rowLinear (Fin.last a) (c i)) j L s

lemma shift_family {a n : ℕ} (c : Fin a → Fin n → A) (j L : ℕ)
    (s : Finset (Fin a)) (u : Fin a) (hu : u ∉ s) (hL : L ≤ j) :
    ((shift (A := A) u.castSucc (Fin.last a)).toLinearMap ^ L) (family c j L s) =
      j.descFactorial L • family c j L (insert u s) := by
  apply pow_apply_mixedProduct _ _ _ _ _ _ _ hu hL
  · intro i
    simp
  · intro i
    simp [ne_comm]

lemma family_degree_dest {a n : ℕ} (c : Fin a → Fin n → A) (j L : ℕ)
    (s : Finset (Fin a)) :
    (family c j L s).IsWeightedHomogeneous (rowWeight (Fin.last a)) (s.card * L) := by
  have hX (i : Fin a) : (rowLinear i.castSucc (c i)).IsWeightedHomogeneous
      (rowWeight (Fin.last a)) 0 := by simpa using rowLinear_homogeneous i.castSucc (Fin.last a) (c i)
  have hY (i : Fin a) : (rowLinear (Fin.last a) (c i)).IsWeightedHomogeneous
      (rowWeight (Fin.last a)) 1 := by simpa using rowLinear_homogeneous (Fin.last a) (Fin.last a) (c i)
  have hF (i : Fin a) : (if i ∈ s then rowLinear (Fin.last a) (c i) ^ L *
      rowLinear i.castSucc (c i) ^ (j - L) else rowLinear i.castSucc (c i) ^ j).IsWeightedHomogeneous (rowWeight (Fin.last a)) (if i ∈ s then L else 0) := by
    split_ifs
    · simpa using ((hY i).pow L).mul ((hX i).pow (j - L))
    · simpa using (hX i).pow j
  have hh := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ (fun i _ => hF i)
  simpa [family, mixedProduct] using hh

lemma family_degree_source {a n : ℕ} (c : Fin a → Fin n → A) (j L : ℕ)
    (s : Finset (Fin a)) (u : Fin a) (hu : u ∉ s) :
    (family c j L s).IsWeightedHomogeneous (rowWeight u.castSucc) j := by
  have hX (i : Fin a) : (rowLinear i.castSucc (c i)).IsWeightedHomogeneous
      (rowWeight u.castSucc) (if i = u then 1 else 0) := by
    simpa using rowLinear_homogeneous i.castSucc u.castSucc (c i)
  have hY (i : Fin a) : (rowLinear (Fin.last a) (c i)).IsWeightedHomogeneous
      (rowWeight u.castSucc) 0 := by
    simpa [Ne.symm (Fin.castSucc_ne_last u)] using
      rowLinear_homogeneous (Fin.last a) u.castSucc (c i)
  have hF (i : Fin a) : (if i ∈ s then rowLinear (Fin.last a) (c i) ^ L *
      rowLinear i.castSucc (c i) ^ (j - L) else rowLinear i.castSucc (c i) ^ j).IsWeightedHomogeneous (rowWeight u.castSucc) (if i = u then j else 0) := by
    by_cases hi : i = u
    · subst i
      simp only [hu, ↓reduceIte]
      simpa using (hX u).pow j
    · have hX' : (rowLinear i.castSucc (c i)).IsWeightedHomogeneous
          (rowWeight u.castSucc) 0 := by simpa [hi] using hX i
      by_cases his : i ∈ s
      · simpa [his, hi] using ((hY i).pow L).mul (hX'.pow (j - L))
      · simpa [his, hi] using hX'.pow j
  have hh := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ (fun i _ => hF i)
  simpa [family, mixedProduct] using hh

lemma eval_rowLinear [Algebra ℂ A] {m n : ℕ} (u : Fin m) (c : Fin n → A)
    (x : Fin m × Fin n → ℂ) :
    eval (fun ij => algebraMap ℂ A (x ij)) (rowLinear u c) = ∑ k, x (u, k) • c k := by
  simp [rowLinear, Algebra.smul_def, mul_comm]

end Foulkes.GenericShift

end

end OAI
