import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.InvariantPolarization

namespace OAI

noncomputable section

namespace Foulkes.Vanishing
open MvPolynomial Foulkes.Polarization Foulkes.PolynomialSpan

lemma binary_split {a n r : ℕ} (hr : 0 < r) (c : ℂ) (x t : Fin n → ℂ) :
    ∃ v : Fin r → Fin n → ℂ, ∀ i : Fin a,
      rowForm i x ^ r + c • rowForm i t ^ r = ∏ j, rowForm i (v j) := by
  classical
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-c) hr
  let ζ := Complex.exp (2 * Real.pi * Complex.I / r)
  have hζ : IsPrimitiveRoot ζ r := Complex.isPrimitiveRoot_exp r hr.ne'
  let S := Polynomial.nthRootsFinset r (1 : ℂ)
  have hS : Fintype.card S = r := by
    rw [Fintype.card_coe]
    exact hζ.card_nthRootsFinset
  let e : Fin r ≃ S := (Fintype.equivFinOfCardEq hS).symm
  refine ⟨fun j k => x k - (α * (e j : ℂ)) * t k, ?_⟩
  intro i
  apply MvPolynomial.funext
  intro w
  let X₀ := ∑ k, x k * w (i,k)
  let Y₀ := ∑ k, t k * w (i,k)
  have heval (j : Fin r) :
      eval w (rowForm i (fun k => x k - α * (e j : ℂ) * t k)) =
        X₀ - (e j : ℂ) * (α * Y₀) := by
    simp only [rowForm, eval_sum, MvPolynomial.smul_eq_C_mul, eval_mul, eval_C, eval_X]
    simp only [sub_mul, Finset.sum_sub_distrib]
    dsimp [X₀, Y₀]
    simp only [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hprod : (∏ j : Fin r, (X₀ - (e j : ℂ) * (α * Y₀))) =
      ∏ z ∈ S, (X₀ - z * (α * Y₀)) := by
    calc
      _ = ∏ z : S, (X₀ - (z : ℂ) * (α * Y₀)) :=
        Fintype.prod_equiv e _ _ (fun _ => rfl)
      _ = _ := Finset.prod_coe_sort S (fun z : ℂ => X₀ - z * (α * Y₀))
  simp only [eval_add, eval_pow, MvPolynomial.smul_eq_C_mul, eval_mul, eval_C, eval_prod, heval]
  have hx : eval w (rowForm i x) = X₀ := by simp [rowForm, X₀, MvPolynomial.smul_eq_C_mul]
  have hy : eval w (rowForm i t) = Y₀ := by simp [rowForm, Y₀, MvPolynomial.smul_eq_C_mul]
  rw [hx, hy]
  rw [hprod, ← hζ.pow_sub_pow_eq_prod_sub_mul X₀ (α * Y₀) hr, mul_pow, hα]
  ring

abbrev S (n : ℕ) := MvPolynomial (Fin n) ℂ

def rowLift {a n : ℕ} (i : Fin a) : S n →ₐ[ℂ] P a n :=
  rename (fun k => (i,k))

def tensorRows {a n : ℕ} (p : Fin a → S n) : P a n := ∏ i, rowLift i (p i)

def lin {n : ℕ} (x : Fin n → ℂ) : S n := ∑ k, x k • X k

@[simp] lemma rowLift_lin {a n : ℕ} (i : Fin a) (x : Fin n → ℂ) :
    rowLift i (lin x) = rowForm i x := by simp [rowLift, lin, rowForm]

@[simp] lemma renameRow_rowLift {a n : ℕ} (σ : Equiv.Perm (Fin a))
    (i : Fin a) (p : S n) : renameRow σ (rowLift i p) = rowLift (σ i) p := by
  simp [rowLift, renameRow, rename_rename, Function.comp_def]

lemma renameRow_tensorRows {a n : ℕ} (σ : Equiv.Perm (Fin a)) (p : Fin a → S n) :
    renameRow σ (tensorRows p) = tensorRows (fun i => p (σ.symm i)) := by
  simp only [tensorRows, map_prod, renameRow_rowLift]
  apply Fintype.prod_equiv σ
  intro i
  simp

def Symmetric {a n : ℕ} (l : P a n →ₗ[ℂ] ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin a)) (f : P a n), l (renameRow σ f) = l f

lemma symmetric_tensorRows {a n : ℕ} {l : P a n →ₗ[ℂ] ℂ} (hl : Symmetric l)
    (σ : Equiv.Perm (Fin a)) (p : Fin a → S n) :
    l (tensorRows (fun i => p (σ.symm i))) = l (tensorRows p) := by
  rw [← renameRow_tensorRows, hl]

def oneSlot {a n : ℕ} (p q : S n) (i : Fin a) : P a n :=
  tensorRows (fun j => if j = i then q else p)

lemma oneSlot_eq {a n : ℕ} {l : P a n →ₗ[ℂ] ℂ} (hl : Symmetric l)
    (p q : S n) (i j : Fin a) : l (oneSlot p q i) = l (oneSlot p q j) := by
  classical
  have hh := symmetric_tensorRows hl (Equiv.swap i j) (fun k => if k = j then q else p)
  have he : (fun k => if (Equiv.swap i j).symm k = j then q else p) =
      (fun k => if k = i then q else p) := by
    funext k
    simp [Equiv.swap_apply_eq_iff]
  rw [he] at hh
  exact hh

lemma eval_pderiv_prod {A ι σ : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (v : σ) (w : σ → A) (f : ι → MvPolynomial σ A) :
    eval w (pderiv v (∏ i, f i)) =
      ∑ i, eval w (pderiv v (f i)) * ∏ j ∈ Finset.univ.erase i, eval w (f j) := by
  classical
  have hs (s : Finset ι) : eval w (pderiv v (∏ i ∈ s, f i)) =
      ∑ i ∈ s, eval w (pderiv v (f i)) * ∏ j ∈ s.erase i, eval w (f j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert u s hu ih =>
      rw [Finset.prod_insert hu, pderiv_mul, eval_add, eval_mul, eval_mul, ih,
        Finset.sum_insert hu]
      rw [Finset.erase_insert hu]
      simp only [eval_prod, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hne : i ≠ u := ne_of_mem_of_not_mem hi hu
      rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (by simp [hu])]
      ring
  exact hs Finset.univ

lemma binary_coefficient {a n : ℕ} (ha : 0 < a) {l : P a n →ₗ[ℂ] ℂ}
    (hl : Symmetric l) (p q : S n)
    (hz : ∀ c : ℂ, l (tensorRows (fun _ => p + c • q)) = 0) (i : Fin a) :
    l (oneSlot p q i) = 0 := by
  classical
  let F : MvPolynomial Unit (P a n) :=
    ∏ j, (C (rowLift j p) + X () * C (rowLift j q))
  have heval (c : ℂ) : eval (fun _ : Unit => algebraMap ℂ (P a n) c) F =
      tensorRows (fun _ => p + c • q) := by
    simp [F, tensorRows, rowLift, Algebra.smul_def]
  have hF : mapCoeffs l F = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [eval_mapCoeffs]
    have hc : c = fun _ : Unit => c () := funext (fun u => by cases u; rfl)
    rw [hc, heval, hz, map_zero]
  have hd := congrArg (eval (fun _ : Unit => (0 : ℂ)))
    (congrArg (pderiv ()) hF)
  rw [← mapCoeffs_pderiv, eval_mapCoeffs] at hd
  have hD : eval (fun _ : Unit => algebraMap ℂ (P a n) 0) (pderiv () F) =
      ∑ j, oneSlot p q j := by
    dsimp only [F]
    rw [eval_pderiv_prod]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_add, pderiv_C, pderiv_mul, pderiv_X_self, mul_zero,
      add_zero, zero_add, eval_C, eval_mul, eval_X, map_zero, zero_mul]
    rw [oneSlot, tensorRows, ← Finset.mul_prod_erase Finset.univ _ (a := j) (by simp)]
    simp only [ite_true, map_one, one_mul]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [ite_eq_right (Finset.mem_erase.mp hk).1]
  rw [hD, map_sum] at hd
  have hsum : (∑ j : Fin a, l (oneSlot p q j)) = (a : ℂ) * l (oneSlot p q i) := by
    simp_rw [fun j => oneSlot_eq hl p q j i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hd
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  exact (mul_eq_zero.mp (by simpa using hd)).resolve_left haC

end Foulkes.Vanishing

namespace Foulkes.Vanishing
open MvPolynomial Foulkes.PolynomialSpan Foulkes.GenericShift

variable {A : Type*} [CommRing A]

def freeBase {r m n : ℕ} (c : Fin r → Fin n → A) : Poly A (m+1) n :=
  ∏ j : Fin m, ∏ i : Fin r, rowLinear j.castSucc (c i)

def freeFamily {r m n : ℕ} (c : Fin r → Fin n → A) (d : Fin n → A)
    (b : ℕ) (s : Finset (Fin m)) : Poly A (m+1) n :=
  (freeBase c * ∏ j ∈ s, rowLinear j.castSucc d) * rowLinear (Fin.last m) d ^ (b-s.card)

lemma shift_freeBase {r m n : ℕ} (c : Fin r → Fin n → A) (u : Fin m) :
    shift (Fin.last m) u.castSucc (freeBase c) = 0 := by
  apply derivation_prod_zero
  intro j _
  apply derivation_prod_zero
  intro i _
  simp

lemma freeBase_degree_last {r m n : ℕ} (c : Fin r → Fin n → A) :
    (freeBase (m := m) c).IsWeightedHomogeneous (rowWeight (Fin.last m)) 0 := by
  have hi (j : Fin m) (i : Fin r) : (rowLinear j.castSucc (c i)).IsWeightedHomogeneous
      (rowWeight (Fin.last m)) 0 := by simpa using rowLinear_homogeneous j.castSucc (Fin.last m) (c i)
  have hj (j : Fin m) : (∏ i : Fin r, rowLinear j.castSucc (c i)).IsWeightedHomogeneous
      (rowWeight (Fin.last m)) 0 := by
    simpa using MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ (fun i _ => hi j i)
  simpa [freeBase] using MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ (fun j _ => hj j)

lemma freeBase_degree_cast {r m n : ℕ} (c : Fin r → Fin n → A) (u : Fin m) :
    (freeBase c).IsWeightedHomogeneous (rowWeight u.castSucc) r := by
  classical
  have hi (j : Fin m) (i : Fin r) : (rowLinear j.castSucc (c i)).IsWeightedHomogeneous
      (rowWeight u.castSucc) (if j = u then 1 else 0) := by
    simpa using rowLinear_homogeneous j.castSucc u.castSucc (c i)
  have hj (j : Fin m) : (∏ i : Fin r, rowLinear j.castSucc (c i)).IsWeightedHomogeneous
      (rowWeight u.castSucc) (if j = u then r else 0) := by
    have hh := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ (fun i _ => hi j i)
    split_ifs at hh ⊢ <;> simpa using hh
  simpa [freeBase] using MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ (fun j _ => hj j)

lemma freeFamily_degree_last {r m n : ℕ} (c : Fin r → Fin n → A) (d : Fin n → A)
    (b : ℕ) (s : Finset (Fin m)) :
    (freeFamily c d b s).IsWeightedHomogeneous (rowWeight (Fin.last m)) (b-s.card) := by
  have hi (j : Fin m) : (rowLinear j.castSucc d).IsWeightedHomogeneous
      (rowWeight (Fin.last m)) 0 := by simpa using rowLinear_homogeneous j.castSucc (Fin.last m) d
  have hs : (∏ j ∈ s, rowLinear j.castSucc d).IsWeightedHomogeneous (rowWeight (Fin.last m)) 0 := by
    simpa using MvPolynomial.IsWeightedHomogeneous.prod s _ _ (fun j _ => hi j)
  have ht : (rowLinear (Fin.last m) d).IsWeightedHomogeneous (rowWeight (Fin.last m)) 1 := by
    simpa using rowLinear_homogeneous (Fin.last m) (Fin.last m) d
  simpa [freeFamily] using ((freeBase_degree_last c).mul hs).mul (ht.pow (b-s.card))

lemma freeFamily_degree_cast {r m n : ℕ} (c : Fin r → Fin n → A) (d : Fin n → A)
    (b : ℕ) (s : Finset (Fin m)) (u : Fin m) (hu : u ∉ s) :
    (freeFamily c d b s).IsWeightedHomogeneous (rowWeight u.castSucc) r := by
  have hi (j : Fin m) (hj : j ∈ s) : (rowLinear j.castSucc d).IsWeightedHomogeneous
      (rowWeight u.castSucc) 0 := by
    have hne : j ≠ u := ne_of_mem_of_not_mem hj hu
    simpa [hne] using rowLinear_homogeneous j.castSucc u.castSucc d
  have hs : (∏ j ∈ s, rowLinear j.castSucc d).IsWeightedHomogeneous (rowWeight u.castSucc) 0 := by
    simpa using MvPolynomial.IsWeightedHomogeneous.prod s _ _ hi
  have ht : (rowLinear (Fin.last m) d).IsWeightedHomogeneous (rowWeight u.castSucc) 0 := by
    simpa [Ne.symm (Fin.castSucc_ne_last u)] using rowLinear_homogeneous (Fin.last m) u.castSucc d
  simpa [freeFamily] using ((freeBase_degree_cast c u).mul hs).mul (ht.pow (b-s.card))

lemma shift_freeFamily {r m n : ℕ} (c : Fin r → Fin n → A) (d : Fin n → A)
    (b : ℕ) (s : Finset (Fin m)) (u : Fin m) (hu : u ∉ s) (hs : s.card < b) :
    shift (Fin.last m) u.castSucc (freeFamily c d b s) =
      (b-s.card) • freeFamily c d b (insert u s) := by
  classical
  let D := shift (A := A) (n := n) (Fin.last m) u.castSucc
  have hG : D (freeBase c * ∏ j ∈ s, rowLinear j.castSucc d) = 0 := by
    rw [D.leibniz, shift_freeBase]
    have hz : D (∏ j ∈ s, rowLinear j.castSucc d) = 0 := by
      apply derivation_prod_zero
      intro j _
      simp [D]
    rw [hz]
    simp
  have hder := pow_apply_pow D (f := rowLinear (Fin.last m) d)
    (g := rowLinear u.castSucc d) (by simp [D]) (by simp [D]) (b-s.card) 1 (by omega)
  simp only [pow_one, Derivation.coeFn_coe, Nat.descFactorial_one] at hder
  change D (_ * _) = _
  rw [D.leibniz, hG, smul_zero, add_zero, hder]
  simp only [freeFamily, Finset.prod_insert hu, Finset.card_insert_of_notMem hu,
    smul_eq_mul, nsmul_eq_mul]
  have he : b-s.card-1 = b-(s.card+1) := by omega
  rw [he]
  ring

theorem freeFamily_zero [Algebra ℂ A] {r m n b : ℕ}
    (c : Fin r → Fin n → A) (d : Fin n → A) (l : A →ₗ[ℂ] ℂ)
    (hb : m+r ≤ b) (hz : mapCoeffs l (freeFamily (m := m) c d b Finset.univ) = 0) :
    mapCoeffs l (freeFamily (m := m) c d b ∅) = 0 := by
  classical
  have ht (t : Finset (Fin m)) :
      mapCoeffs l (freeFamily c d b (Finset.univ \ t)) = 0 := by
    induction t using Finset.induction_on with
    | empty => simpa using hz
    | insert u t hu ih =>
      let s : Finset (Fin m) := Finset.univ \ insert u t
      have hus : u ∉ s := by simp [s]
      have hse : insert u s = Finset.univ \ t := by
        ext i
        by_cases hi : i = u <;> simp [s, hi, hu]
      have hcard : s.card + 1 ≤ m := by
        calc
          s.card + 1 = (insert u s).card := (Finset.card_insert_of_notMem hus).symm
          _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = m := by simp
      change mapCoeffs l (freeFamily c d b s) = 0
      apply Differential.shift_kernel_zero (u := Fin.last m) (v := u.castSucc) (Ne.symm (Fin.castSucc_ne_last u))
        (homogeneous_mapCoeffs l _ (freeFamily_degree_last c d b s))
        (homogeneous_mapCoeffs l _ (freeFamily_degree_cast c d b s u hus)) (by omega)
      change shift (Fin.last m) u.castSucc (mapCoeffs l (freeFamily c d b s)) = 0
      rw [← mapCoeffs_shift, shift_freeFamily c d b s u hus (by omega), hse]
      change (mapCoeffsLM l) ((b-s.card) • freeFamily c d b (Finset.univ \ t)) = 0
      rw [map_nsmul]
      change (b-s.card) • mapCoeffs l (freeFamily c d b (Finset.univ \ t)) = 0
      rw [ih, smul_zero]
  simpa using ht Finset.univ

end Foulkes.Vanishing

namespace Foulkes.Vanishing
open MvPolynomial Foulkes.Polarization Foulkes.PolynomialSpan

lemma lin_binary_split {n r : ℕ} (hr : 0 < r) (c : ℂ) (x t : Fin n → ℂ) :
    ∃ v : Fin r → Fin n → ℂ, lin x ^ r + c • lin t ^ r = ∏ j, lin (v j) := by
  obtain ⟨v,hv⟩ := binary_split (a := 1) hr c x t
  refine ⟨v, ?_⟩
  have hh := congrArg (rename (Prod.snd : Fin 1 × Fin n → Fin n)) (hv 0)
  simpa [rowForm, lin] using hh

def vecProduct {m n : ℕ} (y : Fin m → Fin n → ℂ) : S n := ∏ j, lin (y j)

def ProductsVanish {a n : ℕ} (l : P a n →ₗ[ℂ] ℂ) (b : ℕ) : Prop :=
  ∀ y : Fin b → Fin n → ℂ, l (∏ j, z (y j)) = 0

lemma tensorRows_diag_product {a m n : ℕ} (y : Fin m → Fin n → ℂ) :
    tensorRows (a := a) (fun _ => vecProduct y) = ∏ j, z (y j) := by
  simp only [tensorRows, vecProduct, map_prod, rowLift_lin, z]
  exact Finset.prod_comm

lemma productsVanish_mul {a n r m : ℕ} {l : P a n →ₗ[ℂ] ℂ}
    (hl : ProductsVanish l (r+m)) (u : Fin r → Fin n → ℂ) (v : Fin m → Fin n → ℂ) :
    l (tensorRows (fun _ => vecProduct u * vecProduct v)) = 0 := by
  have hh := hl (Fin.addCases u v)
  rw [Fin.prod_univ_add] at hh
  simp only [Fin.addCases_left, Fin.addCases_right] at hh
  have he : tensorRows (a := a) (fun _ => vecProduct u * vecProduct v) =
      (∏ i, z (u i)) * ∏ j, z (v j) := by
    simp only [tensorRows, map_mul, Finset.prod_mul_distrib]
    rw [← tensorRows, ← tensorRows, tensorRows_diag_product, tensorRows_diag_product]
  rwa [he]

lemma binary_step {r m n : ℕ} (hr : 0 < r) {l : P (r+1) n →ₗ[ℂ] ℂ}
    (hs : Symmetric l) (hz : ProductsVanish l (r+m))
    (x t : Fin n → ℂ) (y : Fin m → Fin n → ℂ) :
    l (oneSlot (lin x ^ r * vecProduct y) (lin t ^ r * vecProduct y) (Fin.last r)) = 0 := by
  apply binary_coefficient (by omega) hs
  intro c
  obtain ⟨u, hu⟩ := lin_binary_split hr c x t
  have he : lin x ^ r * vecProduct y + c • (lin t ^ r * vecProduct y) =
      vecProduct u * vecProduct y := by
    rw [← smul_mul_assoc, ← add_mul, hu]
    rfl
  rw [he]
  exact productsVanish_mul hz u y

lemma oneSlot_last {r n : ℕ} (p q : S n) :
    oneSlot p q (Fin.last r) = (∏ i : Fin r, rowLift i.castSucc p) * rowLift (Fin.last r) q := by
  rw [oneSlot, tensorRows, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ite_false, ite_true]

def commonPower {r n : ℕ} (x : Fin n → ℂ) : P (r+1) n :=
  ∏ i : Fin r, rowForm i.castSucc x ^ r

def fixedFunctional {r n : ℕ} (l : P (r+1) n →ₗ[ℂ] ℂ) (x : Fin n → ℂ) :
    P (r+1) n →ₗ[ℂ] ℂ := l.comp (LinearMap.mulLeft ℂ (commonPower x))

@[simp] lemma fixedFunctional_apply {r n : ℕ} (l : P (r+1) n →ₗ[ℂ] ℂ)
    (x : Fin n → ℂ) (f : P (r+1) n) :
    fixedFunctional l x f = l (commonPower x * f) := rfl

lemma eval_freeFamily {r m n b : ℕ} (s : Finset (Fin m))
    (w : Fin (m+1) × Fin n → ℂ) :
    eval (fun ij => algebraMap ℂ (P (r+1) n) (w ij))
      (freeFamily (fun i : Fin r => fun k => (X (i.castSucc,k) : P (r+1) n))
        (fun k => X (Fin.last r,k)) b s) =
      ((∏ j : Fin m, ∏ i : Fin r, rowForm i.castSucc (fun k => w (j.castSucc,k))) *
        ∏ j ∈ s, rowForm (Fin.last r) (fun k => w (j.castSucc,k))) *
          rowForm (Fin.last r) (fun k => w (Fin.last m,k)) ^ (b-s.card) := by
  simp only [freeFamily, freeBase, map_mul, map_prod, map_pow, GenericShift.eval_rowLinear, rowForm]

lemma free_last_slot {r m n : ℕ} (hr : 0 < r) {l : P (r+1) n →ₗ[ℂ] ℂ}
    (hs : Symmetric l) (hz : ProductsVanish l (r+m))
    (x t : Fin n → ℂ) (y : Fin m → Fin n → ℂ) :
    l ((∏ i : Fin r, rowLift i.castSucc (lin x ^ r * vecProduct y)) *
      rowForm (Fin.last r) t ^ (r+m)) = 0 := by
  let c := fun i : Fin r => fun k : Fin n => (X (i.castSucc,k) : P (r+1) n)
  let d := fun k : Fin n => (X (Fin.last r,k) : P (r+1) n)
  have hfull : mapCoeffs (fixedFunctional l x)
      (freeFamily (m := m) c d (r+m) Finset.univ) = 0 := by
    apply MvPolynomial.funext
    intro w
    rw [eval_mapCoeffs]
    simp only [c, d, eval_freeFamily, Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel_right, fixedFunctional_apply, map_zero]
    have hh := binary_step hr hs hz x (fun k => w (Fin.last m,k))
      (fun j k => w (j.castSucc,k))
    rw [oneSlot_last] at hh
    simp only [map_mul, map_pow, rowLift_lin, vecProduct, map_prod,
      Finset.prod_mul_distrib] at hh
    have hcomm : (∏ i : Fin r, ∏ j : Fin m, rowForm i.castSucc (fun k => w (j.castSucc,k))) =
        ∏ j : Fin m, ∏ i : Fin r, rowForm i.castSucc (fun k => w (j.castSucc,k)) := Finset.prod_comm
    rw [hcomm] at hh
    convert hh using 1
    dsimp only [commonPower]
    congr 1
    ring
  have hzero := freeFamily_zero c d (fixedFunctional l x) (by omega : m+r ≤ r+m) hfull
  let w : Fin (m+1) × Fin n → ℂ := fun ij => Fin.lastCases (t ij.2) (fun j => y j ij.2) ij.1
  have hh := congrArg (eval w) hzero
  rw [eval_mapCoeffs] at hh
  simp only [c, d, eval_freeFamily, Finset.prod_empty, Finset.card_empty, Nat.sub_zero,
    mul_one, fixedFunctional_apply, map_zero, w, Fin.lastCases_castSucc, Fin.lastCases_last] at hh
  simp only [commonPower] at hh
  simp only [map_mul, map_pow, rowLift_lin, vecProduct, map_prod, Finset.prod_mul_distrib]
  have hcomm : (∏ i : Fin r, ∏ j : Fin m, rowForm i.castSucc (y j)) =
      ∏ j : Fin m, ∏ i : Fin r, rowForm i.castSucc (y j) := Finset.prod_comm
  rw [hcomm]
  simpa only [mul_assoc] using hh

end Foulkes.Vanishing

end

end OAI
