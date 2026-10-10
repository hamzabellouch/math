import OAI.NumberTheory.PowerFree.RegularBlocks

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open MvPolynomial
open scoped Matrix

theorem mv_eval_sub_dvd {σ R : Type*} [CommRing R]
    (q : R) (P : MvPolynomial σ R) (x y : σ → R)
    (hxy : ∀ i, q ∣ x i - y i) : q ∣ eval x P - eval y P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hP hQ
  | mul_X P i hP =>
    have h := dvd_add (dvd_mul_of_dvd_left hP (x i))
      (dvd_mul_of_dvd_right (hxy i) (eval y P))
    simpa only [map_mul, eval_X] using (show q ∣ eval x P * x i - eval y P * y i by
      convert h using 1; ring)

theorem mv_eval_sub_linear_dvd {σ R : Type*} [Fintype σ] [CommRing R]
    (q : R) (s : ℕ) (P : MvPolynomial σ R) (x y : σ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ i, q ∣ y i)
    (hxy : ∀ i, q ^ s ∣ x i - y i) :
    q ^ (s + 1) ∣ eval x P - eval y P -
      ∑ i, eval (fun _ => 0) (pderiv i P) * (x i - y i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    convert dvd_add hP hQ using 1
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X P i hP =>
    have h1 : q ^ (s + 1) ∣ (eval x P - eval y P) * x i := by
      simpa only [pow_succ] using mul_dvd_mul (mv_eval_sub_dvd (q ^ s) P x y hxy) (hx i)
    have h2 : q ^ (s + 1) ∣ (eval y P - eval (fun _ => 0) P) * (x i - y i) := by
      have h0 : q ∣ eval y P - eval (fun _ => 0) P :=
        mv_eval_sub_dvd q P y (fun _ => 0) (by simpa using hy)
      simpa only [pow_succ, mul_comm q] using mul_dvd_mul h0 (hxy i)
    have hs : (∑ j, eval (fun _ => 0) (pderiv j (P * X i)) * (x j - y j)) =
        eval (fun _ => 0) P * (x i - y i) := by
      simp [pderiv_X, Pi.single_apply, apply_ite]
    rw [hs, map_mul, map_mul, eval_X, eval_X]
    convert dvd_add h1 h2 using 1; ring

theorem mv_eval_substitute {σ τ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (F : σ → MvPolynomial τ R) (x : τ → R) :
    eval x (eval₂ C F P) = eval (fun i => eval x (F i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [eval₂_mul, hP]

noncomputable def implicitApprox {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R) : ℕ → κ → MvPolynomial ι R
  | 0, _ => 0
  | n + 1, j => eval₂ C (Sum.elim X (implicitApprox Φ n)) (Φ j)

 theorem eval_implicitApprox_succ {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R) (n : ℕ) (x : ι → R) (j : κ) :
    eval x (implicitApprox Φ (n + 1) j) =
      eval (Sum.elim x (fun a => eval x (implicitApprox Φ n a))) (Φ j) := by
  rw [implicitApprox, mv_eval_substitute]
  congr 2
  funext a
  cases a <;> simp

 theorem implicitApprox_zero {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0) (n : ℕ) (j : κ) :
    eval (fun _ => 0) (implicitApprox Φ n j) = 0 := by
  induction n generalizing j with
  | zero => simp [implicitApprox]
  | succ n ih =>
    rw [eval_implicitApprox_succ]
    have hn : (Sum.elim (fun _ : ι => (0 : R))
        (fun a => eval (fun _ => 0) (implicitApprox Φ n a))) = (fun _ => 0) := by
      funext a
      cases a with
      | inl a => rfl
      | inr a => exact ih a
    rw [hn]
    exact hzero j

theorem implicit_map_contraction {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (s : ℕ) (x : ι → R) (y z : κ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ j, q ∣ y j) (hz : ∀ j, q ∣ z j)
    (hyz : ∀ j, q ^ s ∣ y j - z j) (j : κ) :
    q ^ (s + 1) ∣ eval (Sum.elim x y) (Φ j) - eval (Sum.elim x z) (Φ j) := by
  have hv : ∀ i, q ∣ (Sum.elim x y) i := by intro i; cases i <;> simp_all
  have hw : ∀ i, q ∣ (Sum.elim x z) i := by intro i; cases i <;> simp_all
  have hvw : ∀ i, q ^ s ∣ (Sum.elim x y) i - (Sum.elim x z) i := by
    intro i
    cases i <;> simp_all
  have h := mv_eval_sub_linear_dvd q s (Φ j) (Sum.elim x y) (Sum.elim x z) hv hw hvw
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self,
    mul_zero, hlinear, zero_mul, Finset.sum_const_zero, add_zero, sub_zero] using h

theorem implicitApprox_error_dvd {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (y : κ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ j, q ∣ y j)
    (hfix : ∀ j, eval (Sum.elim x y) (Φ j) = y j) (n : ℕ) (j : κ) :
    q ^ (n + 1) ∣ y j - eval x (implicitApprox Φ n j) := by
  induction n generalizing j with
  | zero => simpa only [implicitApprox, map_zero, sub_zero, zero_add, pow_one] using hy j
  | succ n ih =>
    have hn : ∀ a, q ∣ eval x (implicitApprox Φ n a) := by
      intro a
      have h := mv_eval_sub_dvd q (implicitApprox Φ n a) x (fun _ => 0)
        (by simpa only [sub_zero] using hx)
      simpa only [implicitApprox_zero Φ hzero, sub_zero] using h
    have h := implicit_map_contraction Φ hlinear q (n + 1) x y
      (fun a => eval x (implicitApprox Φ n a)) hx hy hn
      ih j
    rwa [hfix, ← eval_implicitApprox_succ] at h

noncomputable def implicitJacobian {ι κ R : Type*} [CommRing R]
    (G : κ → MvPolynomial (ι ⊕ κ) R) : Matrix κ κ R :=
  Matrix.of (fun j a => eval (fun _ => 0) (pderiv (Sum.inr a) (G j)))

noncomputable def normalizedImplicitMap {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (j : κ) : MvPolynomial (ι ⊕ κ) R :=
  X (Sum.inr j) - ∑ a, C ((implicitJacobian G)⁻¹ j a) * G a

theorem normalizedImplicitMap_zero {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0) (j : κ) :
    eval (fun _ => 0) (normalizedImplicitMap G j) = 0 := by
  simp only [normalizedImplicitMap, map_sub, map_sum, map_mul, eval_X, eval_C,
    hzero, mul_zero, Finset.sum_const_zero, sub_zero]

theorem normalizedImplicitMap_linear {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hunit : IsUnit (implicitJacobian G).det) (j a : κ) :
    eval (fun _ => 0) (pderiv (Sum.inr a) (normalizedImplicitMap G j)) = 0 := by
  classical
  have hmat := congrArg (fun M : Matrix κ κ R => M j a)
    (Matrix.nonsing_inv_mul (implicitJacobian G) hunit)
  simp only [Matrix.mul_apply, Matrix.one_apply] at hmat
  have hs : (∑ b, (implicitJacobian G)⁻¹ j b *
      eval (fun _ => 0) (pderiv (Sum.inr a) (G b))) = if j = a then 1 else 0 := hmat
  simp only [normalizedImplicitMap, map_sub, map_sum, pderiv_mul, pderiv_C,
    zero_mul, zero_add, pderiv_X, Pi.single_apply, map_mul, eval_C]
  rw [hs]
  by_cases h : j = a <;> simp [h]

theorem normalizedImplicitMap_fixed {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (x : ι → R) (y : κ → R)
    (hroot : ∀ j, eval (Sum.elim x y) (G j) = 0) (j : κ) :
    eval (Sum.elim x y) (normalizedImplicitMap G j) = y j := by
  simp [normalizedImplicitMap, hroot]

theorem smooth_patch_polynomial_approx {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (implicitJacobian G).det) (q : R) (n : ℕ) :
    ∃ F : κ → MvPolynomial ι R,
      (∀ j, eval (fun _ => 0) (F j) = 0) ∧
      ∀ (x : ι → R) (y : κ → R), (∀ i, q ∣ x i) → (∀ j, q ∣ y j) →
        (∀ j, eval (Sum.elim x y) (G j) = 0) →
        ∀ j, q ^ (n + 1) ∣ y j - eval x (F j) := by
  refine ⟨implicitApprox (normalizedImplicitMap G) n, ?_, ?_⟩
  · exact implicitApprox_zero _ (normalizedImplicitMap_zero G hzero) n
  · intro x y hx hy hroot j
    exact implicitApprox_error_dvd _ (normalizedImplicitMap_zero G hzero)
      (normalizedImplicitMap_linear G hunit) q x y hx hy
      (normalizedImplicitMap_fixed G x y hroot) n j

theorem implicitApprox_eval_dvd {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) (n : ℕ) (j : κ) :
    q ∣ eval x (implicitApprox Φ n j) := by
  have h := mv_eval_sub_dvd q (implicitApprox Φ n j) x (fun _ => 0)
    (by simpa only [sub_zero] using hx)
  simpa only [implicitApprox_zero Φ hzero, sub_zero] using h

theorem implicitApprox_step_dvd {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) (n : ℕ) (j : κ) :
    q ^ (n + 1) ∣ eval x (implicitApprox Φ (n + 1) j) -
      eval x (implicitApprox Φ n j) := by
  induction n generalizing j with
  | zero =>
    simpa only [zero_add, pow_one, implicitApprox, map_zero, sub_zero] using
      implicitApprox_eval_dvd Φ hzero q x hx 1 j
  | succ n ih =>
    rw [eval_implicitApprox_succ, eval_implicitApprox_succ Φ n]
    exact implicit_map_contraction Φ hlinear q (n + 1) x
      (fun j => eval x (implicitApprox Φ (n + 1) j))
      (fun j => eval x (implicitApprox Φ n j)) hx
      (implicitApprox_eval_dvd Φ hzero q x hx (n + 1))
      (implicitApprox_eval_dvd Φ hzero q x hx n) ih j

theorem implicitApprox_later_dvd {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) {n m : ℕ} (hnm : n ≤ m) (j : κ) :
    q ^ (n + 1) ∣ eval x (implicitApprox Φ m j) -
      eval x (implicitApprox Φ n j) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have hs := (pow_dvd_pow q (Nat.add_le_add_right hnm 1)).trans
      (implicitApprox_step_dvd Φ hzero hlinear q x hx m j)
    simpa only [sub_add_sub_cancel] using dvd_add hs ih

theorem exists_implicit_powerSeries_fixed {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [CommRing K] (Φ : κ → MvPolynomial (ι ⊕ κ) (PowerSeries K))
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (x : ι → PowerSeries K) (hx : ∀ i, PowerSeries.X ∣ x i) :
    ∃ y : κ → PowerSeries K, (∀ j, PowerSeries.constantCoeff (y j) = 0) ∧
      ∀ j, eval (Sum.elim x y) (Φ j) = y j := by
  let v := fun n j => eval x (implicitApprox Φ n j)
  let y : κ → PowerSeries K := fun j =>
    PowerSeries.mk (fun n => PowerSeries.coeff n (v n j))
  have happ : ∀ n j, PowerSeries.X ^ (n + 1) ∣ y j - v n j := by
    intro n j
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    have he := PowerSeries.X_pow_dvd_iff.mp
      (implicitApprox_later_dvd Φ hzero hlinear PowerSeries.X x hx
        (Nat.le_of_lt_succ hi) j) i (Nat.lt_succ_self i)
    change PowerSeries.coeff i (v n j - v i j) = 0 at he
    simp only [map_sub] at he
    simp only [map_sub, y, PowerSeries.coeff_mk]
    exact sub_eq_zero.mpr (sub_eq_zero.mp he).symm
  refine ⟨y, ?_, ?_⟩
  · intro j
    have h := happ 0 j
    simpa only [zero_add, pow_one, v, implicitApprox, map_zero, sub_zero,
      PowerSeries.X_dvd_iff] using h
  · intro j
    apply sub_eq_zero.mp
    apply PowerSeries.ext
    intro n
    have hdiff : ∀ a, PowerSeries.X ^ (n + 1) ∣
        (Sum.elim x y) a - (Sum.elim x (v n)) a := by
      intro a
      cases a with
      | inl i => simp
      | inr j => exact happ n j
    have h1 := mv_eval_sub_dvd (PowerSeries.X ^ (n + 1)) (Φ j)
      (Sum.elim x y) (Sum.elim x (v n)) hdiff
    have h2 := implicitApprox_step_dvd Φ hzero hlinear PowerSeries.X x hx n j
    have h3 := dvd_neg.mpr (happ n j)
    have hs := dvd_add (dvd_add h1 h2) h3
    have ht : PowerSeries.X ^ (n + 1) ∣ eval (Sum.elim x y) (Φ j) - y j := by
      convert hs using 1
      rw [eval_implicitApprox_succ]
      dsimp [v]
      ring
    have he := PowerSeries.X_pow_dvd_iff.mp ht n (Nat.lt_succ_self n)
    simpa only [map_zero] using he

theorem normalizedImplicitMap_root {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hunit : IsUnit (implicitJacobian G).det) (x : ι → R) (y : κ → R)
    (hfix : ∀ j, eval (Sum.elim x y) (normalizedImplicitMap G j) = y j) :
    ∀ j, eval (Sum.elim x y) (G j) = 0 := by
  let v : κ → R := fun j => eval (Sum.elim x y) (G j)
  have hv : (implicitJacobian G)⁻¹ *ᵥ v = 0 := by
    funext j
    have h := hfix j
    simp only [normalizedImplicitMap, map_sub, map_sum, map_mul, eval_X, eval_C] at h
    simpa only [Matrix.mulVec, dotProduct, v, Pi.zero_apply] using (sub_eq_self.mp h)
  have h := congrArg (Matrix.mulVec (implicitJacobian G)) hv
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact fun j => congrFun h j

theorem exists_implicit_powerSeries_root {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [CommRing K] (G : κ → MvPolynomial (ι ⊕ κ) (PowerSeries K))
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (implicitJacobian G).det)
    (x : ι → PowerSeries K) (hx : ∀ i, PowerSeries.X ∣ x i) :
    ∃ y : κ → PowerSeries K, (∀ j, PowerSeries.constantCoeff (y j) = 0) ∧
      ∀ j, eval (Sum.elim x y) (G j) = 0 := by
  obtain ⟨y, hy, hfix⟩ := exists_implicit_powerSeries_fixed (normalizedImplicitMap G)
    (normalizedImplicitMap_zero G hzero) (normalizedImplicitMap_linear G hunit) x hx
  exact ⟨y, hy, normalizedImplicitMap_root G hunit x y hfix⟩

noncomputable def shiftedParameterPolynomial {κ R : Type*} [CommRing R]
    (a : κ → R) : MvPolynomial κ R →+* MvPolynomial (Unit ⊕ κ) R :=
  eval₂Hom C (fun i => X (Sum.inr i) + C (a i))

@[simp] theorem eval_shiftedParameterPolynomial {κ R : Type*} [CommRing R]
    (a : κ → R) (p : MvPolynomial κ R) (z : Unit ⊕ κ → R) :
    eval z (shiftedParameterPolynomial a p) = eval (fun i => z (Sum.inr i) + a i) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [shiftedParameterPolynomial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [shiftedParameterPolynomial]

theorem pderiv_shiftedParameterPolynomial {κ R : Type*} [CommRing R]
    (a : κ → R) (p : MvPolynomial κ R) (i : κ) :
    pderiv (Sum.inr i) (shiftedParameterPolynomial a p) =
      shiftedParameterPolynomial a (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [shiftedParameterPolynomial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, pderiv_mul, hp, map_add]
    simp only [shiftedParameterPolynomial, eval₂Hom_X', map_add, pderiv_X,
      pderiv_C, add_zero, Pi.single_apply, Sum.inr.injEq]
    split_ifs <;> simp

theorem exists_deformed_powerSeries_root {κ K : Type*} [Fintype κ] [DecidableEq κ]
    [Field K] (f : κ → MvPolynomial κ K) (a : κ → K)
    (ha : ∀ j, eval a (f j) = 0)
    (hJ : (Matrix.of (fun i j => eval a (pderiv j (f i)))).det ≠ 0) (D : ℕ) :
    ∃ y : κ → PowerSeries K,
      (∀ j, PowerSeries.constantCoeff (y j) = a j) ∧
      ∀ j, eval₂ PowerSeries.C y (f j) + PowerSeries.X * y j ^ (D + 1) = 0 := by
  let a' : κ → PowerSeries K := fun j => PowerSeries.C (a j)
  let f' : κ → MvPolynomial κ (PowerSeries K) := fun j => map PowerSeries.C (f j)
  let G : κ → MvPolynomial (Unit ⊕ κ) (PowerSeries K) := fun j =>
    shiftedParameterPolynomial a' (f' j) +
      X (Sum.inl ()) * (X (Sum.inr j) + C (a' j)) ^ (D + 1)
  have hzero : ∀ j, eval (fun _ => 0) (G j) = 0 := by
    intro j
    simp only [G, map_add, eval_shiftedParameterPolynomial, zero_add, map_mul,
      eval_X, zero_mul, add_zero, f', a']
    rw [← eval₂_eq_eval_map]
    simpa only [Function.comp_def, ha, map_zero] using
      (eval₂_comp PowerSeries.C a (f j)).symm
  have hjac : implicitJacobian G =
      (Matrix.of (fun i j => eval a (pderiv j (f i)))).map PowerSeries.C := by
    apply Matrix.ext
    intro i j
    simp only [implicitJacobian, Matrix.of_apply, Matrix.map_apply, G, map_add,
      pderiv_shiftedParameterPolynomial, pderiv_mul, pderiv_X, Pi.single_apply,
      Sum.inl_ne_inr, ite_false, zero_mul, zero_add, eval_X, map_mul, map_add,
      zero_mul, add_zero, eval_shiftedParameterPolynomial, zero_add, f', pderiv_map, a']
    rw [← eval₂_eq_eval_map]
    exact (eval₂_comp PowerSeries.C a (pderiv j (f i))).symm
  have hunit : IsUnit (implicitJacobian G).det := by
    rw [hjac, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hJ).map PowerSeries.C
  obtain ⟨v, hv, hroot⟩ := exists_implicit_powerSeries_root G hzero hunit
    (fun _ => PowerSeries.X) (fun _ => dvd_refl _)
  refine ⟨fun j => v j + a' j, ?_, ?_⟩
  · intro j
    simp [hv, a']
  · intro j
    have h := hroot j
    simp only [G, map_add, eval_shiftedParameterPolynomial, Sum.elim_inr, map_mul,
      eval_X, Sum.elim_inl, map_pow, eval_C, f', ← eval₂_eq_eval_map] at h
    exact h

end QuarticPowerFree

end OAI
