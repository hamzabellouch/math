import Mathlib

namespace OAI

noncomputable section
namespace PiExponent.CommutingTaylor

open Finset Nat
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def iter (D : Derivation ℚ R R) (n : ℕ) : R →ₗ[ℚ] R := D.toLinearMap ^ n

@[simp] theorem iter_zero (D : Derivation ℚ R R) (a : R) : iter D 0 a = a := rfl
@[simp] theorem iter_succ (D : Derivation ℚ R R) (n : ℕ) (a : R) :
    iter D (n+1) a = D (iter D n a) := by
  change (D.toLinearMap ^ (n + 1)) a = D ((D.toLinearMap ^ n) a)
  calc
    (D.toLinearMap ^ (n + 1)) a = (D.toLinearMap * D.toLinearMap ^ n) a :=
      congrArg (fun f : Module.End ℚ R => f a) (_root_.pow_succ' D.toLinearMap n)
    _ = D.toLinearMap ((D.toLinearMap ^ n) a) :=
      Module.End.mul_apply D.toLinearMap (D.toLinearMap ^ n) a
    _ = D ((D.toLinearMap ^ n) a) :=
      congrFun (Derivation.coeFn_coe D) ((D.toLinearMap ^ n) a)

theorem iter_mul (D : Derivation ℚ R R) (n : ℕ) (a b : R) :
    iter D n (a*b) = ∑ ij ∈ antidiagonal n,
      n.choose ij.1 • (iter D ij.1 a * iter D ij.2 b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (fun i j => iter D i a * iter D j b) n]
    simp only [iter_succ, ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, nsmul_add, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]
    rw [mul_comm]

private theorem factorial_normalize (i j : ℕ) :
    (1 / ((i+j).factorial : ℚ)) * ((i+j).choose i : ℚ) =
      (1 / (i.factorial : ℚ)) * (1 / (j.factorial : ℚ)) := by
  have h : (((i+j).choose i : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ)) =
      ((i+j).factorial : ℚ) := by
    exact_mod_cast (by
      simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j) :
        (i+j).choose i * i.factorial * j.factorial = (i+j).factorial)
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hn : ((i+j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i+j)
  field_simp
  nlinarith [h]

def taylorSeries (D : Derivation ℚ R R) (a : R) : PowerSeries R :=
  PowerSeries.mk fun n => (1 / (n.factorial : ℚ)) • iter D n a

@[simp] theorem coeff_taylorSeries (D : Derivation ℚ R R) (a : R) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries D a) = (1 / (n.factorial : ℚ)) • iter D n a := by
  exact PowerSeries.coeff_mk n _

theorem taylorSeries_mul (D : Derivation ℚ R R) (a b : R) :
    taylorSeries D (a*b) = taylorSeries D a * taylorSeries D b := by
  ext n
  rw [PowerSeries.coeff_mul, coeff_taylorSeries, iter_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  rw [coeff_taylorSeries, coeff_taylorSeries]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_mul_smul_comm]
  rw [← hn, factorial_normalize]

def taylorHom (D : Derivation ℚ R R) : R →+* PowerSeries R where
  toFun := taylorSeries D
  map_zero' := by ext n; simp [taylorSeries]
  map_one' := by
    ext n
    cases n with
    | zero => simp [taylorSeries]
    | succ n =>
      have h : iter D (n+1) (1:R) = 0 := by
        induction n with
        | zero => simp
        | succ n ih => simp [ih]
      simp [taylorSeries, h]
  map_add' a b := by ext n; simp [taylorSeries, smul_add]
  map_mul' := taylorSeries_mul D

@[simp] theorem coeff_taylorHom (D : Derivation ℚ R R) (a : R) (n : ℕ) :
    PowerSeries.coeff n (taylorHom D a) = (1 / (n.factorial : ℚ)) • iter D n a := by
  exact coeff_taylorSeries D a n

@[simp] theorem constantCoeff_taylorHom (D : Derivation ℚ R R) (a : R) :
    PowerSeries.constantCoeff (taylorHom D a) = a := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_taylorHom]
  simp

def mixedIter : (m : ℕ) → (Fin m → Derivation ℚ R R) → (Fin m →₀ ℕ) → R →ₗ[ℚ] R
  | 0, _, _ => LinearMap.id
  | m+1, D, α => (mixedIter m (fun i => D i.succ) α.tail).comp (iter (D 0) (α 0))

def taylorHomFin : (m : ℕ) → (Fin m → Derivation ℚ R R) → R →+* MvPowerSeries (Fin m) R
  | 0, _ => MvPowerSeries.C
  | m+1, D => (MvPowerSeries.finSuccEquiv R m).symm.toRingHom.comp
      ((PowerSeries.map (taylorHomFin m (fun i => D i.succ))).comp (taylorHom (D 0)))

theorem coeff_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (α : Fin m →₀ ℕ) (a : R) :
    MvPowerSeries.coeff α (taylorHomFin m D a) =
      (∏ i, (1 / ((α i).factorial : ℚ))) • mixedIter m D α a := by
  induction m generalizing a with
  | zero =>
    have hα : α = 0 := Subsingleton.elim _ _
    simp [taylorHomFin, mixedIter, hα]
  | succ m ih =>
    have hcoeff := MvPowerSeries.coeff_coeff_finSuccEquiv
      ((MvPowerSeries.finSuccEquiv R m).symm
        (PowerSeries.map (taylorHomFin m (fun i => D i.succ)) (taylorHom (D 0) a)))
      (k := α 0) (x := α.tail)
    simp only [AlgEquiv.apply_symm_apply] at hcoeff
    rw [show α.tail.cons (α 0) = α by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp] at hcoeff
    rw [taylorHomFin, RingHom.comp_apply, RingHom.comp_apply]
    change MvPowerSeries.coeff α ((MvPowerSeries.finSuccEquiv R m).symm
      (PowerSeries.map (taylorHomFin m (fun i => D i.succ)) (taylorHom (D 0) a))) = _
    rw [← hcoeff, PowerSeries.coeff_map, coeff_taylorHom, ih]
    simp only [map_smul, mixedIter, LinearMap.comp_apply, Fin.prod_univ_succ,
      Finsupp.tail_apply, smul_smul]
    rw [mul_comm]

@[simp] theorem mixedIter_zero (m : ℕ) (D : Fin m → Derivation ℚ R R) (a : R) :
    mixedIter m D 0 a = a := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    have ht : (0 : Fin (m+1) →₀ ℕ).tail = 0 := by ext i; rfl
    simp [mixedIter, ht, ih]

@[simp] theorem mixedIter_single (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (i : Fin m) (a : R) : mixedIter m D (Finsupp.single i 1) a = D i a := by
  induction m generalizing a with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← Finsupp.cons_zero_eq_single_zero]
      simp [mixedIter, iter]
    · rw [← Finsupp.cons_zero_single_eq_single_succ]
      simp [mixedIter, ih]

@[simp] theorem coeff_zero_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R) (a : R) :
    MvPowerSeries.coeff 0 (taylorHomFin m D a) = a := by
  simp [coeff_taylorHomFin]

@[simp] theorem coeff_single_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (i : Fin m) (a : R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (taylorHomFin m D a) = D i a := by
  rw [coeff_taylorHomFin, mixedIter_single]
  have h : (∏ j : Fin m, (1 / ((Finsupp.single i 1 j).factorial : ℚ))) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    by_cases he : i = j <;> simp [he]
  rw [h, one_smul]

def residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) :
    R →+* MvPowerSeries (Fin m) K :=
  (MvPowerSeries.map ρ).comp (taylorHomFin m D)

theorem coeff_residueTaylorFin {K : Type*} [CommRing K] [Algebra ℚ K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K)
    (α : Fin m →₀ ℕ) (a : R) :
    MvPowerSeries.coeff α (residueTaylorFin m D ρ a) =
      (∏ i, (1 / ((α i).factorial : ℚ))) • ρ (mixedIter m D α a) := by
  simp [residueTaylorFin, coeff_taylorHomFin, map_rat_smul]

@[simp] theorem coeff_zero_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (a : R) :
    MvPowerSeries.coeff 0 (residueTaylorFin m D ρ a) = ρ a := by
  simp [residueTaylorFin]

@[simp] theorem coeff_single_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (i : Fin m) (a : R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (residueTaylorFin m D ρ a) = ρ (D i a) := by
  simp [residueTaylorFin]

@[simp] theorem constantCoeff_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (a : R) :
    MvPowerSeries.constantCoeff (residueTaylorFin m D ρ a) = ρ a := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_residueTaylorFin m D ρ a

theorem constantCoeff_comp_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) :
    MvPowerSeries.constantCoeff.comp (residueTaylorFin m D ρ) = ρ := by
  ext a
  exact constantCoeff_residueTaylorFin m D ρ a

theorem iter_commute (D E : Derivation ℚ R R)
    (h : Commute D.toLinearMap E.toLinearMap) (i j : ℕ) (a : R) :
    iter D i (iter E j a) = iter E j (iter D i a) := by
  exact LinearMap.congr_fun ((h.pow_left i).pow_right j).eq a

theorem mixedIter_commute (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (E : Derivation ℚ R R) (α : Fin m →₀ ℕ)
    (h : ∀ i, Commute (D i).toLinearMap E.toLinearMap) (a : R) :
    mixedIter m D α (E a) = E (mixedIter m D α a) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    simp only [mixedIter, LinearMap.comp_apply]
    rw [show iter (D 0) (α 0) (E a) = E (iter (D 0) (α 0) a) from
      iter_commute (D 0) E (h 0) (α 0) 1 a]
    exact ih (fun i => D i.succ) α.tail (fun i => h i.succ) _

end PiExponent.CommutingTaylor

end

end OAI
