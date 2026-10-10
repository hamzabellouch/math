import OAI.Algebra.AuslanderReiten.Homology.ExceptionalHomology
import OAI.Algebra.AuslanderReiten.Duality.DualTensorComplex

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q

def idealDualObject : ℕ → ModuleCat C
  | 0 => ModuleCat.of C (RightDual k C (rightF q))
  | _ + 1 => ModuleCat.of C (RightDual k C (rightE q))

def idealDualDifferential : (n : ℕ) → idealDualObject q (n + 1) ⟶ idealDualObject q n
  | 0 => ModuleCat.ofHom (RightDual.map (k := k) (leftU q))
  | m + 1 => ModuleCat.ofHom (RightDual.map (k := k) (leftEll q (q ^ m)))

theorem idealDualDifferential_comp (n : ℕ) :
    idealDualDifferential q (n + 1) ≫ idealDualDifferential q n = 0 := by
  apply ModuleCat.hom_ext
  cases n with
  | zero =>
    apply LinearMap.ext
    intro φ
    apply RightDual.ext
    apply LinearMap.ext
    intro a
    change φ.functional (leftEll q (q ^ 0) (leftU q a)) = 0
    have hz : leftEll q (q ^ 0) (leftU q a) = 0 := by
      apply Subtype.ext
      change ell q (q ^ 0) * (basisVector q u * (a : C)) = 0
      rw [pow_zero, ← mul_assoc, ell_one_mul_u, zero_mul]
    rw [hz, map_zero]
  | succ n =>
    apply LinearMap.ext
    intro φ
    apply RightDual.ext
    apply LinearMap.ext
    intro a
    change φ.functional (leftEll q (q ^ (n + 1)) (leftEll q (q ^ n) a)) = 0
    have hz : leftEll q (q ^ (n + 1)) (leftEll q (q ^ n) a) = 0 := by
      apply Subtype.ext
      change ell q (q ^ (n + 1)) * (ell q (q ^ n) * (a : C)) = 0
      rw [pow_succ', ← mul_assoc, ell_successor_mul, zero_mul]
    rw [hz, map_zero]

def idealDualComplex : ChainComplex (ModuleCat C) ℕ :=
  ChainComplex.of (idealDualObject q) (idealDualDifferential q) (idealDualDifferential_comp q)

theorem idealDualComplex_d (n : ℕ) :
    (idealDualComplex q).d (n + 1) n = idealDualDifferential q n :=
  ChainComplex.of_d _ _ _

theorem idealDual_exact_one : Function.Exact (idealDualDifferential q 1) (idealDualDifferential q 0) := by
  change Function.Exact (RightDual.map (k := k) (leftEll q (q ^ 0))) (RightDual.map (k := k) (leftU q))
  rw [pow_zero]
  exact RightDual.map_exact (k := k) (leftU q) (leftEll q 1) (leftU_exact q)

theorem idealDual_exact_tail (hq : q ≠ 0) (h : NoPositivePowerOne q) (n : ℕ) :
    Function.Exact (idealDualDifferential q (n + 3)) (idealDualDifferential q (n + 2)) := by
  change Function.Exact (RightDual.map (k := k) (leftEll q (q ^ (n + 2))))
    (RightDual.map (k := k) (leftEll q (q ^ (n + 1))))
  have hh := RightDual.map_exact (k := k) (leftEll q (q ^ (n + 1)))
    (leftEll q (q * q ^ (n + 1)))
    (leftEll_exact q (q ^ (n + 1)) hq (h _ (by omega))
      (by simpa only [← pow_succ'] using h (n + 2) (by omega)))
  simpa only [← pow_succ'] using hh

omit [CharP k 2] in
theorem idealDual_exact_zero : Function.Surjective (idealDualDifferential q 0) :=
  RightDual.map_surjective (k := k) (leftU q) (leftU_injective q)

theorem idealDual_exactAt (hq : q ≠ 0) (h : NoPositivePowerOne q) (n : ℕ) (hn : n ≠ 2) :
    (idealDualComplex q).ExactAt n := by
  match n with
  | 0 =>
    rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    intro z
    constructor
    · intro _
      exact idealDual_exact_zero q z
    · intro _
      change (idealDualComplex q).d 0 0 z = 0
      rw [(idealDualComplex q).shape 0 0 (by simp)]
      rfl
  | 1 =>
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact ((idealDualComplex q).d 2 1) ((idealDualComplex q).d 1 0)
    simpa [idealDualComplex, ChainComplex.of_d] using! idealDual_exact_one q
  | 2 => exact (hn rfl).elim
  | n + 3 =>
    rw [HomologicalComplex.exactAt_iff' _ (n + 4) (n + 3) (n + 2) (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact ((idealDualComplex q).d (n + 4) (n + 3)) ((idealDualComplex q).d (n + 3) (n + 2))
    rw [show n + 4 = (n + 3) + 1 by omega, idealDualComplex_d]
    rw [show n + 3 = (n + 2) + 1 by omega, idealDualComplex_d]
    exact idealDual_exact_tail q hq h n

end ArExplicit.Resolution

end

end OAI
