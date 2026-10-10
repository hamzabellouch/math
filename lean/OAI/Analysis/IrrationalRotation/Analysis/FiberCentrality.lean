import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace OAI

namespace Invariant233.FiberCentrality

open scoped ENNReal

local notation "K" => lp (fun _ : ℤ => ℂ) 2

theorem map_single_eq_smul_of_commute_diagonal
    (A D : K →L[ℂ] K) (d : ℤ → ℂ)
    (hd : Function.Injective d)
    (hD : ∀ (v : K) (k : ℤ), D v k = d k * v k)
    (hAD : A * D = D * A) (j : ℤ) :
    A (lp.single 2 j (1 : ℂ)) =
      (A (lp.single 2 j (1 : ℂ)) j) • lp.single 2 j (1 : ℂ) := by
  have hDe : D (lp.single 2 j (1 : ℂ)) =
      d j • lp.single 2 j (1 : ℂ) := by
    ext k
    by_cases h : j = k
    · subst k
      simp [hD]
    · simp [hD, lp.single_apply, h]
  ext k
  by_cases h : j = k
  · subst k
    simp
  · have heq := congrArg
        (fun L : K →L[ℂ] K => L (lp.single 2 j (1 : ℂ)) k) hAD
    have heq' : d j * A (lp.single 2 j (1 : ℂ)) k =
        d k * A (lp.single 2 j (1 : ℂ)) k := by
      simpa only [mul_apply_eq_comp, hDe, map_smul,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hD] using heq
    have hz : A (lp.single 2 j (1 : ℂ)) k = 0 := by
      have hp : (d j - d k) * A (lp.single 2 j (1 : ℂ)) k = 0 := by
        rw [sub_mul, heq', sub_self]
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (fun e => h (hd e)))
    simp [lp.single_apply, h, hz]

theorem scalar_of_commute_diagonal_and_shift
    (A D S : K →L[ℂ] K) (d : ℤ → ℂ)
    (hd : Function.Injective d)
    (hD : ∀ (v : K) (k : ℤ), D v k = d k * v k)
    (hS : ∀ j : ℤ, S (lp.single 2 j (1 : ℂ)) = lp.single 2 (j + 1) (1 : ℂ))
    (hAD : A * D = D * A) (hAS : A * S = S * A) :
    ∃ c : ℂ, A = c • (1 : K →L[ℂ] K) := by
  let a : ℤ → ℂ := fun j => A (lp.single 2 j (1 : ℂ)) j
  have hAe (j : ℤ) : A (lp.single 2 j (1 : ℂ)) =
      a j • lp.single 2 j (1 : ℂ) :=
    map_single_eq_smul_of_commute_diagonal A D d hd hD hAD j
  have hsucc (j : ℤ) : a (j + 1) = a j := by
    have heq : A (S (lp.single 2 j (1 : ℂ))) =
        S (A (lp.single 2 j (1 : ℂ))) :=
      congrArg (fun L : K →L[ℂ] K => L (lp.single 2 j (1 : ℂ))) hAS
    rw [hS, hAe, hAe, map_smul, hS] at heq
    have hcoord := congrArg (fun v : K => v (j + 1)) heq
    simpa using hcoord
  have ha (j : ℤ) : a j = a 0 := by
    induction j using Int.induction_on with
    | zero => rfl
    | succ n ih => exact (hsucc n).trans ih
    | pred n ih =>
      have h := hsucc (-(n : ℤ) - 1)
      simp only [sub_add_cancel] at h
      exact h.symm.trans ih
  refine ⟨a 0, ?_⟩
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply ContinuousLinearMap.ext_ring
  change A (lp.single 2 j (1 : ℂ)) = a 0 • lp.single 2 j (1 : ℂ)
  rw [hAe, ha]

theorem injective_integer_rotation_orbit (θ : ℝ) (hθ : Irrational θ)
    (x : AddCircle (1 : ℝ)) :
    Function.Injective (fun k : ℤ => x + k • (θ : AddCircle (1 : ℝ))) := by
  intro j k heq
  have hzero : (j - k) • (θ : AddCircle (1 : ℝ)) = 0 := by
    rw [sub_zsmul, ← sub_eq_add_neg, sub_eq_zero]
    exact add_left_cancel heq
  have hreal : (((j - k : ℤ) : ℝ) * θ : AddCircle (1 : ℝ)) = 0 := by
    simpa only [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul] using hzero
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hreal
  by_contra hjk
  apply (hθ.intCast_mul (sub_ne_zero.mpr hjk)).ne_int n
  simpa only [zsmul_eq_mul, mul_one] using hn.symm

theorem injective_irrational_diagonal (θ : ℝ) (hθ : Irrational θ)
    (x : AddCircle (1 : ℝ)) :
    Function.Injective (fun k : ℤ =>
      (AddCircle.toCircle (x + k • (θ : AddCircle (1 : ℝ))) : ℂ)) := by
  intro j k h
  apply injective_integer_rotation_orbit θ hθ x
  exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h)

theorem scalar_of_commute_irrational_diagonal_and_shift
    (A D S : K →L[ℂ] K) (θ : ℝ) (hθ : Irrational θ)
    (x : AddCircle (1 : ℝ))
    (hD : ∀ (v : K) (k : ℤ), D v k =
      (AddCircle.toCircle (x + k • (θ : AddCircle (1 : ℝ))) : ℂ) * v k)
    (hS : ∀ j : ℤ, S (lp.single 2 j (1 : ℂ)) = lp.single 2 (j + 1) (1 : ℂ))
    (hAD : A * D = D * A) (hAS : A * S = S * A) :
    ∃ c : ℂ, A = c • (1 : K →L[ℂ] K) :=
  scalar_of_commute_diagonal_and_shift A D S _
    (injective_irrational_diagonal θ hθ x) hD hS hAD hAS

end Invariant233.FiberCentrality

end OAI
