import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Ideal

namespace OAI

/-! # Differentials of bracket words and the lower central series

Changing the basepoint in the differential of a Lie polynomial changes its
linear part only by a map that raises the lower central series. This is the
algebraic part of the Jacobian computation for nilpotent exponential coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped BigOperators

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

def rightBracketLinear (y : L) : L →ₗ[ℝ] L where
  toFun x := ⁅x, y⁆
  map_add' x z := add_lie x z y
  map_smul' c x := smul_lie c x y

def bracketWordDifferential (X : I → L) (dX : I → L →ₗ[ℝ] L) :
    FreeMagma I → L →ₗ[ℝ] L
  | .of i => dX i
  | .mul u v => (rightBracketLinear (evalBracketWord X v)).comp (bracketWordDifferential X dX u) +
      (LieAlgebra.ad ℝ L (evalBracketWord X u)).comp (bracketWordDifferential X dX v)

@[simp] theorem bracketWordDifferential_of (X : I → L) (dX : I → L →ₗ[ℝ] L)
    (i : I) (z : L) : bracketWordDifferential X dX (.of i) z = dX i z := rfl

@[simp] theorem bracketWordDifferential_mul (X : I → L) (dX : I → L →ₗ[ℝ] L)
    (u v : FreeMagma I) (z : L) :
    bracketWordDifferential X dX (u * v) z =
      ⁅bracketWordDifferential X dX u z, evalBracketWord X v⁆ +
        ⁅evalBracketWord X u, bracketWordDifferential X dX v z⁆ := rfl

theorem bracketWordDifferential_mem (X : I → L) (dX : I → L →ₗ[ℝ] L)
    (J : LieIdeal ℝ L) (z : L) (hz : ∀ i, dX i z ∈ J) (w : FreeMagma I) :
    bracketWordDifferential X dX w z ∈ J := by
  induction w using FreeMagma.rec with
  | of i => exact hz i
  | mul u v hu hv =>
    exact J.add_mem (lie_mem_left ℝ L J _ _ hu) (lie_mem_right ℝ L J _ _ hv)

theorem bracketWordDifferential_mul_mem_succ
    (X : I → L) (dX : I → L →ₗ[ℝ] L) (k : ℕ) (z : L)
    (hz : ∀ i, dX i z ∈ lowerCentralSeries ℝ L L k) (u v : FreeMagma I) :
    bracketWordDifferential X dX (u * v) z ∈ lowerCentralSeries ℝ L L (k + 1) := by
  have hu := bracketWordDifferential_mem X dX (lowerCentralSeries ℝ L L k) z hz u
  have hv := bracketWordDifferential_mem X dX (lowerCentralSeries ℝ L L k) z hz v
  have hright : ⁅evalBracketWord X u, bracketWordDifferential X dX v z⁆ ∈
      lowerCentralSeries ℝ L L (k + 1) := by
    rw [lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hv
  have hleft : ⁅evalBracketWord X v, bracketWordDifferential X dX u z⁆ ∈
      lowerCentralSeries ℝ L L (k + 1) := by
    rw [lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hu
  rw [bracketWordDifferential_mul]
  apply (lowerCentralSeries ℝ L L (k + 1)).add_mem _ hright
  rw [← lie_skew]
  exact (lowerCentralSeries ℝ L L (k + 1)).neg_mem hleft

theorem bracketWordDifferential_sub_mem_succ
    (X Y : I → L) (dX : I → L →ₗ[ℝ] L) (k : ℕ) (z : L)
    (hz : ∀ i, dX i z ∈ lowerCentralSeries ℝ L L k) (w : FreeMagma I) :
    bracketWordDifferential X dX w z - bracketWordDifferential Y dX w z ∈
      lowerCentralSeries ℝ L L (k + 1) := by
  cases w with
  | of i => simpa only [bracketWordDifferential_of, sub_self] using
      (lowerCentralSeries ℝ L L (k + 1)).zero_mem
  | mul u v =>
    exact (lowerCentralSeries ℝ L L (k + 1)).sub_mem
      (bracketWordDifferential_mul_mem_succ X dX k z hz u v)
      (bracketWordDifferential_mul_mem_succ Y dX k z hz u v)

def finiteDynkinDifferential {c n : ℕ} (coeff : DynkinCoefficients c n)
    (X : Fin n → L) (dX : Fin n → L →ₗ[ℝ] L) : L →ₗ[ℝ] L :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    coeff d w • bracketWordDifferential X dX (rightNestedWord d.val w)

theorem finiteDynkinDifferential_sub_mem_succ {c n : ℕ}
    (coeff : DynkinCoefficients c n) (X Y : Fin n → L) (dX : Fin n → L →ₗ[ℝ] L)
    (k : ℕ) (z : L) (hz : ∀ i, dX i z ∈ lowerCentralSeries ℝ L L k) :
    finiteDynkinDifferential coeff X dX z - finiteDynkinDifferential coeff Y dX z ∈
      lowerCentralSeries ℝ L L (k + 1) := by
  simp only [finiteDynkinDifferential, LinearMap.sum_apply, LinearMap.smul_apply,
    ← Finset.sum_sub_distrib, ← smul_sub]
  apply (lowerCentralSeries ℝ L L (k + 1)).sum_mem
  intro d _
  apply (lowerCentralSeries ℝ L L (k + 1)).sum_mem
  intro w _
  exact (lowerCentralSeries ℝ L L (k + 1)).smul_mem (coeff d w)
    (bracketWordDifferential_sub_mem_succ X Y dX k z hz _)

end PolycyclicRecognition

end

end OAI
