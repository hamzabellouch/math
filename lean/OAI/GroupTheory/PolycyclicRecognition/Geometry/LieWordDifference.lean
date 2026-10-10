import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieWordDifferential

namespace OAI

/-! # Finite differences of Lie words along the lower central series

The nonlinear part of a bracket polynomial raises the filtration also for
finite differences, not just infinitesimal ones. This supports the explicit
inverse of a BCH translation.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

omit [LieAlgebra ℝ L] in
theorem lie_sub_lie_decomposition (x y z w : L) :
    ⁅x, y⁆ - ⁅z, w⁆ = ⁅x - z, y⁆ + ⁅z, y - w⁆ := by
  rw [sub_lie, lie_sub]
  abel

theorem evalBracketWord_sub_mem (X Y : I → L) (J : LieIdeal ℝ L)
    (hXY : ∀ i, X i - Y i ∈ J) (w : FreeMagma I) :
    evalBracketWord X w - evalBracketWord Y w ∈ J := by
  induction w using FreeMagma.rec with
  | of i => exact hXY i
  | mul u v hu hv =>
    rw [evalBracketWord, evalBracketWord, lie_sub_lie_decomposition]
    exact J.add_mem (lie_mem_left ℝ L J _ _ hu) (lie_mem_right ℝ L J _ _ hv)

theorem evalBracketWord_mul_sub_mem_succ (X Y : I → L) (k : ℕ)
    (hXY : ∀ i, X i - Y i ∈ lowerCentralSeries ℝ L L k) (u v : FreeMagma I) :
    evalBracketWord X (.mul u v) - evalBracketWord Y (.mul u v) ∈
      lowerCentralSeries ℝ L L (k + 1) := by
  have hu := evalBracketWord_sub_mem X Y (lowerCentralSeries ℝ L L k) hXY u
  have hv := evalBracketWord_sub_mem X Y (lowerCentralSeries ℝ L L k) hXY v
  change ⁅evalBracketWord X u, evalBracketWord X v⁆ -
    ⁅evalBracketWord Y u, evalBracketWord Y v⁆ ∈ lowerCentralSeries ℝ L L (k + 1)
  rw [lie_sub_lie_decomposition]
  apply (lowerCentralSeries ℝ L L (k + 1)).add_mem
  · have hh : ⁅evalBracketWord X v, evalBracketWord X u - evalBracketWord Y u⁆ ∈
        lowerCentralSeries ℝ L L (k + 1) := by
      rw [lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hu
    rw [← lie_skew]
    exact (lowerCentralSeries ℝ L L (k + 1)).neg_mem hh
  · rw [lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hv

/-- The degree-one part of a word as a linear map in its input letters. -/
def wordLinearPart : FreeMagma I → (I → L) →ₗ[ℝ] L
  | .of i => LinearMap.proj i
  | .mul _ _ => 0

def finiteDynkinLinearPart {c n : ℕ} (coeff : DynkinCoefficients c n) :
    (Fin n → L) →ₗ[ℝ] L :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    coeff d w • wordLinearPart (rightNestedWord d.val w)

theorem evalBracketWord_sub_linear_mem_succ (X Y : I → L) (k : ℕ)
    (hXY : ∀ i, X i - Y i ∈ lowerCentralSeries ℝ L L k) (w : FreeMagma I) :
    (evalBracketWord X w - evalBracketWord Y w) - wordLinearPart w (X - Y) ∈
      lowerCentralSeries ℝ L L (k + 1) := by
  cases w with
  | of i =>
    simpa only [evalBracketWord, wordLinearPart, LinearMap.proj_apply, Pi.sub_apply, sub_self]
      using (lowerCentralSeries ℝ L L (k + 1)).zero_mem
  | mul u v =>
    simpa only [wordLinearPart, LinearMap.zero_apply, sub_zero]
      using evalBracketWord_mul_sub_mem_succ X Y k hXY u v

theorem finiteDynkinPolynomial_sub_linear_mem_succ {c n : ℕ}
    (coeff : DynkinCoefficients c n) (X Y : Fin n → L) (k : ℕ)
    (hXY : ∀ i, X i - Y i ∈ lowerCentralSeries ℝ L L k) :
    (finiteDynkinPolynomial coeff X - finiteDynkinPolynomial coeff Y) -
        finiteDynkinLinearPart coeff (X - Y) ∈ lowerCentralSeries ℝ L L (k + 1) := by
  simp only [finiteDynkinPolynomial, finiteDynkinLinearPart, LinearMap.sum_apply,
    LinearMap.smul_apply, ← Finset.sum_sub_distrib, ← smul_sub]
  apply (lowerCentralSeries ℝ L L (k + 1)).sum_mem
  intro d _
  apply (lowerCentralSeries ℝ L L (k + 1)).sum_mem
  intro w _
  exact (lowerCentralSeries ℝ L L (k + 1)).smul_mem (coeff d w)
    (evalBracketWord_sub_linear_mem_succ X Y k hXY _)

end PolycyclicRecognition

end

end OAI
