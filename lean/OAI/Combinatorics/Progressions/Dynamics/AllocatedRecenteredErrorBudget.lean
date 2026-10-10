import OAI.Combinatorics.Progressions.Estimates.AllocatedProxyAccuracy

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem allocatedRecenteredErrorFactor_le {m dim : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim)) (hdim : dim ≤ m + 1)
    (hinj : ∀ j, Function.Injective (rows j))
    (C : Fin m → ℝ≥0)
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p)
    {M period : ℕ} (hMP : (M : ℝ) ≤ Real.exp p)
    (hperiod : period ≤ M ^ (m + 1))
    (Mprofile : ℝ) (hMprofile : Mprofile ≤ Real.exp (-(E + 3))) :
    let a := allocatedCoefficientAccuracy m p (E + 3)
    let H := coefficientDeckPeriodCap O Q period *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    (a * H + 2 * a + a) + (Mprofile + 2 * a + a) ≤ Real.exp (-E) := by
  intro a H
  have hE3 : 0 ≤ E + 3 := by linarith
  have hc := allocatedCoefficientAccuracy_proxy_error B U b hb bW rows hdim hinj C hp hE3
    hvars hI hn hJ hC hMP hperiod
  change a * H + 2 * a + a ≤ Real.exp (-(E + 3)) at hc
  have ha : 0 ≤ a := (allocatedCoefficientAccuracy_bounds m hp hE3).1.le
  have hH : 0 ≤ H := mul_nonneg (coefficientDeckPeriodCap_nonneg O Q period) (by positivity)
  have haH := mul_nonneg ha hH
  have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (-(E + 3)) := by linarith
    _ ≤ Real.exp 3 * Real.exp (-(E + 3)) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
