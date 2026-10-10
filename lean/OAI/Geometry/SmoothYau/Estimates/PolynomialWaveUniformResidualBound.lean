import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SmoothFiniteWaveSum

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
namespace YauCounterexamples
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}

theorem polynomial_wave_uniform_residual_bound
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → MvPolynomial σ ℂ) (V : X → ℕ → MvPolynomial σ ℂ)
    (m D J : ℕ) (hJ : D+m+1 ≤ J) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    (P : Set X)
    (hS : UniformJetBounds (fun p => realPolyEval (S p)) P (Metric.ball 0 r))
    (hF : ∀ j, UniformJetBounds (fun p x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x)
      P (Metric.ball 0 r))
    (hR : ∀ j, UniformJetBounds (fun p => polynomialWaveRemainder (g p) (b p) (S p) (V p) j)
      P (Metric.ball 0 r))
    (hL : UniformJetBounds (fun p => smoothPolynomialLaplacian (g p) (b p) (V p J)) P (Metric.ball 0 r))
    (hFzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (fun x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x) (2*D+3*m+6))
    (hRzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (polynomialWaveRemainder (g p) (b p) (S p) (V p) j) (2*D+3*m+6)) :
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p) (polynomialFiniteWave (S p) (V p) J n) y +
         (n : ℂ)*((n : ℂ)+2)*polynomialFiniteWave (S p) (V p) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
  obtain ⟨CS,hCS,hSb⟩ := hS.common m
  obtain ⟨CF,hCF,hFb⟩ := UniformJetBounds.finite_common _ hF J (2*D+3*m+6)
  obtain ⟨CR,hCR,hRb⟩ := UniformJetBounds.finite_common _ hR J (2*D+3*m+6)
  obtain ⟨CL,hCL,hLb⟩ := hL.common m
  let A := max CF (max CR CL)
  have hFA : CF ≤ A := le_max_left _ _
  have hRA : CR ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hLA : CL ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA : 0 ≤ A := zero_le_one.trans (hCF.trans hFA)
  let Ck := fun k => 2*(J+1 : ℕ) *
      (expJetConstant k CS*A*((2*(k+(D+3))).factorial : ℝ)*Real.exp c⁻¹) +
        expJetConstant k CS*A*Real.exp c⁻¹
  have hCk (k : ℕ) : 0 ≤ Ck k := by
    dsimp [Ck]
    have he := expJetConstant_nonneg k (zero_le_one.trans hCS)
    positivity
  let C := 1+∑ k ∈ Finset.range (m+1), Ck k
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun k _ => hCk k))
  refine ⟨C,hC,?_⟩
  intro p hp n hn x hx φ hphase k hk
  have hCkC : Ck k ≤ C := (Finset.single_le_sum (fun i _ => hCk i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans (le_add_of_nonneg_left zero_le_one)
  have horder : 2*D+3*k+6 ≤ 2*D+3*m+6 := by omega
  have hbound := finite_scheduled_residual_bound (realPolyEval (S p))
    (fun j x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x)
    (polynomialWaveRemainder (g p) (b p) (S p) (V p))
    (smoothPolynomialLaplacian (g p) (b p) (V p J))
    (contDiff_realPolyEval _) (fun j => (contDiff_smoothEikonalResidual _ (hg p) _).mul (contDiff_realPolyEval _))
    (contDiff_polynomialWaveRemainder _ _ (hg p) (hb p) _ _)
    (contDiff_smoothPolynomialLaplacian _ _ (hg p) (hb p) _)
    k D J (by omega) x CS A n φ c r hCS hA hn hc hr hx
    (fun i hi hik => hSb p hp x hx i (hik.trans hk))
    (fun j hj => (hFzero p hp j hj).mono horder)
    (fun j hj => (hRzero p hp j hj).mono horder)
    (fun j hj y hy => (hFb j hj p hp y hy _ horder).trans hFA)
    (fun j hj y hy => (hRb j hj p hp y hy _ horder).trans hRA)
    (fun i hi => (hLb p hp x hx i (hi.trans hk)).trans hLA) hphase
  rw [polynomial_wave_residual_expansion _ _ _ _ _ n (ne_of_gt (zero_lt_one.trans_le hn))]
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCkC (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hn) _)))
    (Real.exp_pos _).le

theorem generated_finite_wave_residual_estimate [TopologicalSpace X]
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (hz₀ : ∀ p, z p ≠ 0) (Q : X → σ → σ → ℂ)
    (hQ : ∀ i j, Continuous (fun p => Q p i j)) (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (m D : ℕ) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    {P : Set X} (hP : IsCompact P) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
    let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p) (polynomialFiniteWave (S p) (V p) J n) y +
         (n : ℂ)*((n : ℂ)+2)*polynomialFiniteWave (S p) (V p) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
  dsimp only
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  have hu := generated_wave_uniform_jets g b hg hb hg0 hdg0 hgc hbc s hs z hz hz₀ Q hQ
    hsym hnull hQz K J (by dsimp [K]; omega) hP (isCompact_closedBall (0 : σ → ℝ) r)
  apply polynomial_wave_uniform_residual_bound g b hg hb S V m D J le_rfl r c hr hc P
    (hu.1.mono subset_rfl Metric.ball_subset_closedBall)
    (fun j => (hu.2.1 j).mono subset_rfl Metric.ball_subset_closedBall)
    (fun j => (hu.2.2.1 j).mono subset_rfl Metric.ball_subset_closedBall)
    ((hu.2.2.2.1 J).mono subset_rfl Metric.ball_subset_closedBall)
  · intro p hp j hj
    exact (generated_wave_remainders_vanish (g p) (b p) (hg p) (hb p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hsym p) (hnull p) (hQz p) K J (by dsimp [K]; omega)).1 j
  · intro p hp j hj
    exact (generated_wave_remainders_vanish (g p) (b p) (hg p) (hb p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hsym p) (hnull p) (hQz p) K J (by dsimp [K]; omega)).2 j hj
end YauCounterexamples

end

end OAI
