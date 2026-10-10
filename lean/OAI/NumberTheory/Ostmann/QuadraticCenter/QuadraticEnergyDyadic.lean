import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyArray

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem sum_Ico_dyadic {A : Type*} [AddCommMonoid A] (a N : ℕ) (F : ℕ → A) :
    (∑ s ∈ Finset.Ico a (2^N*a), F s) =
      ∑ j ∈ Finset.range N, ∑ s ∈ Finset.Ico (2^j*a) (2*(2^j*a)), F s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hpow : 1 ≤ 2^N := Nat.one_le_pow N 2 (by omega)
    have hlow : a ≤ 2^N*a := by simpa only [one_mul] using Nat.mul_le_mul_right a hpow
    have hhigh : 2^N*a ≤ 2*(2^N*a) := by omega
    rw [show 2^(N+1)*a = 2*(2^N*a) by ring]
    exact (Finset.sum_Ico_consecutive F hlow hhigh).symm

theorem positiveDivisorArray_large_energy_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (L B N q : ℕ), Squarefree L → 2 ≤ L →
      B < 2^N*L^4 → (2^N*L^4 : ℕ) ≤ Real.exp (T^2) →
      ∀ (u K : ℝ), 1 < u → u ≤ T^((1 : ℝ)/100000) → T^((3 : ℝ)/4) ≤ K →
      ∀ (lam : ℝ), 0 ≤ lam →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Icc (L^4) B).filter (fun s => Squarefree s ∧ s.Coprime L),
        u^s.primeFactors.card * ‖positiveDivisorArray L q lam A mInv 1 R h θ s‖^2) ≤
      (N : ℝ) * (reciprocalSqrtDivisorSum L)^2 *
        (Real.exp (K/200) * (quadraticCorrelationConstant *
          ∏ p ∈ L.primeFactors, (1+lam^2+2*lam/Real.sqrt (p : ℝ))) +
        cutoffFourierBound^2 * Real.exp (-10*K) * (1+lam)^(2*L.primeFactors.card)) := by
  filter_upwards [positiveDivisorArray_dyadic_energy_eventually] with T hT
  intro L B N q hL hL2 hBN hNup u K hu huup hK lam hlam A mInv R h θ hR
  let E := (reciprocalSqrtDivisorSum L)^2 *
    (Real.exp (K/200) * (quadraticCorrelationConstant *
      ∏ p ∈ L.primeFactors, (1+lam^2+2*lam/Real.sqrt (p : ℝ))) +
      cutoffFourierBound^2 * Real.exp (-10*K) * (1+lam)^(2*L.primeFactors.card))
  let F : ℕ → ℝ := fun s => if Squarefree s ∧ s.Coprime L then
    u^s.primeFactors.card * ‖positiveDivisorArray L q lam A mInv 1 R h θ s‖^2 else 0
  have hF : ∀ s, 0 ≤ F s := by
    intro s
    dsimp [F]
    split_ifs <;> positivity
  have hsub : Finset.Icc (L^4) B ⊆ Finset.Ico (L^4) (2^N*L^4) := by
    intro s hs
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hs).1,
      ((Finset.mem_Icc.mp hs).2).trans_lt hBN⟩
  calc
    _ = ∑ s ∈ Finset.Icc (L^4) B, F s := by simp only [Finset.sum_filter, F]
    _ ≤ ∑ s ∈ Finset.Ico (L^4) (2^N*L^4), F s :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => hF s)
    _ = ∑ j ∈ Finset.range N, ∑ s ∈ Finset.Ico (2^j*L^4) (2*(2^j*L^4)), F s :=
      sum_Ico_dyadic (L^4) N F
    _ ≤ ∑ _j ∈ Finset.range N, E := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j ≤ N := (Finset.mem_range.mp hj).le
      have hpow : 1 ≤ 2^j := Nat.one_le_pow j 2 (by omega)
      have hscale : L^4 ≤ 2^j*L^4 := by
        simpa only [one_mul] using Nat.mul_le_mul_right (L^4) hpow
      have hscaleup : ((2^j*L^4 : ℕ) : ℝ) ≤ Real.exp (T^2) := by
        apply le_trans _ hNup
        exact_mod_cast Nat.mul_le_mul_right (L^4) (Nat.pow_le_pow_right (by omega) hjN)
      simpa only [Finset.sum_filter, F, E] using
        (hT L (2^j*L^4) q hL hL2 hscale u K hscaleup hu huup hK lam hlam A mInv R h θ hR)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp [E]; ring

end Ostmann.QuadraticCenter

end

end OAI
