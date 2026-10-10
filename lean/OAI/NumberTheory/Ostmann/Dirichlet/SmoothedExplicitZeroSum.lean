import Mathlib.Tactic.GCongr
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitIntegrand

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Dirichlet

theorem smoothed_zero_sum_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (S : Finset ℂ)
    {T X C M : ℝ} (A : ℕ) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hS : ∀ p ∈ S, p ∈ zerosUpTo χ T)
    (hM : (∑ p ∈ S, (zeroMultiplicity χ p : ℝ)) ≤ M)
    (W : ℂ → ℝ)
    (hW : ∀ p ∈ S, W p ≤ C/(1+|p.im|)^A)
    (hW0 : ∀ p ∈ S, W p ≤ C) :
    (∑ p ∈ S, (zeroMultiplicity χ p : ℝ)*X^p.re*W p) ≤
      C*((∑ p ∈ (zerosUpTo_finite χ hχ T).toFinset.filter (fun p => (1 : ℝ)/2 ≤ p.re),
        (zeroMultiplicity χ p : ℝ)*X^p.re/(1+|p.im|)^A)+Real.sqrt X*M) := by
  classical
  let F : ℂ → ℝ := fun p => (zeroMultiplicity χ p : ℝ)*X^p.re/(1+|p.im|)^A
  have hFp (p : ℂ) : 0 ≤ F p := by dsimp [F]; positivity
  have hpoint (p : ℂ) (hp : p ∈ S) :
      (zeroMultiplicity χ p : ℝ)*X^p.re*W p ≤
        C*(if (1 : ℝ)/2 ≤ p.re then F p else 0)+
          C*Real.sqrt X*(zeroMultiplicity χ p : ℝ) := by
    by_cases hhalf : (1 : ℝ)/2 ≤ p.re
    · rw [ite_eq_left hhalf]
      have hw := mul_le_mul_of_nonneg_left (hW p hp)
        (show 0 ≤ (zeroMultiplicity χ p : ℝ)*X^p.re by positivity)
      have hn : 0 ≤ C*Real.sqrt X*(zeroMultiplicity χ p : ℝ) := by positivity
      have hw' : (zeroMultiplicity χ p : ℝ)*X^p.re*W p ≤ C*F p := by
        calc
          _ ≤ (zeroMultiplicity χ p : ℝ)*X^p.re*(C/(1+|p.im|)^A) := hw
          _ = _ := by dsimp [F]; ring
      linarith only [hw',hn]
    · rw [ite_eq_right hhalf,mul_zero,zero_add]
      have hpow : X^p.re ≤ Real.sqrt X := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hX (le_of_not_ge hhalf)
      calc
        _ ≤ (zeroMultiplicity χ p : ℝ)*X^p.re*C :=
          mul_le_mul_of_nonneg_left (hW0 p hp) (by positivity)
        _ ≤ (zeroMultiplicity χ p : ℝ)*Real.sqrt X*C := by gcongr
        _ = _ := by ring
  have hsub : S.filter (fun p => (1 : ℝ)/2 ≤ p.re) ⊆
      (zerosUpTo_finite χ hχ T).toFinset.filter (fun p => (1 : ℝ)/2 ≤ p.re) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(zerosUpTo_finite χ hχ T).mem_toFinset.mpr (hS p hp'.1),hp'.2⟩
  have hsum := Finset.sum_le_sum hpoint
  have hfilter : (∑ p ∈ S, if (1 : ℝ)/2 ≤ p.re then F p else 0) ≤
      ∑ p ∈ (zerosUpTo_finite χ hχ T).toFinset.filter (fun p => (1 : ℝ)/2 ≤ p.re), F p := by
    rw [← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hFp p)
  calc
    _ ≤ C*(∑ p ∈ S, if (1 : ℝ)/2 ≤ p.re then F p else 0)+
        C*Real.sqrt X*(∑ p ∈ S, (zeroMultiplicity χ p : ℝ)) := by
      simpa only [Finset.sum_add_distrib,Finset.mul_sum] using hsum
    _ ≤ C*(∑ p ∈ (zerosUpTo_finite χ hχ T).toFinset.filter (fun p => (1 : ℝ)/2 ≤ p.re), F p)+
        C*Real.sqrt X*M := by gcongr
    _ = _ := by dsimp [F]; ring

theorem mellin_smoothed_zero_sum_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (S : Finset ℂ)
    (ρ : 𝓢(ℝ,ℂ)) {T X C M : ℝ} (A : ℕ) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hS : ∀ p ∈ S, p ∈ zerosUpTo χ T)
    (hM : (∑ p ∈ S, (zeroMultiplicity χ p : ℝ)) ≤ M)
    (hW : ∀ p ∈ S, ‖mellin (ρ : ℝ → ℂ) p‖ ≤ C/(1+|p.im|)^A)
    (hW0 : ∀ p ∈ S, ‖mellin (ρ : ℝ → ℂ) p‖ ≤ C) :
    (∑ p ∈ S, (zeroMultiplicity χ p : ℝ)*X^p.re*‖mellin (ρ : ℝ → ℂ) p‖) ≤
      C*((∑ p ∈ (zerosUpTo_finite χ hχ T).toFinset.filter (fun p => (1 : ℝ)/2 ≤ p.re),
        (zeroMultiplicity χ p : ℝ)*X^p.re/(1+|p.im|)^A)+Real.sqrt X*M) :=
  smoothed_zero_sum_le χ hχ S A hX hC hS hM _ hW hW0

end Ostmann.Dirichlet

end

end OAI
