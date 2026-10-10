import OAI.NumberTheory.JointDickman.Counting.CoarseDiscreteShort
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! # Uniformly shifted discrete coarse-feature short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem residueBinAverage_sq_integrable {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖residueBinAverage E ζ μ w r H z‖^2) volume a b := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  exact complexShortAverage_sq_integrable_any f hH a b

theorem residueBinAverage_shifted_discrete_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) {H : ℕ} (hH : 0 < H) {X : ℝ} (hX : 0 < X)
    (j : ℕ) (hj : (j : ℝ) ≤ X) :
    (∑ u ∈ Ico ⌈X⌉₊ ⌊2*X⌋₊, ‖residueBinAverage E ζ μ w r H (u+j)‖^2) ≤
      ∫ z in X..4*X, ‖residueBinAverage E ζ μ w r H z‖^2 := by
  have hs := sum_Ico_add' (fun u : ℕ => ‖residueBinAverage E ζ μ w r H u‖^2)
    ⌈X⌉₊ ⌊2*X⌋₊ j
  simp only [Nat.cast_add] at hs
  rw [hs]
  apply residueBinAverage_discrete_energy_le E ζ μ w r hH
  · linarith
  · push_cast
    exact (Nat.le_ceil X).trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  · push_cast
    have hf := Nat.floor_le (show 0 ≤ 2*X by positivity)
    linarith

theorem all_residues_coarse_shifted_short
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {q : ℕ} [NeZero q] (A scale : ℕ → ℝ) (H M : ℕ → ℕ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ (j : ℕ), j ≤ M B → ∀ r : ZMod q,
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) r (H B) (u+j)‖^2) < ε := by
  have hs₁ := all_residues_coarse_short_with_center hMR hMRT hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b (q := q) A scale (fun B => (H B : ℝ)) hA hscale
    (tendsto_natCast_atTop_atTop.comp hH)
  have hs₂ := all_residues_coarse_short_with_center hMR hMRT hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b (q := q) (fun B => 2*A B) scale (fun B => (H B : ℝ))
    (fun B => mul_pos (by norm_num) (hA B)) hscale (tendsto_natCast_atTop_atTop.comp hH)
  intro ε hε
  filter_upwards [hs₁ (ε/4) (by positivity),hs₂ (ε/4) (by positivity),hH.eventually_gt_atTop 0]
    with B h₁ h₂ hHB
  filter_upwards [h₁,h₂,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop (M B)]
    with n h₁ h₂ hX
  intro j hj r
  have hX0 : 0 < A B*scale n := (Nat.cast_nonneg (M B)).trans_lt hX
  let E := fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)
  let w := primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)
  let f := fun z => ‖residueBinAverage E ζ μ w r (H B) z‖^2
  have hi₁ := residueBinAverage_sq_integrable E ζ μ w r (by exact_mod_cast hHB : (0 : ℝ) < H B)
    (A B*scale n) (2*(A B*scale n))
  have hi₂ := residueBinAverage_sq_integrable E ζ μ w r (by exact_mod_cast hHB : (0 : ℝ) < H B)
    (2*(A B*scale n)) (4*(A B*scale n))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have hh₂ : (1/(2*(A B*scale n)))*(∫ z in 2*(A B*scale n)..4*(A B*scale n), f z) < ε/4 := by
    have hb := h₂ r
    have heA : (2*A B)*scale n = 2*(A B*scale n) := by ring
    have heU : 2*((2*A B)*scale n) = 4*(A B*scale n) := by ring
    rw [heU,heA] at hb
    exact hb
  have hratio : (1/(A B*scale n))*(∫ z in (A B*scale n)..4*(A B*scale n), f z) =
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n), f z)+
        2*((1/(2*(A B*scale n)))*(∫ z in 2*(A B*scale n)..4*(A B*scale n), f z)) := by
    rw [← hadd]
    ring
  have hsmall : (1/(A B*scale n))*(∫ z in (A B*scale n)..4*(A B*scale n), f z) < ε := by
    rw [hratio]
    have hh₁ := h₁ r
    change (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n), f z) < ε/4 at hh₁
    linarith
  apply lt_of_le_of_lt _ hsmall
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact residueBinAverage_shifted_discrete_energy_le E ζ μ w r hHB hX0 j
    ((by exact_mod_cast hj : (j : ℝ) ≤ M B).trans hX.le)

end JointDickman

end OAI
