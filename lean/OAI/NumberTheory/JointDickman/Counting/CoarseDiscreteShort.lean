import OAI.NumberTheory.JointDickman.Counting.DiscreteShortEnergy

namespace OAI

/-! # Coarse-feature cancellation for discrete integer starting points -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem residueBinAverage_discrete_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) {H : ℕ} (hH : 0 < H) (a b : ℕ) {X Y : ℝ}
    (hXY : X ≤ Y) (hXa : X ≤ a) (hbY : (b : ℝ) ≤ Y) :
    (∑ u ∈ Ico a b, ‖residueBinAverage E ζ μ w r H u‖^2) ≤
      ∫ z in X..Y, ‖residueBinAverage E ζ μ w r H z‖^2 := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  by_cases hab : a ≤ b
  · rw [residueBinAverage_discrete_energy E ζ μ w r hH a b hab]
    exact intervalIntegral.integral_mono_interval hXa (by exact_mod_cast hab) hbY
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (complexShortAverage_sq_integrable_any f (by exact_mod_cast hH) X Y)
  · rw [Ico_eq_empty_of_le (by omega : b ≤ a),sum_empty]
    exact intervalIntegral.integral_nonneg hXY (fun _ _ => sq_nonneg _)

theorem all_residues_coarse_discrete_short
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {q : ℕ} [NeZero q] (A scale : ℕ → ℝ) (H : ℕ → ℕ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ r : ZMod q,
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) r (H B) u‖^2) < ε := by
  have hshort := all_residues_coarse_short_with_center hMR hMRT hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b (q := q) A scale (fun B => (H B : ℝ)) hA hscale
    (tendsto_natCast_atTop_atTop.comp hH)
  intro ε hε
  filter_upwards [hshort ε hε,hH.eventually_gt_atTop 0] with B hB hHB
  filter_upwards [hB,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro r
  apply lt_of_le_of_lt _ (hn r)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply residueBinAverage_discrete_energy_le _ ζ μ _ r hHB
  · linarith
  · exact Nat.le_ceil _
  · exact Nat.floor_le (by linarith)

end JointDickman

end OAI
