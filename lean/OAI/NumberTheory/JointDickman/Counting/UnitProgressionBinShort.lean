import OAI.NumberTheory.JointDickman.Amplification.UnitProgressionBinAverage
import OAI.NumberTheory.JointDickman.Counting.ComplexShortIntegrability

namespace OAI

/-! # Weighted centered-bin short averages in every unit residue class -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem twistedWeightedBinAverage_sq_integrable {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖twistedWeightedBinAverage E ζ μ w χ H z‖^2) volume a b := by
  let f : ArithmeticFunction ℂ := ⟨fun n => (binLabel E ζ n-μ)*(w n : ℂ)*χ (n : ZMod q),by simp⟩
  exact complexShortAverage_sq_integrable_any f hH a b

theorem unitProgressionBinAverage_sq_integrable {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖unitProgressionBinAverage E ζ μ w r H z‖^2) volume a b := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  exact complexShortAverage_sq_integrable_any f hH a b

theorem unitProgressionBinAverage_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖unitProgressionBinAverage E ζ μ w r H z‖^2) ≤
      (1/(q.totient : ℝ))*∑ χ : DirichletCharacter ℂ q,
        (1/X)*(∫ z in X..2*X, ‖twistedWeightedBinAverage E ζ μ w χ H z‖^2) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hfi (χ : DirichletCharacter ℂ q) := twistedWeightedBinAverage_sq_integrable E ζ μ w χ hH X (2*X)
  have hsum : IntervalIntegrable (fun z =>
      (∑ χ : DirichletCharacter ℂ q, ‖twistedWeightedBinAverage E ζ μ w χ H z‖^2)/(q.totient : ℝ))
      volume X (2*X) := by
    simpa only [Finset.sum_apply] using (IntervalIntegrable.sum univ (fun χ _ => hfi χ)).div_const (q.totient : ℝ)
  have he := intervalIntegral.integral_mono (by linarith : X ≤ 2*X)
    (unitProgressionBinAverage_sq_integrable E ζ μ w r hH X (2*X)) hsum
    (unitProgressionBinAverage_square_le E ζ μ w r H)
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1/X)
  rw [intervalIntegral.integral_div,intervalIntegral.integral_finsetSum (fun χ _ => hfi χ)] at hh
  convert hh using 1
  rw [← mul_sum]
  ring

theorem unit_progressions_weightedBinAverage_short
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hBill : FiniteBinDistributionInput)
    {J : ℕ} (hJ : 2 ≤ J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ r : (ZMod q)ˣ,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖unitProgressionBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) r (H B) z‖^2) < ε := by
  obtain ⟨μ,hμ,hb⟩ := all_characters_weightedBinAverage_short hMR hMRT hKMT hM hBill
    hJ ζ hζ P hP t ht (q := q) A scale H hA hscale hH
  refine ⟨μ,hμ,?_⟩
  intro ε hε
  filter_upwards [hb (ε/2) (half_pos hε),hH.eventually_gt_atTop 0] with B hb hHB
  have hX : Tendsto (fun n => A B*scale n) atTop atTop := hscale.const_mul_atTop (hA B)
  filter_upwards [hb,hX.eventually_gt_atTop 0] with n hb hXn
  intro r
  have he := unitProgressionBinAverage_energy_le
    (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
    (finitePrimeWeight (P B) (t B)) r hHB hXn
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hc : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
    rw [← Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hs := sum_le_sum (s := univ) (fun χ _ => (hb χ).le)
  have hh := he.trans (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1/(q.totient : ℝ)))
  simp only [sum_const,card_univ,nsmul_eq_mul,hc] at hh
  have hid : (1/(q.totient : ℝ))*((q.totient : ℝ)*(ε/2)) = ε/2 := by field_simp
  rw [hid] at hh
  exact hh.trans_lt (by linarith)

end JointDickman

end OAI
