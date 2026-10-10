import OAI.NumberTheory.JointDickman.Amplification.BinCounts
import OAI.NumberTheory.JointDickman.Counting.ShortIntervalConsequences
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

namespace OAI

/-!
# The real/principal short-average estimate for the actual bin labels

Finite interpolation on fixed windows combines with the
published real short-interval input. Real multiplicative weights are allowed,
so the result includes the principal-character summands in `labels-short`.

The weighted long-mean limit remains an explicit arithmetic marginal
hypothesis. No short-average estimate, correlation statement, or independence
claim is assumed in place of it.
-/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology
open PublishedInputs

/-- The short average of the actual centered bin label with a real weight. -/
noncomputable def weightedBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    (H z : ℝ) : ℂ :=
  (∑ m ∈ Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊,
    (binLabel E ζ m - μ) * (w m : ℂ)) / (H : ℂ)

/-- The real multiplicative interpolants after multiplying by the real weight. -/
noncomputable def weightedBinInterpolant {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) {m : ℕ} (a : ι → Fin m) :
    ArithmeticFunction ℝ :=
  (binLabel E (fun i => interpolationNode (a i))).pmul w

theorem weightedBinInterpolant_isMultiplicative {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : w.IsMultiplicative)
    {m : ℕ} (a : ι → Fin m) : (weightedBinInterpolant E w a).IsMultiplicative :=
  (binLabel_isMultiplicative E _).pmul hw

theorem abs_weightedBinInterpolant_le_one {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : ∀ n, |w n| ≤ 1)
    {m : ℕ} (a : ι → Fin m) (n : ℕ) : |weightedBinInterpolant E w a n| ≤ 1 := by
  simp only [weightedBinInterpolant, ArithmeticFunction.pmul_apply, abs_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (abs_binLabel_le_one E _ (fun i => interpolationNode_mem (a i)) n)
      (hw n) (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

private theorem finite_average_eq_combination {α : Type*} (s : Finset α)
    (c : α → ℂ) (f : α → ArithmeticFunction ℝ) (g : ℕ → ℂ)
    (S : Finset ℕ) (H : ℝ)
    (heq : ∀ m ∈ S, g m = ∑ a ∈ s, c a * (f a m : ℂ)) :
    (∑ m ∈ S, g m) / (H : ℂ) =
      ∑ a ∈ s, c a * (((∑ m ∈ S, f a m) / H : ℝ) : ℂ) := by
  rw [Finset.sum_congr rfl heq, Finset.sum_comm]
  simp only [Finset.sum_div, Complex.ofReal_div, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Finite-window interpolation gives exact equality of the short sums,
including their natural-number-floor endpoint convention. -/
theorem weightedBinAverage_eq_combination {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ) (J : ℕ)
    (c : (ι → Fin (J + 1)) → ℂ) (Y H z : ℝ)
    (hcoeff : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Y →
      binLabel E ζ m - μ = ∑ a : ι → Fin (J + 1),
        c a * (binLabel E (fun i => interpolationNode (a i)) m : ℂ))
    (hzH : z + H ≤ Y) :
    weightedBinAverage E ζ μ w H z =
      complexShortCombination Finset.univ c (weightedBinInterpolant E w) H z := by
  unfold weightedBinAverage complexShortCombination realShortAverage
  apply finite_average_eq_combination
  intro m hm
  have hmpos : 1 ≤ m := by
    have h := (Finset.mem_Ioc.mp hm).1
    omega
  have hmupper : (m : ℝ) ≤ Y := by
    exact ((Nat.le_floor_iff' (by omega : m ≠ 0)).mp (Finset.mem_Ioc.mp hm).2).trans hzH
  rw [hcoeff m hmpos hmupper, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedBinInterpolant, ArithmeticFunction.pmul_apply, Complex.ofReal_mul]
  ring

/-- The principal-character estimate for actual bin labels, conditional only
on the published real input and the weighted marginal long-mean
limit. The two limits have the manuscript's order: scale first, length second. -/
theorem weightedBinAverage_eventually_eventually
    (hMR : RealShortIntervalInput)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (ζ : ι → ℂ) (μ : ℂ)
    (w : ℕ → ArithmeticFunction ℝ) (hwmult : ∀ B, (w B).IsMultiplicative)
    (hw : ∀ B n, |w B n| ≤ 1)
    (A : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (H : ℕ → ℝ) (hH : Tendsto H atTop atTop)
    (hmarginal : ∀ B, Tendsto
      (fun n => weightedBinAverage (fun i => primeBin (scale n) J (k i)) ζ μ (w B)
        (A B * scale n) (A B * scale n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1 / (A B * scale n)) *
        (∫ z in (A B * scale n)..2 * (A B * scale n),
          ‖weightedBinAverage (fun i => primeBin (scale n) J (k i)) ζ μ (w B) (H B) z‖ ^ 2)
        < ε := by
  obtain ⟨c, hc⟩ := centered_binLabel_interpolation ζ μ J
  let E : ℕ → ι → Finset ℕ := fun n i => primeBin (scale n) J (k i)
  let X : ℕ → ℕ → ℝ := fun B n => A B * scale n
  let f : ℕ → ℕ → (ι → Fin (J + 1)) → ArithmeticFunction ℝ :=
    fun B n => weightedBinInterpolant (E n) (w B)
  have hX (B : ℕ) : Tendsto (X B) atTop atTop :=
    hscale.const_mul_atTop (hA B)
  have hXpos (B : ℕ) : ∀ᶠ n in atTop, 0 < X B n :=
    (hX B).eventually (eventually_gt_atTop 0)
  have hHX (B : ℕ) : ∀ᶠ n in atTop, H B ≤ X B n :=
    (hX B).eventually (eventually_ge_atTop (H B))
  have hwindow (B : ℕ) : ∀ᶠ n in atTop, ∀ m : ℕ, 1 ≤ m →
      (m : ℝ) ≤ 3 * X B n →
      binLabel (E n) ζ m - μ = ∑ a : ι → Fin (J + 1),
        c a * (binLabel (E n) (fun i => interpolationNode (a i)) m : ℂ) := by
    have hb := hscale.eventually (primeBin_count_eventually_le J hJ (3 * A B))
    filter_upwards [hb] with n hn m hm hmupper
    apply hc (E n) m (by omega)
    intro i
    apply hn (k i) (hk i) m hm
    simpa only [X, mul_assoc] using hmupper
  have hlong (B : ℕ) : Tendsto
      (fun n => complexLongCombination Finset.univ c (f B n) (X B n)) atTop (𝓝 0) := by
    apply (hmarginal B).congr'
    filter_upwards [hwindow B, hXpos B] with n hn hnpos
    change weightedBinAverage (E n) ζ μ (w B) (X B n) (X B n) =
      complexLongCombination Finset.univ c (f B n) (X B n)
    simpa only [complexLongCombination, complexShortCombination, realLongAverage, f] using
      weightedBinAverage_eq_combination (E n) ζ μ (w B) J c (3 * X B n)
        (X B n) (X B n) hn (by linarith)
  have hbound := complexShortCombination_eventually_eventually hMR Finset.univ c f
    (fun B n a _ => weightedBinInterpolant_isMultiplicative (E n) (w B) (hwmult B) a)
    (fun B n a _ m => abs_weightedBinInterpolant_le_one (E n) (w B) (hw B) a m)
    H X hH hHX hlong
  have hintegral (B : ℕ) : ∀ᶠ n in atTop,
      (∫ z in X B n..2 * X B n,
        ‖weightedBinAverage (E n) ζ μ (w B) (H B) z‖ ^ 2) =
      (∫ z in X B n..2 * X B n,
        ‖complexShortCombination Finset.univ c (f B n) (H B) z‖ ^ 2) := by
    filter_upwards [hwindow B, hXpos B, hHX B] with n hn hnpos hnHX
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by linarith : X B n ≤ 2 * X B n)] at hz
    dsimp only
    rw [weightedBinAverage_eq_combination (E n) ζ μ (w B) J c (3 * X B n)
      (H B) z hn (by linarith [hz.2])]
  intro ε hε
  filter_upwards [hbound ε hε] with B hB
  filter_upwards [hB, hintegral B] with n hn heq
  change (1 / X B n) * (∫ z in X B n..2 * X B n,
    ‖weightedBinAverage (E n) ζ μ (w B) (H B) z‖ ^ 2) < ε
  rw [heq]
  exact hn

end JointDickman

end OAI
