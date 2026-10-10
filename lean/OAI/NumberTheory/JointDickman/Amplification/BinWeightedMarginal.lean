import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightAverages
import OAI.NumberTheory.JointDickman.Amplification.BinMarginalMean
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI

/-! # Finite-prime weights preserve the centered long mean -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def weightedCenteredBinPrefix (J : ℕ) (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (P : Finset ℕ) (t : ℕ → ℝ) (A x : ℝ) : ℂ :=
  (∑ n ∈ Ioc 0 ⌊A*x⌋₊,
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n-μ)*
      (finitePrimeWeight P t n : ℂ))/(A*x : ℂ)

theorem centeredBin_divisor_prefix_tendsto {J : ℕ} (hJ : 0 < J)
    (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto (centeredBinPrefix J ζ μ A) atTop (𝓝 0))
    {A : ℝ} (hA : 0 < A) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Ioc 0 ⌊A*x⌋₊, if d ∣ n then
        binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n-μ else 0)/(A*x : ℂ))
      atTop (𝓝 0) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ht := (hmean (A/d) (div_pos hA hdr)).const_mul (1/(d : ℂ))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [binLabel_eventually_mul_invariant J hJ
    (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ hd.ne',
    eventually_gt_atTop (0 : ℝ)] with x hinv hx
  rw [sum_divisible_Ioc _ _ d hd]
  simp_rw [hinv]
  have hf : ⌊A*x⌋₊/d = ⌊(A/(d : ℝ))*x⌋₊ := by
    rw [← Nat.floor_div_natCast]
    congr 1
    ring
  rw [hf]
  dsimp only [centeredBinPrefix]
  simp only [Complex.ofReal_div,Complex.ofReal_natCast]
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem weightedCenteredBinPrefix_tendsto {J : ℕ} (hJ : 0 < J)
    (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto (centeredBinPrefix J ζ μ A) atTop (𝓝 0))
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (weightedCenteredBinPrefix J ζ μ P t A) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum P.powerset (fun S hS =>
    (centeredBin_divisor_prefix_tendsto hJ ζ μ hmean hA
      (prod_pos (fun p hp => (hP p (mem_powerset.mp hS hp)).pos))).const_mul
        (((∏ p ∈ S, (t p-1) : ℝ) : ℂ)))
  simp only [mul_zero,sum_const_zero] at ht
  apply ht.congr'
  filter_upwards [] with x
  dsimp only [weightedCenteredBinPrefix]
  rw [finitePrimeWeight_sum_expansion hP]
  rw [sum_div]
  apply sum_congr rfl
  intro S hS
  rw [sum_divisible_Ioc _ _ _ (prod_pos (fun p hp => (hP p (mem_powerset.mp hS hp)).pos))]
  ring

theorem weightedBinAverage_eq_prefix {J : ℕ} (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (P : Finset ℕ) (t : ℕ → ℝ) {A x : ℝ} (hA : 0 < A) (hx : 0 < x) :
    weightedBinAverage (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ μ
      (finitePrimeWeight P t) (A*x) (A*x) =
      2*weightedCenteredBinPrefix J ζ μ P t (2*A) x-
        weightedCenteredBinPrefix J ζ μ P t A x := by
  let f := fun n => (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n-μ)*
    (finitePrimeWeight P t n : ℂ)
  have hAx : 0 < A*x := mul_pos hA hx
  have hfl : ⌊A*x⌋₊ ≤ ⌊(2*A)*x⌋₊ := Nat.floor_mono (by nlinarith)
  have hs := sum_Ioc_consecutive f (Nat.zero_le ⌊A*x⌋₊) hfl
  have hs' : (∑ n ∈ Ioc ⌊A*x⌋₊ ⌊(2*A)*x⌋₊, f n) =
      (∑ n ∈ Ioc 0 ⌊(2*A)*x⌋₊, f n)-(∑ n ∈ Ioc 0 ⌊A*x⌋₊, f n) := by
    linear_combination hs
  unfold weightedBinAverage
  simp only [Complex.ofReal_mul]
  change (∑ n ∈ Ioc ⌊A*x⌋₊ ⌊A*x+A*x⌋₊, f n)/(A*x : ℂ) = _
  rw [show A*x+A*x = (2*A)*x by ring,hs']
  unfold weightedCenteredBinPrefix
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp
  ring

theorem weightedBinAverage_long_tendsto {J : ℕ} (hJ : 0 < J)
    (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto (centeredBinPrefix J ζ μ A) atTop (𝓝 0))
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      weightedBinAverage (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ μ
        (finitePrimeWeight P t) (A*x) (A*x)) atTop (𝓝 0) := by
  have ht := ((weightedCenteredBinPrefix_tendsto hJ ζ μ hmean hP t
    (show 0 < 2*A by positivity)).const_mul 2).sub
      (weightedCenteredBinPrefix_tendsto hJ ζ μ hmean hP t hA)
  simp only [mul_zero,sub_self] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (weightedBinAverage_eq_prefix ζ μ P t hA hx).symm

end JointDickman

end OAI
