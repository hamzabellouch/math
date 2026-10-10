import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteMean
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Scaled prefix means of the finite prime law -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem prefix_scaled_sum_tendsto (f : ℕ → ℝ) {L A : ℝ} (hA : 0 < A)
    (hf : Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/(N : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => (∑ n ∈ range (⌊A*x⌋₊+1), f n)/x) atTop (𝓝 (A*L)) := by
  have hAx : Tendsto (fun x : ℝ => A*x) atTop atTop := tendsto_id.const_mul_atTop hA
  have hN : Tendsto (fun x : ℝ => ⌊A*x⌋₊+1) atTop atTop :=
    tendsto_atTop_mono (fun x => Nat.le_add_right ⌊A*x⌋₊ 1) (tendsto_nat_floor_atTop.comp hAx)
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hAx
  have hsmall : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hratio : Tendsto (fun x : ℝ => ((⌊A*x⌋₊+1 : ℕ) : ℝ)/x) atTop (𝓝 A) := by
    have hh := (hfloor.mul_const A).add hsmall
    simp only [one_mul,add_zero,Function.comp_def] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hAx0 : A*x ≠ 0 := (mul_pos hA hx).ne'
    push_cast
    field_simp
  have hh := hratio.mul (hf.comp hN)
  apply hh.congr'
  filter_upwards [] with x
  have hN0 : ((⌊A*x⌋₊+1 : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp only [Function.comp_def]
  field_simp

theorem prime_site_scaled_sum_tendsto (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : (Q → Bool) → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ range (⌊A*x⌋₊+1), F (fun p => decide (p.val ∣ n)))/x)
      atTop (𝓝 (A*∑ y, fullPrimeMass Q y*F y)) :=
  prefix_scaled_sum_tendsto _ hA (prime_site_average_tendsto Q hQ F)

end JointDickman

end OAI
