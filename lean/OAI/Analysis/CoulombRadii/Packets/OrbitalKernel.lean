import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.TwoBodyTensorIntegrable

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def orbitalKernel {A : Type*} {n : ℕ} (v : Fin n → A → ℂ) (x y : A) : ℂ :=
  ∑ i, star (v i y) * v i x

lemma complex_star_mul_self (z : ℂ) : star z * z = (↑(‖z‖^2) : ℂ) := by
  rw [mul_comm, Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z

lemma exchange_algebra {A : Type*} {n : ℕ} (v : Fin n → A → ℂ) (x y : A) :
    (∑ i, ∑ j, (star (v i x) * v j x) * (star (v j y) * v i y)) =
      (↑(‖orbitalKernel v x y‖^2) : ℂ) := by
  rw [← complex_star_mul_self]
  simp only [orbitalKernel, star_sum, star_mul, star_star, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma exchange_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℝ)
    (hw : ∀ i j, Integrable (fun xy : A × A => (w xy.1 xy.2 : ℂ) *
      ((star (v i xy.1) * v j xy.1) * (star (v j xy.2) * v i xy.2))) (μ.prod μ)) :
    (∑ i, ∑ j, ∫ xy : A × A, (w xy.1 xy.2 : ℂ) *
      ((star (v i xy.1) * v j xy.1) * (star (v j xy.2) * v i xy.2)) ∂(μ.prod μ)) =
      (((∫ xy : A × A, w xy.1 xy.2 * ‖orbitalKernel v xy.1 xy.2‖^2 ∂(μ.prod μ)) : ℝ) : ℂ) := by
  calc
    _ = ∫ xy : A × A, ∑ i, ∑ j, (w xy.1 xy.2 : ℂ) *
        ((star (v i xy.1) * v j xy.1) * (star (v j xy.2) * v i xy.2)) ∂(μ.prod μ) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hw i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hw i j)).symm
    _ = ∫ xy : A × A, ((w xy.1 xy.2 * ‖orbitalKernel v xy.1 xy.2‖^2 : ℝ) : ℂ)
        ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [] with xy
      simp_rw [← Finset.mul_sum]
      rw [exchange_algebra, Complex.ofReal_mul]
    _ = _ := integral_complex_ofReal

lemma determinant_two_body_real {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => (w xy.1 xy.2 : ℂ) *
      ((star (v a xy.1) * v c xy.1) * (star (v b xy.2) * v d xy.2))) (μ.prod μ)) :
    (∫ x : Fin n → A, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      ‖determinantWave v x‖^2 ∂(Measure.pi fun _ => μ)) =
      (n.factorial : ℝ) * ((∑ i, ∑ j, ∫ xy : A × A,
        w xy.1 xy.2 * (‖v i xy.1‖^2 * ‖v j xy.2‖^2) ∂(μ.prod μ)) -
        ∫ xy : A × A, w xy.1 xy.2 * ‖orbitalKernel v xy.1 xy.2‖^2 ∂(μ.prod μ)) := by
  have H := determinant_two_body_integral v (fun x y => (w x y : ℂ)) hv ho hw
  simp only [Finset.sum_sub_distrib] at H
  rw [exchange_integral v w (fun i j => hw i j j i)] at H
  simp_rw [complex_star_mul_self] at H
  apply Complex.ofReal_injective
  push_cast
  simpa only [← Complex.ofReal_sum, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_natCast] using H

lemma slaterWave_two_body_upper {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => (w xy.1 xy.2 : ℂ) *
      ((star (v a xy.1) * v c xy.1) * (star (v b xy.2) * v d xy.2))) (μ.prod μ))
    (hw0 : ∀ x y, 0 ≤ w x y) :
    (∫ x : Fin n → A, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      ‖slaterWave v x‖^2 ∂(Measure.pi fun _ => μ)) ≤
      ∑ i, ∑ j, ∫ xy : A × A, w xy.1 xy.2 * (‖v i xy.1‖^2 * ‖v j xy.2‖^2)
        ∂(μ.prod μ) := by
  have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have he (x : Fin n → A) : (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      ‖slaterWave v x‖^2 = (n.factorial : ℝ)⁻¹ *
        ((∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) * ‖determinantWave v x‖^2) := by
    simp only [slaterWave, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le]
    ring
  simp_rw [he]
  rw [integral_const_mul, determinant_two_body_real v w hv ho hw,
    ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  exact sub_le_self _ (integral_nonneg (fun xy => mul_nonneg (hw0 _ _) (sq_nonneg _)))

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
