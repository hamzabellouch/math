import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessErrorBelowTrace
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResiduesAdd
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.Adj

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.Localization
variable {S : PrimeSystem} {B τ C₀ T : ℝ} {h ℓ L D₀ : ℕ}

def traceMean (D : S.DivisorFamily B τ C₀) (hh : 0<h) (L ℓ D₀ : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) : ℝ :=
  ∑ w : WindowWalk D h ℓ D₀,(w.coefficient a).re *
    avg (fun r => S.chronologicalKernel (w.line hh).line cut r *
      allowedIndicator (w.line hh).line D L r)

lemma traceMean_le (D : S.DivisorFamily B τ C₀) (hh : 0<h) (L ℓ D₀ : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (ha : ∀ d∈D.members,‖a d‖≤1) :
    traceMean D hh L ℓ D₀ cut a ≤
      (D₀:ℝ)*NumericalLine.fullTraceSum D h ℓ L cut := by
  let F : Fin D₀ × NumericalLine D h ℓ → ℝ := fun z =>
    |avg (fun r => S.chronologicalKernel z.2.line cut r *
      allowedIndicator z.2.line D L r)|
  let enc := fun w : WindowWalk D h ℓ D₀ => (w.val 0,w.line hh)
  have hinj : Function.Injective enc := WindowWalk.encode_injective hh
  calc
    _ ≤ ∑ w : WindowWalk D h ℓ D₀,F (enc w) := by
      apply sum_le_sum
      intro w hw
      have hc := (Complex.abs_re_le_norm (w.coefficient a)).trans (w.coefficient_norm a ha)
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans_eq (one_mul _)
    _ = ∑ z∈univ.image enc,F z := by rw [sum_image]; exact fun x hx y hy he => hinj he
    _ ≤ ∑ z : Fin D₀ × NumericalLine D h ℓ,F z :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z hz hn => abs_nonneg _)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [F,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        NumericalLine.fullTraceSum]

lemma trace_tendsto (D : S.DivisorFamily B τ C₀) (hh : 0<h) (hℓ : 0<ℓ)
    (L D₀ : ℕ) (cut : S.Cutoffs T) (a : ℕ→ℂ) (z : ℝ→ℤ) :
    Tendsto (fun X : ℝ => (∑ n∈range ⌊X⌋₊,
      (((symMatrix D h L cut a D₀ ((n:ℤ)+z X))^ℓ).trace.re))/X)
      atTop (nhds (traceMean D hh L ℓ D₀ cut a)) := by
  have hs := tendsto_finsetSum univ (fun (w : WindowWalk D h ℓ D₀) hw =>
    (tendsto_const_nhds (x := (w.coefficient a).re)).mul (S.real_origin_tendsto
      (fun r => S.chronologicalKernel (w.line hh).line cut r *
        allowedIndicator (w.line hh).line D L r)
      (fun X => z X+(w.val 0).val)))
  convert hs using 1
  · funext X
    simp only [matrix_trace, WindowWalk.matrix_product (hh:=hh) (hℓ:=hℓ),
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,mul_zero,sub_zero]
    rw [sum_comm,sum_div]
    apply sum_congr rfl
    intro w hw
    simp only [add_assoc,←mul_sum,mul_div_assoc]
  · rfl

open scoped Matrix.Norms.L2Operator
lemma traceMean_nonneg (D : S.DivisorFamily B τ C₀) (hh : 0<h)
    (L D₀ m : ℕ) (hD : 0<D₀) (hm : 0 < m) (cut : S.Cutoffs T) (a : ℕ→ℂ) :
    0 ≤ traceMean D hh L (2*m) D₀ cut a := by
  have ht := trace_tendsto D hh (by omega : 0 < 2*m) L D₀ cut a (fun _=>0)
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX
  apply div_nonneg _ hX
  apply sum_nonneg
  intro n hn
  exact (pow_nonneg (norm_nonneg _) _).trans (matrix_norm_moment D hh L cut a _ hD m)

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding

end

end OAI
