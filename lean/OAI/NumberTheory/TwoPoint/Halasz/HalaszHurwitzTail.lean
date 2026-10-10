import OAI.NumberTheory.TwoPoint.Halasz.HalaszHurwitzContinuation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! Uniform shifted-tail error, retaining the actual Hurwitz function. -/
namespace TwoPointCorrelations

open Complex HurwitzZeta Filter MeasureTheory Finset
open scoped Topology

lemma halasz_hurwitz_difference_tail {a : ℝ} (ha : a∈Set.Icc (0:ℝ) 1)
    {s : ℂ} (hs : 0<s.re) {N : ℕ} (hN : 1≤N) :
    ‖∑' n,halaszHurwitzDifference a (n+N) s‖≤
      ‖s‖*(N:ℝ)^(-s.re)/s.re := by
  have hN0 : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have he : -(s.re+1)< -1 := by linarith
  have hp : Summable (fun n : ℕ => ((n+N+1:ℕ):ℝ)^(-(s.re+1))) :=
    (Real.summable_nat_rpow.mpr he).comp_injective (fun _ _ h => by omega)
  have hanti : AntitoneOn (fun x : ℝ => x^(-(s.re+1))) (Set.Ici (N:ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hN0 hx) hxy (by linarith)
  have ht := hanti.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt he hN0)
    (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans hN0 hx)) _)
  have hi : (∫ x in Set.Ioi (N:ℝ),x^(-(s.re+1)))=(N:ℝ)^(-s.re)/s.re := by
    rw [integral_Ioi_rpow_of_lt he hN0]
    rw [show -(s.re+1)+1= -s.re by ring]
    exact neg_div_neg_eq _ _
  calc
    _ ≤ ∑' n : ℕ,‖s‖*((n+N+1:ℕ):ℝ)^(-(s.re+1)) :=
      tsum_of_norm_bounded (hp.mul_left ‖s‖).hasSum
        (fun n => halasz_hurwitz_difference_norm ha (n+N) hs)
    _ = ‖s‖*(∑' n : ℕ,((n+N+1:ℕ):ℝ)^(-(s.re+1))) := tsum_mul_left
    _ ≤ ‖s‖*((N:ℝ)^(-s.re)/s.re) :=
      mul_le_mul_of_nonneg_left (ht.trans_eq hi) (norm_nonneg s)
    _ = _ := by ring

/-- Transfer any unshifted zeta truncation bound to a uniform Hurwitz
truncation bound. The additional error has the same decay as Euler's
first-order remainder. -/
theorem halasz_hurwitz_cutoff_transfer {a : ℝ} (ha : a∈Set.Icc (0:ℝ) 1)
    {s : ℂ} (hs : 0<s.re) {N : ℕ} (hN : 1≤N) {E : ℝ}
    (hE : ‖riemannZeta s-(∑ n∈range N,((n+1:ℕ):ℂ)^(-s))‖≤E) :
    ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s-
      (∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s))‖≤
      E+‖s‖*(N:ℝ)^(-s.re)/s.re := by
  have hd := halasz_hurwitz_difference_series ha hs
  have hsplit := (halasz_hurwitz_difference_summable ha hs).sum_add_tsum_nat_add N
  have heq : hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s-
      (∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s)) =
      (riemannZeta s-(∑ n∈range N,((n+1:ℕ):ℂ)^(-s)))+
        ∑' n,halaszHurwitzDifference a (n+N) s := by
    rw [hd] at hsplit
    simp only [halaszHurwitzDifference,sum_sub_distrib,Complex.ofReal_natCast] at hsplit ⊢
    linear_combination -hsplit
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hE (halasz_hurwitz_difference_tail ha hs hN))

end TwoPointCorrelations

end OAI
