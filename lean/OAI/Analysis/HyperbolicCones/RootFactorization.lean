import OAI.Analysis.HyperbolicCones.ConeRoots
import OAI.Analysis.HyperbolicCones.LinePolynomial

namespace OAI

noncomputable section

open Polynomial

namespace Paper256

theorem linePolynomial_splits (x : Ambient) : (linePolynomial x).Splits := by
  apply Polynomial.Splits.of_splits_map_of_injective
    (algebraMap ℝ ℂ).injective (IsAlgClosed.splits _)
  intro z hz
  have hm : (linePolynomial x).map (algebraMap ℝ ℂ) ≠ 0 :=
    ((linePolynomial_monic x).map (algebraMap ℝ ℂ)).ne_zero
  have hr := (Polynomial.mem_roots hm).mp hz
  have hz0 : (linePolynomial x).aeval z = 0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hr
  have hi := linePolynomial_complex_roots_real x z hz0
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · rfl
  · change (0 : ℝ) = z.im
    exact hi.symm

theorem linePolynomial_card_roots (x : Ambient) : (linePolynomial x).roots.card = 20 := by
  rw [← (linePolynomial_splits x).natDegree_eq_card_roots, linePolynomial_natDegree]

theorem cone_iff_roots_nonnegative (x : Ambient) :
    x ∈ cone ↔ ∀ r ∈ (linePolynomial x).roots, 0 ≤ r := by
  rw [cone_iff_nonnegative_real_roots]
  simp only [Polynomial.mem_roots (linePolynomial_monic x).ne_zero, Polynomial.IsRoot]

theorem polynomial_shift_product (x : Ambient) (t : ℝ) :
    MvPolynomial.eval (coordinates (x + t • basePoint)) polynomial =
      ((linePolynomial x).roots.map (fun r => t + r)).prod := by
  rw [← linePolynomial_eval_neg,
    (linePolynomial_splits x).eval_eq_prod_roots_of_monic (linePolynomial_monic x)]
  have he : (linePolynomial x).roots.map (fun r => -t - r) =
      ((linePolynomial x).roots.map (fun r => t + r)).map (fun r => -r) := by
    rw [Multiset.map_map]
    congr 1
    funext r
    simp [neg_add_rev, sub_eq_add_neg, add_comm]
  rw [he, Multiset.prod_map_neg, Multiset.card_map, linePolynomial_card_roots]
  norm_num

end Paper256

end

end OAI
