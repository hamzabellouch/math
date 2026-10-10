import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ZeroSum
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ResidueComparison

namespace OAI

/-!
# From separated zeros and Hadamard's identity to a uniform residue comparison

This is the downstream argument in the manuscript's residue lemma. The
zero coordinates, their separation, the baseline zero-sum bound, and
Hadamard's identity are explicit hypotheses. Their number-field instances
come from Stark (1974), Lemmas 3 and 8 and equation (9), together with the
Euler product.
-/

open Set

namespace DukePrimeDegree

/-- The constants in the residue comparison depend only on the uniform
zero-separation, baseline sum, and gamma-factor bounds, not on `L` or `h`. -/
theorem residue_comparison_from_separated_zeros {ι : Type*}
    (F G : ℝ → ℝ) (X Y : ι → ℝ) (L c A B h : ℝ)
    (hL : 1 ≤ L) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 < h) (hlen : h ≤ 4 / L)
    (hX : ∀ i, 0 ≤ X i) (hgap : ∀ i, c ^ 2 ≤ X i ^ 2 + Y i ^ 2)
    (hsum : Summable (fun i => (X i + 1) / ((X i + 1) ^ 2 + Y i ^ 2)))
    (hbaseline : (∑' i, (X i + 1) / ((X i + 1) ^ 2 + Y i ^ 2)) ≤ A)
    (hgamma : ∀ σ, 1 < σ → σ ≤ 1 + 4 / L → |G σ| ≤ B)
    (hhadamard : ∀ σ, 1 < σ → σ ≤ 1 + 4 / L →
      deriv (fun s => Real.log (F s)) σ =
        L * (∑' i, (X i + L * (σ - 1)) /
          ((X i + L * (σ - 1)) ^ 2 + Y i ^ 2)) - 1 / σ - L / 2 - G σ)
    (hresidue : 0 < F 1) (hvalue : 0 < F (1 + h))
    (hcont : ContinuousOn (fun x => Real.log (F x)) (Icc 1 (1 + h)))
    (hdiff : DifferentiableOn ℝ (fun x => Real.log (F x)) (Ioo 1 (1 + h))) :
    let C := (8 + 8 / c ^ 2) * A + B + 2
    Real.exp (-4 * C) * F 1 ≤ F (1 + h) ∧
      F (1 + h) ≤ Real.exp (4 * C) * F 1 := by
  let C₀ := 8 + 8 / c ^ 2
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  apply residue_comparison_on_short_interval F (zero_lt_one.trans_le hL) hh
    (by positivity) hlen hresidue hvalue hcont hdiff
  intro σ hσ
  have hσrange : σ ≤ 1 + 4 / L := by linarith [hσ.2]
  have hU : 0 < L * (σ - 1) := mul_pos (zero_lt_one.trans_le hL) (sub_pos.mpr hσ.1)
  have hU4 : L * (σ - 1) ≤ 4 := by
    have hmul := (le_div_iff₀ (zero_lt_one.trans_le hL)).mp (show σ - 1 ≤ 4 / L by linarith)
    nlinarith
  obtain ⟨_, hcompare⟩ := zero_sum_comparison X Y c (L * (σ - 1)) hc hU hU4 hX hgap hsum
  have hsum_le : (∑' i, (X i + L * (σ - 1)) /
      ((X i + L * (σ - 1)) ^ 2 + Y i ^ 2)) ≤ C₀ * A :=
    hcompare.trans (mul_le_mul_of_nonneg_left hbaseline hC₀)
  have hsum_nonneg : 0 ≤ (∑' i, (X i + L * (σ - 1)) /
      ((X i + L * (σ - 1)) ^ 2 + Y i ^ 2)) := by
    apply tsum_nonneg
    intro i
    exact div_nonneg (add_nonneg (hX i) hU.le) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  apply log_derivative_bound_from_hadamard hL hσ.1.le
    hB
    (mul_nonneg (zero_le_one.trans hL) hsum_nonneg)
    ?_ (hgamma σ hσ.1 hσrange) (hhadamard σ hσ.1 hσrange)
  simpa only [mul_comm L] using
    mul_le_mul_of_nonneg_left hsum_le (zero_le_one.trans hL)

end DukePrimeDegree

end OAI
