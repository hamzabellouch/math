import OAI.Analysis.ModularRecovery.ErgodicAverages

namespace OAI

/-! Simultaneous finite approximations of modular moments. -/

universe u uE uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
namespace BoundedRecovery
variable {ι : Type uι} [Fintype ι]
lemma norm_sum_probability_smul_le {E : Type uE} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1)
    (f : ι → E) {C : ℝ} (hf : ∀ i, ‖f i‖ ≤ C) : ‖∑ i, p i • f i‖ ≤ C := by
  calc
    _ ≤ ∑ i, ‖p i • f i‖ := norm_sum_le _ _
    _ = ∑ i, p i * ‖f i‖ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp _)]
    _ ≤ ∑ i, p i * C := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hp i))
    _ = C := by rw [← Finset.sum_mul, hsum, one_mul]
end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData
variable {ι : Type uι} [Fintype ι]

lemma real_smul_mem (S : StandardModularData H) {a : H →L[ℂ] H} (ha : a ∈ S.M) (r : ℝ) :
    r • a ∈ S.M := by
  have hm := S.M.toStarSubalgebra.smul_mem ha (algebraMap ℝ ℂ r)
  rw [algebraMap_smul] at hm
  exact hm

def modularAverage (S : StandardModularData H) (p t : ι → ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, p i • S.sigma (t i) a

lemma modularAverage_mem (S : StandardModularData H) (p t : ι → ℝ) {a : H →L[ℂ] H}
    (ha : a ∈ S.M) : S.modularAverage p t a ∈ S.M := by
  exact sum_mem (fun i _ => S.real_smul_mem (S.sigma_mem (t i) ha) (p i))

lemma norm_modularAverage_le (S : StandardModularData H) (p t : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1) (a : H →L[ℂ] H) :
    ‖S.modularAverage p t a‖ ≤ ‖a‖ :=
  norm_sum_probability_smul_le p hp hsum _ (fun i => (S.norm_sigma (t i) a).le)

lemma modularAverage_apply_xi (S : StandardModularData H) (p t : ι → ℝ) (a : H →L[ℂ] H) :
    S.modularAverage p t a S.xi = ∑ i, p i • S.D.unitary (t i) (a S.xi) := by
  simp only [modularAverage, sum_apply, smul_apply, S.sigma_apply_xi]

lemma norm_modularAverage_apply_xi_sub_le (S : StandardModularData H) (p t : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1) (a : H →L[ℂ] H) (c : ℂ) :
    ‖S.modularAverage p t a S.xi - c • S.xi‖ ≤ ‖a S.xi - c • S.xi‖ := by
  have he : S.modularAverage p t a S.xi - c • S.xi =
      ∑ i, p i • S.D.unitary (t i) (a S.xi - c • S.xi) := by
    simp only [map_sub, map_smul, S.fixes_xi, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hsum, one_smul, S.modularAverage_apply_xi]
  rw [he]
  exact norm_sum_probability_smul_le p hp hsum _ (fun i => (S.D.norm_unitary_apply (t i) _).le)

lemma modularAverage_sandwich (S : StandardModularData H) (p t : ι → ℝ) (y b : H →L[ℂ] H) :
    (∑ i, p i * (S.state (star (S.sigma (t i) y) * b * S.sigma (t i) y)).re) =
      (inner ℂ (y S.xi) (S.modularAverage p (fun i => -t i) b (y S.xi))).re := by
  simp_rw [S.state_covariant_sandwich, S.state_sandwich]
  simp only [modularAverage, sum_apply, smul_apply, inner_sum, inner_smul_right_eq_smul, Complex.re_sum, Complex.smul_re, smul_eq_mul]

lemma averageSquare_eq (S : StandardModularData H) (p t : ι → ℝ) (y : H →L[ℂ] H) :
    (∑ i, p i • (star (S.sigma (t i) y) * S.sigma (t i) y)) =
      S.modularAverage p t (star y * y) := by
  simp only [modularAverage, S.sigma_mul, S.sigma_star]

lemma averageReverseSquare_eq (S : StandardModularData H) (p t : ι → ℝ) (y : H →L[ℂ] H) :
    (∑ i, p i • (S.sigma (t i) y * star (S.sigma (t i) y))) =
      S.modularAverage p t (y * star y) := by
  simp only [modularAverage, S.sigma_mul, S.sigma_star]

lemma isSelfAdjoint_averageSquare (p : ι → ℝ) (z : ι → H →L[ℂ] H) :
    IsSelfAdjoint (∑ i, p i • (star (z i) * z i)) := by
  simp only [IsSelfAdjoint, star_sum, star_smul, star_trivial, star_mul, star_star]

omit [CompleteSpace H] in
lemma re_inner_operator_le_of_small (h : H) (a : H →L[ℂ] H) (b : ℝ)
    (hsmall : ‖(a - b • (1 : H →L[ℂ] H)) h‖ < 1 / (‖h‖+1)) :
    (inner ℂ h (a h)).re < b * ‖h‖ ^ 2 + 1 := by
  let e := a - b • (1 : H →L[ℂ] H)
  have he : a h = e h + b • h := by simp [e]
  have hb : (inner ℂ h (b • h)).re = b * ‖h‖ ^ 2 := by
    rw [inner_smul_right_eq_smul, Complex.smul_re]
    simp only [smul_eq_mul]
    congr 1
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [he, inner_add_right, Complex.add_re, hb]
  have hi : (inner ℂ h (e h)).re ≤ ‖h‖ * ‖e h‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hn : ‖h‖ * ‖e h‖ < 1 := by
    calc
      _ ≤ (‖h‖+1) * ‖e h‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖h‖+1) * (1/(‖h‖+1)) := mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = 1 := by field_simp
  linarith

end StandardModularData
end BoundedRecovery

end
end

end OAI
