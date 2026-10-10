import OAI.NumberTheory.CubicMoment.Estimates.CorrectedSquareMass

namespace OAI

/-! Cauchy--Schwarz with the true squarefree corrected mass. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_gauss_sq_eq_moebius_sq {a : Eisenstein} (ha : primary a) :
    ‖gauss a‖^2 = (idealMoebius a:ℝ)^2 := by
  rw [norm_gauss ha,idealMoebius_sq]
  split_ifs <;> norm_num

theorem corrected_bilinear_mass_bound_sq (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hP : ∀ a ∈ P, primary a)
    (hB : ∀ b ∈ B, primary b) (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    {A R : ℝ} (hA : 0 < A) (hcut : ∀ x, R < x → V x = 0)
    (hPV : ∀ a ∈ P, 1 ≤ V (norm a/A)) :
    ‖(∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist u (a*b))-
      (cStar:ℂ)*dispersionModel B β u*
        (∑ a ∈ P, α a*normTwist u a*(if Squarefree a then (1:ℂ) else 0)*
          ((norm a^(-1/6:ℝ):ℝ):ℂ))‖^2 ≤
      (∑ a ∈ P, ‖α a‖^2)*correctedSquareMass B β u V A := by
  rw [corrected_bilinear_identity P B α β u hP hB]
  have hsub : P ⊆ primaryElementBall (R*A) := by
    intro a ha
    refine mem_primaryElementBall.mpr ⟨hP a ha,?_⟩
    apply (div_le_iff₀ hA).mp
    by_contra h
    have hz := hcut (norm a/A) (lt_of_not_ge h)
    have hv := hPV a ha
    rw [hz] at hv
    norm_num at hv
  have hrows : (∑ a ∈ P, ‖normTwist u a*gauss a*
      correctedDispersionPolynomial B β u a‖^2) ≤ correctedSquareMass B β u V A := by
    rw [correctedSquareMass_eq_sum B β u V hA le_rfl hcut]
    apply (Finset.sum_le_sum (g := fun a => (idealMoebius a:ℝ)^2*V (norm a/A)*
      ‖correctedDispersionPolynomial B β u a‖^2) ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (hV _)) (sq_nonneg _)))
    intro a ha
    simp only [norm_mul,norm_normTwist,one_mul,mul_pow,
      norm_gauss_sq_eq_moebius_sq (hP a ha)]
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (sq_nonneg _) (hPV a ha)) (sq_nonneg _)
  calc
    _ = ‖∑ a ∈ P, α a*(normTwist u a*gauss a*
        correctedDispersionPolynomial B β u a)‖^2 := by
      congr 2
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ (∑ a ∈ P, ‖α a‖^2)*
        ∑ a ∈ P, ‖normTwist u a*gauss a*correctedDispersionPolynomial B β u a‖^2 :=
      complex_bilinear_rows_sq P α _
    _ ≤ _ := mul_le_mul_of_nonneg_left hrows (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end CubicFirstMoment

end

end OAI
