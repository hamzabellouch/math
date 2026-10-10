import OAI.NumberTheory.CubicMoment.Estimates.HeckeDyadicMoment

namespace OAI

/-! A character average of actual full smooth sums is bounded by the
normalized dual dyad averages plus the proved negligible tail. -/

noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

private lemma norm_sq_le_twice_approx (x y : ℂ) {e : ℝ} (he : ‖x-y‖ ≤ e) :
    ‖x‖^2 ≤ 2*‖y‖^2+2*e^2 := by
  have he0 : 0 ≤ e := (_root_.norm_nonneg _).trans he
  have hn : ‖x‖ ≤ ‖y‖+e := by
    calc
      ‖x‖ = ‖y+(x-y)‖ := by congr 1; ring
      _ ≤ ‖y‖+‖x-y‖ := norm_add_le _ _
      _ ≤ ‖y‖+e := add_le_add le_rfl he
  have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖y‖-e)]

/-- The full smooth-sum moment, from the precisely specified completed
Hecke inputs and actual bounds for the normalized dual polynomials. -/
theorem full_smooth_hecke_moment
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {δ : ℝ} (hδ : 0 < δ) (H R : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ {ι : Type*} [Fintype ι], ∀ (χ χdual : ι → EisensteinIdealExponent → ℂ) (ε : ι → ℂ) (A : ι → ℝ),
      (∀ i ν, ‖χ i ν‖ ≤ 1) → (∀ i ν, ‖χdual i ν‖ ≤ 1) →
      (∀ i, ‖ε i‖ = 1) → (∀ i, 0 < A i) → ∀ (Y Z J t : ℝ),
      1 ≤ Y → 1 ≤ Z → 0 < J → Z ≤ Y^H → J ≤ Y^H →
      (∀ i, ((A i)^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ)) →
      ∀ (L Ldual : ι → ℂ → ℂ),
      (∀ i, Differentiable ℂ (L i)) →
      (∀ i s, 1 < s.re → L i s = normDirichletSeries (χ i) idealExponentNorm s) →
      (∀ i s, 1 < s.re → Ldual i s = normDirichletSeries (χdual i) idealExponentNorm s) →
      (∀ i, HeckeFunctionalEquation (A i) 0 (ε i) (L i) (Ldual i)) →
      (∀ i, CompletedHeckeFiniteOrder (A i) (L i)) →
      (∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2) →
      (∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) →
      ∀ B : ℕ → ℝ, (∀ j ∈ idealDyadIndices (fullIdealBall J), 0 ≤ B j) →
      (∀ j ∈ idealDyadIndices (fullIdealBall J), ∀ τ : ℝ,
        (∑ i, ‖normalizedDualPolynomial (idealDyad (fullIdealBall J) j) (χdual i)
          idealExponentNorm ((2:ℝ)^j) (τ-t)‖^2) ≤ B j) →
      (∑ i, ‖∑' ν, χ i ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2) ≤
        C*(idealDyadIndices (fullIdealBall J)).card *
          (∑ j ∈ idealDyadIndices (fullIdealBall J), (Z/(2:ℝ)^j)*B j) +
        D*Fintype.card ι*Y^(-2*R) := by
  obtain ⟨C,hC,hret⟩ := retained_ideal_dyadic_moment_transfer W hW hpos hsm
  obtain ⟨D,hD,happrox⟩ := hecke_smooth_approximation_of_completed W hW hpos hsm hδ H R
  refine ⟨2*C,2*D^2,by positivity,by positivity,?_⟩
  intro ι inst χ χdual ε A hχ hχdual hε hA Y Z J t hY hZ hJ hZH hJH hcut L Ldual hL hs hds hFE hcomp hGI hGQ B hB hP
  let V (i : ι) := finiteDualIntegral W (fullIdealBall J) (χdual i) idealExponentNorm (ε i) (A i) Z t
  have hv := hret (fullIdealBall J) χdual ε A hε hA Z t B hZ hB hP
  have ha (i : ι) :
      ‖(∑' ν, χ i ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z))-V i‖ ≤ D*Y^(-R) :=
    happrox (χ i) (χdual i) (hχ i) (hχdual i) (ε i) (hε i).le Y (A i) Z J t
      hY (hA i) hZ hJ hZH hJH (hcut i) (L i) (Ldual i) (hL i) (hs i) (hds i)
      (hFE i) (hcomp i) hGI hGQ
  calc
    _ ≤ ∑ i, (2*‖V i‖^2+2*(D*Y^(-R))^2) :=
      Finset.sum_le_sum (fun i _ => norm_sq_le_twice_approx _ _ (ha i))
    _ = 2*(∑ i, ‖V i‖^2)+2*(Fintype.card ι:ℝ)*(D*Y^(-R))^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ 2*(C*(idealDyadIndices (fullIdealBall J)).card *
          (∑ j ∈ idealDyadIndices (fullIdealBall J), (Z/(2:ℝ)^j)*B j)) +
        2*(Fintype.card ι:ℝ)*(D*Y^(-R))^2 := by
      gcongr
      exact hv.trans_eq (by ring)
    _ = _ := by
      have hp : (Y^(-R))^2 = Y^(-2*R) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans_le hY).le]
        congr 1
        ring
      rw [mul_pow,hp]
      ring

end CubicFirstMoment

end

end OAI
