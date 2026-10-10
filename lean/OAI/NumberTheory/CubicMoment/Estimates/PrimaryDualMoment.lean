import OAI.NumberTheory.CubicMoment.Estimates.PrimaryIdealMoments
import OAI.NumberTheory.CubicMoment.Estimates.SmoothHeckeMoment

namespace OAI

/-! Summing the actual cubic dual dyads. The conductor and root-number
phases are outside the polynomials, and the dyadic loss is explicit. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealDyadIndex_scale_le {J : ℝ} {j : ℕ}
    (hj : j ∈ idealDyadIndices (fullIdealBall J)) : (2:ℝ)^j ≤ J := by
  obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hj
  exact (idealDyad_norm (show ν ∈ idealDyad (fullIdealBall J) (idealDyadIndex ν) from
    Finset.mem_filter.mpr ⟨hν,rfl⟩)).1.trans (mem_fullIdealBall.mp hν)

/-- The retained integral for the actual primary-normalized characters
has the predicted cubic second-moment size, with an explicit squared
dyad count. The fixed local factor is an actual coefficient twist. -/
theorem retained_primary_cubic_moment {ε : ℝ} (hε : 0 < ε)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset Eisenstein) (b : Eisenstein)
      (ξ : EisensteinIdealExponent → ℂ) (root : Eisenstein → ℂ)
      (A : Eisenstein → ℝ) (N J Z t : ℝ),
      primary b → (∀ ν, ‖ξ ν‖ ≤ 1) →
      (∀ a ∈ P, ‖root a‖ = 1) → (∀ a ∈ P, 0 < A a) →
      1 ≤ N → 1 ≤ J → 1 ≤ Z →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ a ∈ P, ‖finiteDualIntegral W (fullIdealBall J)
        (fun ν => ξ ν*primaryMixedIdealChar a b ν) idealExponentNorm (root a) (A a) Z t‖^2) ≤
        C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) := by
  obtain ⟨C,hC,hret⟩ := retained_ideal_dyadic_moment_transfer W hW hpos hsm
  obtain ⟨D,hD,hcubic⟩ := normalized_primary_ideal_cubic_moment hε
  refine ⟨2*C*D,by positivity,?_⟩
  intro P b ξ root A N J Z t hb hξ hroot hA hN hJ hZ hP
  let B (j : ℕ) : ℝ := D*(N*(2*(2:ℝ)^j))^ε*(2*(2:ℝ)^j)*
    (N+2*(2:ℝ)^j+(N*(2*(2:ℝ)^j))^(2/3:ℝ))
  have hbudget : ∀ j ∈ idealDyadIndices (fullIdealBall J),
      (Z/(2:ℝ)^j)*B j ≤
        2*D*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) := by
    intro j hj
    have hjJ := idealDyadIndex_scale_le hj
    have hj0 : 0 < (2:ℝ)^j := by positivity
    have hNj : 0 ≤ N*(2*(2:ℝ)^j) := by positivity
    have hmul : N*(2*(2:ℝ)^j) ≤ N*(2*J) := by gcongr
    have he := Real.rpow_le_rpow hNj hmul hε.le
    have he23 := Real.rpow_le_rpow hNj hmul (by norm_num : (0:ℝ) ≤ 2/3)
    have hsum : N+2*(2:ℝ)^j+(N*(2*(2:ℝ)^j))^(2/3:ℝ) ≤
        N+2*J+(N*(2*J))^(2/3:ℝ) := by linarith
    calc
      _ = 2*D*Z*(N*(2*(2:ℝ)^j))^ε*
          (N+2*(2:ℝ)^j+(N*(2*(2:ℝ)^j))^(2/3:ℝ)) := by
            dsimp [B]
            field_simp
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hsum
        (by positivity) (by positivity)
  have hm : ∀ j ∈ idealDyadIndices (fullIdealBall J), ∀ τ : ℝ,
      (∑ a : P, ‖normalizedDualPolynomial (idealDyad (fullIdealBall J) j)
        (fun ν => ξ ν*primaryMixedIdealChar a b ν) idealExponentNorm ((2:ℝ)^j) (τ-t)‖^2) ≤ B j := by
    intro j hj τ
    rw [Finset.sum_coe_sort P (fun a : Eisenstein =>
      ‖normalizedDualPolynomial (idealDyad (fullIdealBall J) j)
        (fun ν => ξ ν*primaryMixedIdealChar a b ν) idealExponentNorm ((2:ℝ)^j) (τ-t)‖^2)]
    apply hcubic P (idealDyad (fullIdealBall J) j) b ξ N (2*(2:ℝ)^j) ((2:ℝ)^j) (τ-t)
      hb (fun ν _ => hξ ν) hN (by have := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := j); linarith)
      (by positivity) hP (fun ν hν => idealDyad_norm hν)
  have h := hret (fullIdealBall J) (fun a : P => fun ν => ξ ν*primaryMixedIdealChar a b ν)
    (fun a : P => root a) (fun a : P => A a)
    (fun a => hroot a a.property) (fun a => hA a a.property) Z t B hZ
    (fun j _ => by dsimp [B]; positivity) hm
  rw [Finset.sum_coe_sort P (fun a : Eisenstein =>
    ‖finiteDualIntegral W (fullIdealBall J) (fun ν => ξ ν*primaryMixedIdealChar a b ν)
      idealExponentNorm (root a) (A a) Z t‖^2)] at h
  apply h.trans
  calc
    _ ≤ ((idealDyadIndices (fullIdealBall J)).card:ℝ)*C*
      ∑ _j ∈ idealDyadIndices (fullIdealBall J),
        2*D*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbudget) (by positivity)
    _ = _ := by simp; ring

/-- From the exact completed Hecke inputs, the full smooth sum inherits
the explicit cubic dual bound and the arbitrarily small truncation error.
The dual coefficients here are the actual primary-normalized characters. -/
theorem full_smooth_primary_cubic_moment {ε : ℝ} (hε : 0 < ε)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {δ : ℝ} (hδ : 0 < δ) (H R : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b : Eisenstein)
      (χ : Eisenstein → EisensteinIdealExponent → ℂ)
      (ξ : EisensteinIdealExponent → ℂ) (root : Eisenstein → ℂ)
      (A : Eisenstein → ℝ) (N Y Z J t : ℝ),
      primary b → (∀ a ∈ P, ∀ ν, ‖χ a ν‖ ≤ 1) → (∀ ν, ‖ξ ν‖ ≤ 1) →
      (∀ a ∈ P, ‖root a‖ = 1) → (∀ a ∈ P, 0 < A a) →
      1 ≤ N → 1 ≤ Y → 1 ≤ Z → 1 ≤ J → Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ a ∈ P, ((A a)^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ)) →
      ∀ (L Ldual : Eisenstein → ℂ → ℂ),
      (∀ a ∈ P, Differentiable ℂ (L a)) →
      (∀ a ∈ P, ∀ s : ℂ, 1 < s.re → L a s = normDirichletSeries (χ a) idealExponentNorm s) →
      (∀ a ∈ P, ∀ s : ℂ, 1 < s.re → Ldual a s = normDirichletSeries
        (fun ν => ξ ν*primaryMixedIdealChar a b ν) idealExponentNorm s) →
      (∀ a ∈ P, HeckeFunctionalEquation (A a) 0 (root a) (L a) (Ldual a)) →
      (∀ a ∈ P, CompletedHeckeFiniteOrder (A a) (L a)) →
      (∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2) →
      (∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) →
      (∑ a ∈ P, ‖∑' ν, χ a ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2) ≤
        C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by
  obtain ⟨C,hC,hret⟩ := retained_primary_cubic_moment hε W hW hpos hsm
  obtain ⟨D,hD,happrox⟩ := hecke_smooth_approximation_of_completed W hW hpos hsm hδ H R
  refine ⟨2*C,2*D^2,by positivity,by positivity,?_⟩
  intro P b χ ξ root A N Y Z J t hb hχ hξ hroot hA hN hY hZ hJ hZH hJH hP hcut L Ldual hL hs hds hFE hcomp hGI hGQ
  let V (a : Eisenstein) := finiteDualIntegral W (fullIdealBall J)
    (fun ν => ξ ν*primaryMixedIdealChar a b ν) idealExponentNorm (root a) (A a) Z t
  have hv := hret P b ξ root A N J Z t hb hξ hroot hA hN hJ hZ hP
  have ha (a : Eisenstein) (hap : a ∈ P) :
      ‖(∑' ν, χ a ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z))-V a‖ ≤ D*Y^(-R) := by
    have hd : ∀ ν, ‖ξ ν*primaryMixedIdealChar a b ν‖ ≤ 1 := by
      intro ν
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul (hξ ν)
        (primaryMixedIdealChar_norm_le_one (hP a hap).1 hb ν) (_root_.norm_nonneg _) zero_le_one
    exact happrox (χ a) (fun ν => ξ ν*primaryMixedIdealChar a b ν) (hχ a hap) hd
      (root a) (hroot a hap).le Y (A a) Z J t hY (hA a hap) hZ
      (zero_lt_one.trans_le hJ) hZH hJH (hcut a hap) (L a) (Ldual a)
      (hL a hap) (hs a hap) (hds a hap) (hFE a hap) (hcomp a hap) hGI hGQ
  have hn (a : Eisenstein) (hap : a ∈ P) :
      ‖∑' ν, χ a ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2 ≤
      2*‖V a‖^2+2*(D*Y^(-R))^2 := by
    have he := ha a hap
    have he0 : 0 ≤ D*Y^(-R) := by positivity
    have htriangle := norm_add_le (V a)
      ((∑' ν, χ a ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z))-V a)
    have hsame : V a+((∑' ν, χ a ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z))-V a) =
        (∑' ν, χ a ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) := by ring
    rw [hsame] at htriangle
    have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _)
      (htriangle.trans (add_le_add le_rfl he)) 2
    nlinarith [sq_nonneg (‖V a‖-D*Y^(-R))]
  calc
    _ ≤ ∑ a ∈ P, (2*‖V a‖^2+2*(D*Y^(-R))^2) := Finset.sum_le_sum hn
    _ = 2*(∑ a ∈ P, ‖V a‖^2)+2*P.card*(D*Y^(-R))^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ 2*(C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)))+2*P.card*(D*Y^(-R))^2 := by
      gcongr
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
