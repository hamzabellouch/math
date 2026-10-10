import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveSmoothMoment
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveLogLoss

namespace OAI

/-! The application-sized primitive cubic moment, with the fixed logarithmic
losses absorbed into an arbitrary positive power. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem full_smooth_primitive_cubic_bound (hpub : PrimitiveResidueHeckeInput)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b : Eisenstein) (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → 1 ≤ N → 1 ≤ Y → 1 ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∀ a ∈ P, d a ≠ 0) → (∀ a ∈ P, PrimitiveResidueCharacter (d a) (ψ a)) →
      (∀ a ∈ P, ψ a ≠ 1) →
      (∀ a ∈ P, ∀ v : Eisensteinˣ, ψ a (Ideal.Quotient.mk (modulus (d a)) v) = 1) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) = mixedCubic a b x) →
      (∀ a ∈ P, ((residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ)) →
      (∑ a ∈ P, ‖∑' ν, residueIdealChar (d a) (ψ a) ν*
        mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2) ≤
        C*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := full_smooth_primitive_cubic_moment hpub
    (show 0 < ε/2 by positivity) W hW hpos hsm hδ H R hGI hGQ
  obtain ⟨E,hE,hlog⟩ := primitive_moment_weighted_log_loss hε
  refine ⟨C*E,D,mul_nonneg hC hE.le,hD,?_⟩
  intro P b d ψ N Y Z J t hb hsb hN hY hZ hJ hZH hJH hP hd hp hn hu hagree hcut
  apply (hbound P b d ψ N Y Z J t hb hsb hN hY hZ hJ hZH hJH
    hP hd hp hn hu hagree hcut).trans
  have hF : 0 ≤ N+2*J+(N*(2*J))^(2/3:ℝ) := by positivity
  calc
    _ = C*Z*((((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*ramifiedMomentLoss J)*
        (N*(2*J))^(ε/2))*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by ring
    _ ≤ C*Z*(E*(N*(2*J))^ε)*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by
      have hm : C*Z*((((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*ramifiedMomentLoss J)*
          (N*(2*J))^(ε/2))*(N+2*J+(N*(2*J))^(2/3:ℝ)) ≤
          C*Z*(E*(N*(2*J))^ε)*(N+2*J+(N*(2*J))^(2/3:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlog N J hN hJ)
          (show 0 ≤ C*Z by positivity)) hF
      exact add_le_add hm le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
