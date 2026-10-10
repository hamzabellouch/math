import OAI.NumberTheory.CubicMoment.Estimates.TwistedRetainedMoment
import OAI.NumberTheory.CubicMoment.Estimates.PublishedPrimitiveHecke

namespace OAI

/-! The actual primitive mixed-character smooth sums, conditional only
on the cited Hecke continuation/completion and Gamma inputs. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem full_smooth_twisted_primitive_cubic_moment (hpub : PrimitiveResidueHeckeInput)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b : Eisenstein) (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
      (r : Eisenstein) (η : MulChar (Residues r) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → r ≠ 0 →
      (∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) v) = 1) →
      (∀ a ∈ P, IsCoprime (a*b) r) → 1 ≤ N → 1 ≤ Y → 1 ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∀ a ∈ P, d a ≠ 0) → (∀ a ∈ P, PrimitiveResidueCharacter (d a) (ψ a)) →
      (∀ a ∈ P, ψ a ≠ 1) →
      (∀ a ∈ P, ∀ v : Eisensteinˣ, ψ a (Ideal.Quotient.mk (modulus (d a)) v) = 1) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) →
      (∀ a ∈ P, ((residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ)) →
      (∑ a ∈ P, ‖∑' ν, residueIdealChar (d a) (ψ a) ν*
        mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2) ≤
        C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by
  obtain ⟨C,hC,hret⟩ := retained_twisted_primitive_cubic_moment hε W hW hpos hsm
  obtain ⟨D,hD,happrox⟩ := primitive_residue_smooth_approximation hpub
    W hW hpos hsm hδ H R hGI hGQ
  refine ⟨2*C,2*D^2,by positivity,by positivity,?_⟩
  intro P b d ψ r η N Y Z J t hb hsb hr hη hsmall hN hY hZ hJ hZH hJH hP hd hp hn hu hagree hcut
  have hex (a : P) : ∃ root : ℂ, ‖root‖ = 1 ∧
      ‖(∑' ν, residueIdealChar (d a) (ψ a) ν*mellinPhase t (idealExponentNorm ν)*
        W (idealExponentNorm ν/Z))-
        finiteDualIntegral W (fullIdealBall J) (residueIdealChar (d a) (star (ψ a)))
          idealExponentNorm root (residueHeckeScale (d a)) Z t‖ ≤ D*Y^(-R) := by
    obtain ⟨r,hr,he⟩ := happrox (d a) (hd a a.property) (ψ a)
      (hp a a.property) (hn a a.property) (hu a a.property)
    exact ⟨r,hr,he Y Z J t hY hZ (zero_lt_one.trans_le hJ) hZH hJH (hcut a a.property)⟩
  choose roots hroots he using hex
  let root : Eisenstein → ℂ := fun a => if h : a ∈ P then roots ⟨a,h⟩ else 1
  have hroot (a : Eisenstein) (ha : a ∈ P) : root a = roots ⟨a,ha⟩ := dite_eq_left ha
  let V (a : Eisenstein) := finiteDualIntegral W (fullIdealBall J)
    (residueIdealChar (d a) (star (ψ a))) idealExponentNorm (root a) (residueHeckeScale (d a)) Z t
  have hv := hret P b d ψ r η root (fun a => residueHeckeScale (d a)) N J Z t
    hb hsb hr hη hsmall hd hu hagree (fun a ha => by rw [hroot a ha]; exact hroots ⟨a,ha⟩)
    (fun a ha => residueHeckeScale_pos (hd a ha)) hN hJ hZ hP
  have ha (a : Eisenstein) (hap : a ∈ P) :
      ‖(∑' ν, residueIdealChar (d a) (ψ a) ν*mellinPhase t (idealExponentNorm ν)*
        W (idealExponentNorm ν/Z))-V a‖ ≤ D*Y^(-R) := by
    dsimp only [V]
    rw [hroot a hap]
    exact he ⟨a,hap⟩
  have hs (a : Eisenstein) (hap : a ∈ P) :
      ‖∑' ν, residueIdealChar (d a) (ψ a) ν*mellinPhase t (idealExponentNorm ν)*
        W (idealExponentNorm ν/Z)‖^2 ≤ 2*‖V a‖^2+2*(D*Y^(-R))^2 := by
    have htriangle := norm_add_le (V a)
      ((∑' ν, residueIdealChar (d a) (ψ a) ν*mellinPhase t (idealExponentNorm ν)*
        W (idealExponentNorm ν/Z))-V a)
    have hsame : V a+((∑' ν, residueIdealChar (d a) (ψ a) ν*
        mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z))-V a) =
        ∑' ν, residueIdealChar (d a) (ψ a) ν*mellinPhase t (idealExponentNorm ν)*
          W (idealExponentNorm ν/Z) := by ring
    rw [hsame] at htriangle
    have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _)
      (htriangle.trans (add_le_add le_rfl (ha a hap))) 2
    nlinarith [sq_nonneg (‖V a‖-D*Y^(-R))]
  calc
    _ ≤ ∑ a ∈ P, (2*‖V a‖^2+2*(D*Y^(-R))^2) := Finset.sum_le_sum hs
    _ = 2*(∑ a ∈ P, ‖V a‖^2)+2*P.card*(D*Y^(-R))^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ 2*(C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)))+2*P.card*(D*Y^(-R))^2 := by
      gcongr
    _ = _ := by
      have hpow : (Y^(-R))^2 = Y^(-2*R) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans_le hY).le]
        congr 1
        ring
      rw [mul_pow,hpow]
      ring

end CubicFirstMoment

end

end OAI
