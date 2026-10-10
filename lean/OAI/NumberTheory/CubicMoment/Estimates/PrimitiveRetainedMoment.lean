import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveDualConjugation
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryDualMoment

namespace OAI

/-! The retained functional-equation integrals of the actual primitive
characters have the cubic second moment, with explicit logarithmic losses. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def ramifiedMomentLoss (J : ℝ) : ℝ :=
  ((((Nat.log 2 ⌊2*J⌋₊+1:ℕ):ℝ)^ramifiedIdealPrimes.card))^2

lemma ramifiedMomentLoss_nonneg (J : ℝ) : 0 ≤ ramifiedMomentLoss J := sq_nonneg _

theorem retained_primitive_cubic_moment {ε : ℝ} (hε : 0 < ε)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset Eisenstein) (b : Eisenstein)
      (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
      (root : Eisenstein → ℂ) (A : Eisenstein → ℝ) (N J Z t : ℝ),
      primary b → Squarefree b →
      (∀ a ∈ P, d a ≠ 0) →
      (∀ a ∈ P, ∀ v : Eisensteinˣ, ψ a (Ideal.Quotient.mk (modulus (d a)) v) = 1) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) = mixedCubic a b x) →
      (∀ a ∈ P, ‖root a‖ = 1) → (∀ a ∈ P, 0 < A a) →
      1 ≤ N → 1 ≤ J → 1 ≤ Z →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∑ a ∈ P, ‖finiteDualIntegral W (fullIdealBall J)
        (residueIdealChar (d a) (star (ψ a))) idealExponentNorm (root a) (A a) Z t‖^2) ≤
        C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*ramifiedMomentLoss J*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) := by
  obtain ⟨C,hC,hret⟩ := retained_ideal_dyadic_moment_transfer W hW hpos hsm
  obtain ⟨D,hD,hcubic⟩ := normalized_primitive_ideal_cubic_moment hε
  refine ⟨2*C*D,by positivity,?_⟩
  intro P b d ψ root A N J Z t hb hsb hd hu hagree hroot hA hN hJ hZ hP
  let L := ramifiedMomentLoss J
  have hL : 0 ≤ L := ramifiedMomentLoss_nonneg J
  let B (j : ℕ) : ℝ := D*L*(N*(2*(2:ℝ)^j))^ε*(2*(2:ℝ)^j)*
    (N+2*(2:ℝ)^j+(N*(2*(2:ℝ)^j))^(2/3:ℝ))
  have hbudget : ∀ j ∈ idealDyadIndices (fullIdealBall J),
      (Z/(2:ℝ)^j)*B j ≤
        2*D*L*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) := by
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
      _ = 2*D*L*Z*(N*(2*(2:ℝ)^j))^ε*
          (N+2*(2:ℝ)^j+(N*(2*(2:ℝ)^j))^(2/3:ℝ)) := by
            dsimp [B]
            field_simp
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hsum
        (by positivity) (by positivity)
  have hm : ∀ j ∈ idealDyadIndices (fullIdealBall J), ∀ τ : ℝ,
      (∑ a : P, ‖normalizedDualPolynomial (idealDyad (fullIdealBall J) j)
        (residueIdealChar (d a) (star (ψ a))) idealExponentNorm ((2:ℝ)^j) (τ-t)‖^2) ≤ B j := by
    intro j hj τ
    have hjJ := idealDyadIndex_scale_le hj
    have hj1 : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hcard : ((ramifiedParts (idealDyad (fullIdealBall J) j)).card:ℝ)^2 ≤ L := by
      dsimp [L,ramifiedMomentLoss]
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast ramifiedParts_card_le (J := 2*J)
        (fun ν hν => (idealDyad_norm hν).2.trans (by gcongr))
    rw [Finset.sum_coe_sort P (fun a : Eisenstein =>
      ‖normalizedDualPolynomial (idealDyad (fullIdealBall J) j)
        (residueIdealChar (d a) (star (ψ a))) idealExponentNorm ((2:ℝ)^j) (τ-t)‖^2)]
    simp_rw [norm_dual_conjugate]
    apply (hcubic P (idealDyad (fullIdealBall J) j) b d ψ N ((2:ℝ)^j) (-(τ-t))
      hb hsb hN hj1 hP hd hu hagree
      (fun ν hν => ⟨(idealDyad_norm hν).1,(idealDyad_norm hν).2⟩)).trans
    dsimp [B]
    gcongr
  have h := hret (fullIdealBall J)
    (fun a : P => residueIdealChar (d a) (star (ψ a)))
    (fun a : P => root a) (fun a : P => A a)
    (fun a => hroot a a.property) (fun a => hA a a.property) Z t B hZ
    (fun j _ => by dsimp [B]; positivity) hm
  rw [Finset.sum_coe_sort P (fun a : Eisenstein =>
    ‖finiteDualIntegral W (fullIdealBall J) (residueIdealChar (d a) (star (ψ a)))
      idealExponentNorm (root a) (A a) Z t‖^2)] at h
  apply h.trans
  calc
    _ ≤ ((idealDyadIndices (fullIdealBall J)).card:ℝ)*C*
      ∑ _j ∈ idealDyadIndices (fullIdealBall J),
        2*D*L*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbudget) (by positivity)
    _ = _ := by simp [L]; ring

end CubicFirstMoment

end

end OAI
