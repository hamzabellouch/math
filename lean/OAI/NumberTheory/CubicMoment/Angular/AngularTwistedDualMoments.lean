import OAI.NumberTheory.CubicMoment.Angular.AngularTwistedIdealMatch
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryIdealMoments

namespace OAI

/-! The cubic second moment for actual primitive characters after a fixed
small twist. All exceptional small-prime parts remain explicit. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- A family of primitive mixed characters satisfies the cubic second moment
on a full ideal dyad. Only the explicit number of ramified parts is lost. -/
theorem normalized_angular_twisted_primitive_ideal_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (S : Finset EisensteinIdealExponent)
      (b : Eisenstein) (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
      (r : Eisenstein) (η : MulChar (Residues r) ℂ) (ℓ : ℤ) (N J u : ℝ),
      primary b → Squarefree b → r ≠ 0 →
      (AngularUnitCompatible r η ℓ) →
      1 ≤ N → 1 ≤ J →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∀ a ∈ P, IsCoprime (a*b) r) →
      (∀ a ∈ P, d a ≠ 0) →
      (∀ a ∈ P, AngularUnitCompatible (d a) (ψ a) ℓ) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) →
      (∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*J) →
      (∑ a ∈ P, ‖normalizedDualPolynomial S (angularResidueIdealChar (d a) (ψ a) ℓ)
        idealExponentNorm J u‖^2) ≤
        C*((supportedParts (3*r) S).card:ℝ)^2*(N*(2*J))^ε*(2*J)*
          (N+2*J+(N*(2*J))^(2/3:ℝ)) := by
  obtain ⟨C,hC,hcubic⟩ := normalized_primary_ideal_cubic_moment hε
  refine ⟨C,hC,?_⟩
  intro P S b d ψ r η ℓ N J u hb hsb hr hη hN hJ hP hsmall hd hu hagree hS
  let B : ℝ := C*(N*(2*J))^ε*(2*J)*(N+2*J+(N*(2*J))^(2/3:ℝ))
  let F (a : Eisenstein) (ρ : EisensteinIdealExponent) : ℂ :=
    (angularResidueIdealChar (d a) (ψ a) ℓ ρ*mellinPhase u (idealExponentNorm ρ))*
      normalizedDualPolynomial (outsideFiber (3*r) S ρ) (fun ν => primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν)
        idealExponentNorm (J/idealExponentNorm ρ) u
  have hrow (ρ : EisensteinIdealExponent) (hρ : ρ ∈ supportedParts (3*r) S) :
      (∑ a ∈ P, ‖F a ρ‖^2) ≤ B := by
    have hY : 1 ≤ (2*J)/idealExponentNorm ρ :=
      supportedPart_norm_le_upper (fun ν hν => (hS ν hν).2) hρ
    have hYJ : (2*J)/idealExponentNorm ρ ≤ 2*J :=
      div_le_self (by positivity) (idealExponentNorm_ge_one ρ)
    calc
      _ ≤ ∑ a ∈ P, ‖normalizedDualPolynomial (outsideFiber (3*r) S ρ)
          (fun ν => primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν) idealExponentNorm (J/idealExponentNorm ρ) u‖^2 := by
        apply Finset.sum_le_sum
        intro a ha
        apply pow_le_pow_left₀ (_root_.norm_nonneg _)
        dsimp only [F]
        rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _)
          (angularResidueIdealChar_norm_le_one (hd a ha) (ψ a) ℓ ρ)
      _ ≤ C*(N*((2*J)/idealExponentNorm ρ))^ε*((2*J)/idealExponentNorm ρ)*
          (N+(2*J)/idealExponentNorm ρ+(N*((2*J)/idealExponentNorm ρ))^(2/3:ℝ)) := by
        simpa only [mul_comm] using hcubic P (outsideFiber (3*r) S ρ) b (angularResidueIdealChar r η ℓ)
          N ((2*J)/idealExponentNorm ρ) (J/idealExponentNorm ρ) u hb
          (fun ν _ => angularResidueIdealChar_norm_le_one hr η ℓ ν) hN hY (div_pos (by positivity) (idealExponentNorm_pos ρ))
          (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1⟩)
          (fun ν hν => outsideFiber_norm hS hν)
      _ ≤ B := by
        dsimp [B]
        gcongr
  have hsplit (a : Eisenstein) (ha : a ∈ P) :
      normalizedDualPolynomial S (angularResidueIdealChar (d a) (ψ a) ℓ) idealExponentNorm J u =
        ∑ ρ ∈ supportedParts (3*r) S, F a ρ :=
    angularTwistedDualPolynomial_supported_partition (hP a ha).1 hb (hP a ha).2.1 hsb
      (hP a ha).2.2.2 hr (hsmall a ha) (ψ a) η ℓ (hu a ha) hη (hagree a ha) S J u
  calc
    _ = ∑ a ∈ P, ‖∑ ρ ∈ supportedParts (3*r) S, F a ρ‖^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsplit a ha]
    _ ≤ ((supportedParts (3*r) S).card:ℝ)*∑ ρ ∈ supportedParts (3*r) S, ∑ a ∈ P, ‖F a ρ‖^2 :=
      complex_mass_sum_sq_le (supportedParts (3*r) S) P F
    _ ≤ ((supportedParts (3*r) S).card:ℝ)*∑ _ρ ∈ supportedParts (3*r) S, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (Nat.cast_nonneg _)
    _ = _ := by simp [B]; ring

end CubicFirstMoment

end

end OAI
