import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryIdealMoments

namespace OAI

/-! Cubic second moments for the actual primitive ideal characters.
The primes above three are separated exactly before applying the cubic sieve. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primitiveDualPolynomial_ramified_partition {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (ψ : MulChar (Residues d) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x)
    (S : Finset EisensteinIdealExponent) (J u : ℝ) :
    normalizedDualPolynomial S (residueIdealChar d ψ) idealExponentNorm J u =
      ∑ ρ ∈ ramifiedParts S,
        (residueIdealChar d ψ ρ*mellinPhase u (idealExponentNorm ρ))*
          normalizedDualPolynomial (unramifiedFiber S ρ) (primaryMixedIdealChar a b)
            idealExponentNorm (J/idealExponentNorm ρ) u := by
  rw [normalizedDualPolynomial_ramified_partition S _ (residueIdealChar_add d ψ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  unfold normalizedDualPolynomial
  apply Finset.sum_congr rfl
  intro ν hν
  rw [primitive_ideal_mixed_match ha hb hsa hsb hab ψ hu hagree ν
    (unramifiedFiber_primary hν)]

/-- A family of primitive mixed characters satisfies the cubic second moment
on a full ideal dyad. Only the explicit number of ramified parts is lost. -/
theorem normalized_primitive_ideal_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (S : Finset EisensteinIdealExponent)
      (b : Eisenstein) (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ) (N J u : ℝ),
      primary b → Squarefree b → 1 ≤ N → 1 ≤ J →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∀ a ∈ P, d a ≠ 0) →
      (∀ a ∈ P, ∀ v : Eisensteinˣ, ψ a (Ideal.Quotient.mk (modulus (d a)) v) = 1) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) = mixedCubic a b x) →
      (∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*J) →
      (∑ a ∈ P, ‖normalizedDualPolynomial S (residueIdealChar (d a) (ψ a))
        idealExponentNorm J u‖^2) ≤
        C*((ramifiedParts S).card:ℝ)^2*(N*(2*J))^ε*(2*J)*
          (N+2*J+(N*(2*J))^(2/3:ℝ)) := by
  obtain ⟨C,hC,hcubic⟩ := normalized_primary_ideal_cubic_moment hε
  refine ⟨C,hC,?_⟩
  intro P S b d ψ N J u hb hsb hN hJ hP hd hu hagree hS
  let B : ℝ := C*(N*(2*J))^ε*(2*J)*(N+2*J+(N*(2*J))^(2/3:ℝ))
  let F (a : Eisenstein) (ρ : EisensteinIdealExponent) : ℂ :=
    (residueIdealChar (d a) (ψ a) ρ*mellinPhase u (idealExponentNorm ρ))*
      normalizedDualPolynomial (unramifiedFiber S ρ) (primaryMixedIdealChar a b)
        idealExponentNorm (J/idealExponentNorm ρ) u
  have hrow (ρ : EisensteinIdealExponent) (hρ : ρ ∈ ramifiedParts S) :
      (∑ a ∈ P, ‖F a ρ‖^2) ≤ B := by
    have hY : 1 ≤ (2*J)/idealExponentNorm ρ :=
      ramifiedPart_norm_le_upper (fun ν hν => (hS ν hν).2) hρ
    have hYJ : (2*J)/idealExponentNorm ρ ≤ 2*J :=
      div_le_self (by positivity) (idealExponentNorm_ge_one ρ)
    calc
      _ ≤ ∑ a ∈ P, ‖normalizedDualPolynomial (unramifiedFiber S ρ)
          (primaryMixedIdealChar a b) idealExponentNorm (J/idealExponentNorm ρ) u‖^2 := by
        apply Finset.sum_le_sum
        intro a ha
        apply pow_le_pow_left₀ (_root_.norm_nonneg _)
        dsimp only [F]
        rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _)
          (residueIdealChar_norm_le_one (hd a ha) (ψ a) ρ)
      _ ≤ C*(N*((2*J)/idealExponentNorm ρ))^ε*((2*J)/idealExponentNorm ρ)*
          (N+(2*J)/idealExponentNorm ρ+(N*((2*J)/idealExponentNorm ρ))^(2/3:ℝ)) := by
        simpa only [one_mul] using hcubic P (unramifiedFiber S ρ) b (fun _ => 1)
          N ((2*J)/idealExponentNorm ρ) (J/idealExponentNorm ρ) u hb
          (by intros; simp) hN hY (div_pos (by positivity) (idealExponentNorm_pos ρ))
          (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1⟩)
          (fun ν hν => unramifiedFiber_norm hS hν)
      _ ≤ B := by
        dsimp [B]
        gcongr
  have hsplit (a : Eisenstein) (ha : a ∈ P) :
      normalizedDualPolynomial S (residueIdealChar (d a) (ψ a)) idealExponentNorm J u =
        ∑ ρ ∈ ramifiedParts S, F a ρ :=
    primitiveDualPolynomial_ramified_partition (hP a ha).1 hb (hP a ha).2.1 hsb
      (hP a ha).2.2.2 (ψ a) (hu a ha) (hagree a ha) S J u
  calc
    _ = ∑ a ∈ P, ‖∑ ρ ∈ ramifiedParts S, F a ρ‖^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsplit a ha]
    _ ≤ ((ramifiedParts S).card:ℝ)*∑ ρ ∈ ramifiedParts S, ∑ a ∈ P, ‖F a ρ‖^2 :=
      complex_mass_sum_sq_le (ramifiedParts S) P F
    _ ≤ ((ramifiedParts S).card:ℝ)*∑ _ρ ∈ ramifiedParts S, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (Nat.cast_nonneg _)
    _ = _ := by simp [B]; ring

end CubicFirstMoment

end

end OAI
