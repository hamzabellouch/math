import OAI.NumberTheory.CubicMoment.Angular.AngularNumeratorCharacter
import OAI.NumberTheory.CubicMoment.Estimates.PublishedAngularKummerPrime

namespace OAI

/-! Primitive reduction for the literal angular numerator character,
with the original `9*v` modulus and its exact analytic conductor bound. -/
noncomputable section
namespace CubicFirstMoment

theorem angularNumerator_primitive_conductor (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : v ≠ 0) (ℓ : ℤ) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ d ∣ 9*v ∧
      normNat d ≤ normNat (9*v) ∧ AngularUnitCompatible d ψ ℓ ∧
      ResidueCharacterInduces (9*v) d (angularNumeratorChar hpub v hv ℓ) ψ ∧
      (∀ x : Eisenstein, primary x → IsCoprime v x →
        ψ (Ideal.Quotient.mk (modulus d) x)=cubicSymbol x v) := by
  have hq : 9*v ≠ (0:Eisenstein) := mul_ne_zero (by norm_num) hv
  obtain ⟨d,ψ,hd,hi,hN,hp⟩ := primitive_residue_conductor_exists hq
    (angularNumeratorChar hpub v hv ℓ)
  refine ⟨d,ψ,hd,hp,hi.1,hN,
    hi.angular_units (angularNumeratorChar_compatible hpub v hv ℓ),hi,?_⟩
  intro x hx hcop
  have h9x : IsCoprime (9:Eisenstein) x := by
    convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
    norm_num
  exact (hi.2 x (h9x.mul_left hcop)).trans (angularNumeratorChar_primary hpub v hv ℓ hx)

lemma angularNumerator_conductor_bound {v d : Eisenstein} (ℓ : ℤ)
    (hN : normNat d ≤ normNat (9*v)) :
    3*norm d*(|(ℓ:ℝ)|/2+3)*(|(ℓ:ℝ)|/2+4) ≤ angularKummerAnalyticConductor ℓ v := by
  have h9 : norm (9:Eisenstein)=81 := by change Complex.normSq (9:ℂ)=81; norm_num
  have hd : norm d ≤ 81*norm v := by
    have h := (Nat.cast_le.mpr hN : (normNat d:ℝ) ≤ (normNat (9*v):ℝ))
    simpa only [normNat_cast,norm_mul_eq,h9] using h
  unfold angularKummerAnalyticConductor angularKummerConductorFactor angularConductorFactor
  have hf : 0 ≤ 3*(|(ℓ:ℝ)|/2+3)*(|(ℓ:ℝ)|/2+4) := by positivity
  calc
    _ = norm d*(3*(|(ℓ:ℝ)|/2+3)*(|(ℓ:ℝ)|/2+4)) := by ring
    _ ≤ (81*norm v)*(3*(|(ℓ:ℝ)|/2+3)*(|(ℓ:ℝ)|/2+4)) :=
      mul_le_mul_of_nonneg_right hd hf
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
