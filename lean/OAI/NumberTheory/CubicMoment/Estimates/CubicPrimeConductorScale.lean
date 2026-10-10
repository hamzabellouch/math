import OAI.NumberTheory.CubicMoment.Estimates.PublishedPrimitiveHecke
import OAI.NumberTheory.CubicMoment.Estimates.KummerPrimitiveConductor

namespace OAI

/-! Elementary conductor scales for the arbitrary nonzero cubic numerator. -/
noncomputable section
namespace CubicFirstMoment

lemma residueHeckeScale_le_norm {q : Eisenstein} (hq : q ≠ 0) :
    residueHeckeScale q ≤ norm q := by
  have hN := one_le_norm hq
  have hs : Real.sqrt (3*norm q) ≤ 2*norm q := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  unfold residueHeckeScale
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)).mpr
  nlinarith [Real.pi_gt_three]

lemma cubicNumerator_modulus_norm (v : Eisenstein) : norm (9*v)=81*norm v := by
  rw [norm_mul_eq]
  have h9 : norm (9:Eisenstein)=81 := by change Complex.normSq (9:ℂ)=81; norm_num
  rw [h9]

lemma cubicNumerator_primitive_scale {v d : Eisenstein} (hv : v ≠ 0) (hd : d ≠ 0)
    (hN : normNat d ≤ normNat (9*v)) :
    1 ≤ 810*norm v ∧ residueHeckeScale d ≤ 810*norm v ∧ 7 ≤ 810*norm v ∧
      norm (9*v) ≤ 810*norm v := by
  have hv1 := one_le_norm hv
  have hdN : norm d ≤ 81*norm v := by
    have hh : (normNat d:ℝ) ≤ (normNat (9*v):ℝ) := Nat.cast_le.mpr hN
    simpa only [normNat_cast,cubicNumerator_modulus_norm] using hh
  have hs := (residueHeckeScale_le_norm hd).trans hdN
  rw [cubicNumerator_modulus_norm]
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end CubicFirstMoment

end

end OAI
