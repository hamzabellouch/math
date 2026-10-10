import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimePairingL2

namespace OAI

/-! The actual original automorphic L2 space and its prime Atkin
translate are orthogonal inside the common finite cover. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeNormalizedAtkin_orthogonal {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaSmoothTests) :
    inner ℂ (cubicThetaPrimeNormalizedRestriction hp F)
      (cubicThetaPrimeAtkinL2 hp (cubicThetaPrimeNormalizedRestriction hp G))=0 := by
  simp only [cubicThetaPrimeNormalizedRestriction,LinearMap.smul_apply,LinearMap.comp_apply]
  rw [map_smul,inner_smul_left,
    inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeAutomorphicL2 hp),
    cubicThetaPrimeSmoothAtkin_orthogonal,mul_zero,mul_zero]

theorem cubicThetaPrimeLiftAtkin_orthogonal {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeLiftL2 hp u)
      (cubicThetaPrimeAtkinL2 hp (cubicThetaPrimeLiftL2 hp v))=0 := by
  apply cubicThetaGlobalMassClosure_dense.induction_on₂
    (p:=fun u v => inner ℂ (cubicThetaPrimeLiftL2 hp u)
      (cubicThetaPrimeAtkinL2 hp (cubicThetaPrimeLiftL2 hp v))=0) ?_ ?_ u v
  · apply isClosed_eq _ continuous_const
    exact ((cubicThetaPrimeLiftL2 hp).continuous.comp continuous_fst).inner
      ((cubicThetaPrimeAtkinL2 hp).continuous.comp
        ((cubicThetaPrimeLiftL2 hp).continuous.comp continuous_snd))
  · intro F G
    rw [cubicThetaPrimeLiftL2_smooth,cubicThetaPrimeLiftL2_smooth]
    exact cubicThetaPrimeNormalizedAtkin_orthogonal hp F G

end CubicFirstMoment

end

end OAI
