import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootTracePairing

namespace OAI

/-! The exact normalized trace pairing. No Hecke eigenvalue or local
coefficient relation is postulated in constructing this identity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootTrace_scalar {p : Eisenstein} (hp : primaryPrime p) :
    star (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)):ℂ)⁻¹)*
      (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)):ℂ)⁻¹)*
        ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℂ)=
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹ := by
  let k : ℝ := (cubicThetaPrimeCubeRootCoverGroup hp).index
  let r : ℝ := (cubicThetaPrimeCubeRootHeckeSubgroup hp).index
  let d : ℝ := (cubicThetaPrimeIwahori (p^3)).index
  have hk : 0<k := cubicThetaPrimeCubeRootCoverDegree_pos hp
  have hd : d≠0 := by
    exact Nat.cast_ne_zero.mpr (cubicThetaPrimeCubeIwahori_finiteIndex hp).index_ne_zero
  have hrd : (r:ℂ)*(d:ℂ)=(k:ℂ) := by
    change ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℂ)*
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)=((cubicThetaPrimeCubeRootCoverGroup hp).index:ℂ)
    rw [←Nat.cast_mul,cubicThetaPrimeCubeRootHecke_index hp]
  have hs : star ((Real.sqrt k:ℂ)⁻¹)*(Real.sqrt k:ℂ)⁻¹=(k:ℂ)⁻¹ := by
    rw [star_inv₀,Complex.star_def,Complex.conj_ofReal,←mul_inv_rev,←pow_two,
      ←Complex.ofReal_pow,Real.sq_sqrt hk.le]
  change star ((Real.sqrt k:ℂ)⁻¹)*(Real.sqrt k:ℂ)⁻¹*(r:ℂ)=(d:ℂ)⁻¹
  rw [hs]
  apply mul_left_cancel₀ (show (d:ℂ)≠0 from Complex.ofReal_ne_zero.mpr hd)
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hd)]
  calc
    _ = (k:ℂ)⁻¹*((r:ℂ)*(d:ℂ)) := by ring
    _ = 1 := by rw [hrd,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hk.ne')]

lemma cubicThetaPrimeCubeRootTrace_normalized_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaSmoothTests) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalMassClosure F))
      (cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalMassClosure G))=
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹*
        inner ℂ (cubicThetaGlobalMassClosure F)
          (cubicThetaPrimeCubeHeckeMass hp (cubicThetaGlobalMassClosure G)) := by
  rw [cubicThetaPrimeCubeRootLiftL2_smooth,cubicThetaPrimeCubeRootDilationL2_smooth]
  simp only [cubicThetaPrimeCubeRootNormalizedRestriction,cubicThetaPrimeCubeRootNormalizedDilation,
    LinearMap.smul_apply,LinearMap.comp_apply]
  rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),
    inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),starRingEnd_apply,
    cubicThetaPrimeCubeRootTrace_finite]
  change star (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)):ℂ)⁻¹)*
    ((((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)):ℂ)⁻¹)*
      (((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℂ)*
        inner ℂ (cubicThetaGlobalMassClosure F)
          (cubicThetaPrimeCubeHeckeMass hp (cubicThetaGlobalMassClosure G))))=_
  rw [←mul_assoc,←mul_assoc,cubicThetaPrimeCubeRootTrace_scalar]

theorem cubicThetaPrimeCubeRootTrace_normalized {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u) (cubicThetaPrimeCubeRootDilationL2 hp v)=
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹*
        inner ℂ u (cubicThetaPrimeCubeHeckeMass hp v) := by
  apply cubicThetaGlobalMassClosure_dense.induction_on₂
    (p:=fun u v => inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u) (cubicThetaPrimeCubeRootDilationL2 hp v)=
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹*inner ℂ u (cubicThetaPrimeCubeHeckeMass hp v)) ?_ ?_ u v
  · apply isClosed_eq
    · exact ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp continuous_fst).inner
        ((cubicThetaPrimeCubeRootDilationL2 hp).continuous.comp continuous_snd)
    · exact continuous_const.mul (continuous_fst.inner
        ((cubicThetaPrimeCubeHeckeMass hp).continuous.comp continuous_snd))
  · exact cubicThetaPrimeCubeRootTrace_normalized_smooth hp

end CubicFirstMoment

end

end OAI
