import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootTraceNormalized
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootFourierNorm

namespace OAI

/-! The once-cubic dilation is fixed by the cubic root translations.
The zero Fourier projection preserves its pairings exactly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootDilation_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeCubeRootSectionTranslate hp x
      (cubicThetaPrimeCubeRootHeckeRestriction hp (cubicThetaPrimeCubeDilationSection hp F))=
    cubicThetaPrimeCubeRootHeckeRestriction hp (cubicThetaPrimeCubeDilationSection hp F) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  have hm : D*cubicThetaPrimeCubeRootElement hp x=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*D := by
    dsimp only [D,cubicThetaPrimeCubeRootElement]
    group
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (D • (cubicThetaPrimeCubeRootElement hp x • y))=F.val (D • y)
  rw [←mul_smul,hm,mul_smul]
  change F.val (cubicThetaPrincipalTranslation x • (D • y))=_
  rw [F.property,cubicThetaPrincipalTranslation_value,one_mul]

lemma cubicThetaPrimeCubeRootFiniteDilation_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootFiniteTranslate hp x (cubicThetaPrimeCubeRootSmoothDilation hp F)=
      cubicThetaPrimeCubeRootSmoothDilation hp F := by
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootDilation_translate hp x F.val

theorem cubicThetaPrimeCubeRootDilationL2_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootDilationL2 hp u)=
      cubicThetaPrimeCubeRootDilationL2 hp u := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootTranslateL2 hp x).continuous.comp
      (cubicThetaPrimeCubeRootDilationL2 hp).continuous) (cubicThetaPrimeCubeRootDilationL2 hp).continuous) ?_
  intro F
  simp only [cubicThetaPrimeCubeRootDilationL2_smooth,cubicThetaPrimeCubeRootNormalizedDilation,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeCubeRootTranslateL2_finite,
    cubicThetaPrimeCubeRootFiniteDilation_translate]

theorem cubicThetaPrimeCubeRootDilationL2_fourier_zero {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeCubeRootFourierL2 hp 0 (cubicThetaPrimeCubeRootDilationL2 hp u)=
      cubicThetaPrimeCubeRootDilationL2 hp u := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  have hcard : (Fintype.card (Residues (p^3)):ℂ)=(norm (p^3):ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card (pow_ne_zero 3 hp.2.ne_zero)]
    simpa only [Complex.ofReal_natCast] using congrArg Complex.ofReal (normNat_cast (p^3))
  rw [cubicThetaPrimeCubeRootFourierL2_apply]
  simp only [zero_mul,AddChar.map_zero_eq_one,star_one,one_smul,
    cubicThetaPrimeCubeRootResidueL2,cubicThetaPrimeCubeRootDilationL2_translate,
    Finset.sum_const,Finset.card_univ]
  rw [←Nat.cast_smul_eq_nsmul ℂ,hcard,smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero)).ne'),one_smul]

theorem cubicThetaPrimeCubeRootDilationL2_average_pairing {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp 0 (cubicThetaPrimeCubeRootLiftL2 hp u))
      (cubicThetaPrimeCubeRootDilationL2 hp v)=
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u) (cubicThetaPrimeCubeRootDilationL2 hp v) := by
  have he := cubicThetaPrimeCubeRootFourierL2_pair_projection hp 0
    (cubicThetaPrimeCubeRootLiftL2 hp u) (cubicThetaPrimeCubeRootDilationL2 hp v)
  rwa [cubicThetaPrimeCubeRootDilationL2_fourier_zero] at he

end CubicFirstMoment

end

end OAI
