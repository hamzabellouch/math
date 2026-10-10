import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootWeylMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootL2Algebra

namespace OAI

/-! Isometric opposite-root action on the actual cubic-scale completion. -/
noncomputable section
namespace CubicFirstMoment

local instance cubeRootWeyl_finiteGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeCubeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeCubeRootFiniteWeyl {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] cubicThetaPrimeCubeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeCubeRootWeylSection hp F.val,
    cubicThetaPrimeCubeRootWeylSection_memLp hp F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeCubeRootFiniteWeyl_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteWeyl hp F)‖=
      ‖cubicThetaPrimeCubeRootFiniteEmbedding hp F‖ := by
  change ‖cubicThetaPrimeCubeRootFiniteValue hp (cubicThetaPrimeCubeRootFiniteWeyl hp F)‖=
    ‖cubicThetaPrimeCubeRootFiniteValue hp F‖
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeCubeRootSectionL2_norm_sq,cubicThetaPrimeCubeRootSectionL2_norm_sq]
  exact cubicThetaPrimeCubeRootWeylSection_mass hp F.val

def cubicThetaPrimeCubeRootWeylL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  ((cubicThetaPrimeCubeRootFiniteEmbedding hp).comp (cubicThetaPrimeCubeRootFiniteWeyl hp)).extendOfIsometry
    (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp) (cubicThetaPrimeCubeRootFiniteWeyl_norm hp)

lemma cubicThetaPrimeCubeRootWeylL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteWeyl hp F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

theorem cubicThetaPrimeCubeRootWeylL2_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeCubeRootWeylL2 hp) := by
  intro u
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootWeylL2 hp).continuous.comp
      (cubicThetaPrimeCubeRootWeylL2 hp).continuous) continuous_id) ?_
  intro F
  rw [cubicThetaPrimeCubeRootWeylL2_finite,cubicThetaPrimeCubeRootWeylL2_finite]
  apply congrArg (cubicThetaPrimeCubeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootWeylSection_involutive hp F.val

end CubicFirstMoment

end

end OAI
