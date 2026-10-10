import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootStripBound

namespace OAI

/-! Bounded restriction from the actual completed cubic-root automorphic
space to the high cusp strip. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

local instance cubeRootCuspFinite_addCommGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeCubeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeCubeRootFiniteCuspRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] CubicThetaStripL2 where
  toFun F := (cubicThetaPrimeCubeRoot_strip_memLp hp F).toLp _
  map_add' F G := MemLp.toLp_add (cubicThetaPrimeCubeRoot_strip_memLp hp F)
    (cubicThetaPrimeCubeRoot_strip_memLp hp G)
  map_smul' c F := MemLp.toLp_const_smul c (cubicThetaPrimeCubeRoot_strip_memLp hp F)

lemma cubicThetaPrimeCubeRootFiniteCuspRestriction_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteCuspRestriction hp F‖^2=
      ∫ x in cubicThetaCuspStrip 2,‖F.val.val x‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaPrimeCubeRoot_strip_memLp hp F).coeFn_toLp] with x hx
  change ‖((cubicThetaPrimeCubeRoot_strip_memLp hp F).toLp _) x‖^2=_
  rw [hx]

lemma cubicThetaPrimeCubeRootFiniteCuspRestriction_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteCuspRestriction hp F‖≤
      ‖cubicThetaPrimeCubeRootFiniteEmbedding hp F‖ := by
  have hf := (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mp F.property
  have hi := cubicThetaPrimeCubeRoot_strip_lintegral_le hp F.val
  simp_rw [Real.enorm_eq_ofReal (sq_nonneg _)] at hi
  have hfin : (∫⁻ x in cubicThetaPrimeCubeRootCoverDomain hp,
      ENNReal.ofReal (‖F.val.val x‖^2) ∂cubicThetaPointMeasure)≠⊤ := by
    simpa only [hasFiniteIntegral_iff_enorm,Real.enorm_eq_ofReal (sq_nonneg _)] using hf.hasFiniteIntegral.ne
  have hr := ENNReal.toReal_mono hfin hi
  rw [←integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (F.val.val.continuous.norm.pow 2).aestronglyMeasurable,
    ←integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (F.val.val.continuous.norm.pow 2).aestronglyMeasurable] at hr
  rw [←cubicThetaPrimeCubeRootFiniteCuspRestriction_norm_sq,
    ←cubicThetaPrimeCubeRootSectionL2_norm_sq] at hr
  change ‖cubicThetaPrimeCubeRootFiniteCuspRestriction hp F‖^2≤
    ‖cubicThetaPrimeCubeRootFiniteEmbedding hp F‖^2 at hr
  nlinarith [_root_.norm_nonneg (cubicThetaPrimeCubeRootFiniteCuspRestriction hp F),
    _root_.norm_nonneg (cubicThetaPrimeCubeRootFiniteEmbedding hp F)]

def cubicThetaPrimeCubeRootCuspRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootAutomorphicL2 hp →L[ℂ] CubicThetaStripL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=cubicThetaPrimeCubeRootFiniteSections hp)
    (Eₗ:=cubicThetaPrimeCubeRootAutomorphicL2 hp) (F:=CubicThetaStripL2)
    (cubicThetaPrimeCubeRootFiniteCuspRestriction hp) (cubicThetaPrimeCubeRootFiniteEmbedding hp)

lemma cubicThetaPrimeCubeRootCuspRestriction_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootCuspRestriction hp (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      cubicThetaPrimeCubeRootFiniteCuspRestriction hp F := by
  apply LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaPrimeCubeRootFiniteCuspRestriction hp) (e:=cubicThetaPrimeCubeRootFiniteEmbedding hp)
    (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp)
  exact ⟨1,fun G => by simpa only [one_mul] using cubicThetaPrimeCubeRootFiniteCuspRestriction_bound hp G⟩

end CubicFirstMoment

end

end OAI
