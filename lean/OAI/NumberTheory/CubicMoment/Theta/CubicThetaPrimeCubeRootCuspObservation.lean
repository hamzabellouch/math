import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCuspRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootHorizontal
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierIntegral

namespace OAI

/-! Weighted cusp observations of finite cubic-root sections, evaluated
by absolutely convergent Fubini integrals. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootFunction {p : Eisenstein} (F : cubicThetaPrimeCubeRootSections p)
    (y : ℂ × ℝ) : ℂ := F.val (cubicThetaPointInclusion.symm y)

lemma cubicThetaPrimeCubeRootFunction_coordinates {p : Eisenstein}
    (F : cubicThetaPrimeCubeRootSections p) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeRootFunction F x.val=F.val x := by
  exact congrArg F.val (cubicThetaPointInclusion.left_inv (by
    rw [cubicThetaPointInclusion_source]; trivial))

lemma cubicThetaPrimeCubeRootFunction_apply {p : Eisenstein}
    (F : cubicThetaPrimeCubeRootSections p) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPrimeCubeRootFunction F y=F.val ⟨y,hy⟩ := by
  apply congrArg F.val
  apply Subtype.ext
  exact cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target])

def cubicThetaPrimeCubeRootObservation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) : cubicThetaPrimeCubeRootAutomorphicL2 hp →L[ℂ] ℂ :=
  (innerSL ℂ (cubicThetaCuspFourierTest h W)).comp (cubicThetaPrimeCubeRootCuspRestriction hp)

lemma cubicThetaPrimeCubeRootFinite_observation_integral {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootObservation hp h W (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      ∫ x in cubicThetaCuspStrip 2,star (W x.val.2*cubicThetaHorizontalCharacter h x.val.1)*
        F.val.val x ∂cubicThetaPointMeasure := by
  change inner ℂ (cubicThetaCuspFourierTest h W)
    (cubicThetaPrimeCubeRootCuspRestriction hp (cubicThetaPrimeCubeRootFiniteEmbedding hp F))=_
  rw [cubicThetaPrimeCubeRootCuspRestriction_finite,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    (cubicThetaPrimeCubeRoot_strip_memLp hp F).coeFn_toLp] with x hx hF
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) x)
    (((cubicThetaPrimeCubeRoot_strip_memLp hp F).toLp _) x)=_
  rw [hx,hF,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter]
  ring

lemma cubicThetaPrimeCubeRootFinite_observation_iterated {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootObservation hp h W (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
        cubicThetaHorizontalFourierCoefficient h (fun z => cubicThetaPrimeCubeRootFunction F.val (z,v)) := by
  have hi : IntegrableOn (fun x : CubicThetaPoint =>
      star (W x.val.2*cubicThetaHorizontalCharacter h x.val.1)*F.val.val x)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    have he := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W)
      (cubicThetaPrimeCubeRootFiniteCuspRestriction hp F)
    apply he.congr
    filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
      (cubicThetaPrimeCubeRoot_strip_memLp hp F).coeFn_toLp] with x hx hF
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) x)
      (((cubicThetaPrimeCubeRoot_strip_memLp hp F).toLp _) x)=_
    rw [hx,hF,RCLike.inner_apply]
    simp only [starRingEnd_apply,cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter]
    ring
  have hi' : IntegrableOn (fun x : CubicThetaPoint =>
      star (W x.val.2*cubicThetaHorizontalCharacter h x.val.1)*
        cubicThetaPrimeCubeRootFunction F.val x.val) (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    simpa only [cubicThetaPrimeCubeRootFunction_coordinates] using hi
  rw [cubicThetaPrimeCubeRootFinite_observation_integral]
  have he := cubicThetaCuspStrip_fubini (fun y =>
    star (W y.2*cubicThetaHorizontalCharacter h y.1)*cubicThetaPrimeCubeRootFunction F.val y) hi'
  simp only [cubicThetaPointCoordinates,cubicThetaPrimeCubeRootFunction_coordinates] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  unfold cubicThetaHorizontalFourierCoefficient
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
