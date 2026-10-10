import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootAutomorphicL2

namespace OAI

/-! Fractional translations extend isometrically to the actual completed
space of root-cover sections. -/
noncomputable section
namespace CubicFirstMoment

local instance rootTranslation_finiteGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

lemma cubicThetaPrimeRootResidueSection_memLp {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaPrimeRootSections p)
    (hF : MeasureTheory.MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2
      (cubicThetaPrimeRootCoverMeasure hp)) :
    MeasureTheory.MemLp (cubicThetaPrimeRootSectionRepresentative hp
      (cubicThetaPrimeRootResidueOperator hp r F)) 2 (cubicThetaPrimeRootCoverMeasure hp) := by
  change MeasureTheory.MemLp (cubicThetaPrimeRootSectionRepresentative hp
    (cubicThetaPrimeRootSectionTranslate hp (residueRepresentative p r) F)) 2 _
  apply (MeasureTheory.memLp_norm_iff
    (cubicThetaPrimeRootSectionRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaPrimeRootSectionRepresentative_norm] at hn
  have hc := hn.comp_measurePreserving
    (cubicThetaPrimeRootCoverTranslate_measurePreserving hp (residueRepresentative p r))
  simpa only [Function.comp_def,cubicThetaPrimeRootSectionRepresentative_norm,
    cubicThetaPrimeRootSectionTranslate_norm] using hc

def cubicThetaPrimeRootFiniteResidue {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) : cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ]
      cubicThetaPrimeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeRootResidueOperator hp r F.val,
    cubicThetaPrimeRootResidueSection_memLp hp r F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeRootFiniteResidue_norm {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaPrimeRootFiniteSections hp) :
    ‖cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootFiniteResidue hp r F)‖=
      ‖cubicThetaPrimeRootFiniteEmbedding hp F‖ := by
  change ‖cubicThetaPrimeRootFiniteValue hp (cubicThetaPrimeRootFiniteResidue hp r F)‖=
    ‖cubicThetaPrimeRootFiniteValue hp F‖
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  have hf : MeasureTheory.MemLp (cubicThetaPrimeRootSectionRepresentative hp F.val) 2
      (cubicThetaPrimeRootCoverMeasure hp) := F.property
  change ‖(cubicThetaPrimeRootResidueSection_memLp hp r F.val hf).toLp _‖^2=‖hf.toLp _‖^2
  calc
    _ = ∫ q, (cubicThetaPrimeRootSectionNorm hp
        (cubicThetaPrimeRootResidueOperator hp r F.val) q)^2
        ∂cubicThetaPrimeRootCoverMeasure hp :=
      cubicThetaPrimeRootSectionL2_norm_sq hp _ (cubicThetaPrimeRootResidueSection_memLp hp r F.val hf)
    _ = ∫ q, (cubicThetaPrimeRootSectionNorm hp F.val q)^2
        ∂cubicThetaPrimeRootCoverMeasure hp :=
      cubicThetaPrimeRootSectionTranslate_mass hp (residueRepresentative p r) F.val
    _ = _ := (cubicThetaPrimeRootSectionL2_norm_sq hp F.val hf).symm

def cubicThetaPrimeRootResidueL2 {p : Eisenstein} (hp : primaryPrime p) (r : Residues p) :
    cubicThetaPrimeRootAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  ((cubicThetaPrimeRootFiniteEmbedding hp).comp (cubicThetaPrimeRootFiniteResidue hp r)).extendOfIsometry
    (cubicThetaPrimeRootFiniteEmbedding_dense hp) (cubicThetaPrimeRootFiniteResidue_norm hp r)

lemma cubicThetaPrimeRootResidueL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaPrimeRootFiniteSections hp) :
    cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootFiniteEmbedding hp F)=
      cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootFiniteResidue hp r F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
