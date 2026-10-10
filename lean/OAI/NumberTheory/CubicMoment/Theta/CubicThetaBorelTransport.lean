import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalL2

namespace OAI

/-! Measurable transport of the quotient's chosen representatives back
upstairs, with the actual cubic character. No smooth representative is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaBorelSheet (g : cubicThetaPrincipalGroup) : Set CubicThetaPoint :=
  {p | g • cubicThetaBorelSection (cubicThetaQuotientMap p)=p}

lemma cubicThetaBorelSheet_measurable (g : cubicThetaPrincipalGroup) :
    MeasurableSet (cubicThetaBorelSheet g) :=
  measurableSet_eq_fun ((measurable_const_smul g).comp
    (cubicThetaBorelSection_measurable.comp cubicThetaQuotientMap_open.continuous.measurable))
    measurable_id

lemma cubicThetaBorelSheet_cover (p : CubicThetaPoint) :
    ∃ g : cubicThetaPrincipalGroup,p∈cubicThetaBorelSheet g := by
  have hq : cubicThetaQuotientMap p=
      cubicThetaQuotientMap (cubicThetaBorelSection (cubicThetaQuotientMap p)) := by
    rw [cubicThetaBorelSection_rightInverse]
  exact cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp hq

lemma cubicThetaBorelSheet_disjoint {g h : cubicThetaPrincipalGroup} (hne : g≠h) :
    Disjoint (cubicThetaBorelSheet g) (cubicThetaBorelSheet h) := by
  apply Set.disjoint_left.mpr
  intro p hg hh
  exact hne (IsCancelSMul.right_cancel g h _ (hg.trans hh.symm))

lemma cubicThetaBorelPhase_exists :
    ∃ b : CubicThetaPoint → ℂ,Measurable b ∧
      ∀ g,EqOn b (fun _ => cubicThetaKubotaValue g) (cubicThetaBorelSheet g) := by
  apply exists_measurable_piecewise cubicThetaBorelSheet cubicThetaBorelSheet_measurable
    (fun g _ => cubicThetaKubotaValue g) (fun _ => measurable_const)
  intro g h hne p hp
  exact False.elim (Set.disjoint_left.mp (cubicThetaBorelSheet_disjoint hne) hp.1 hp.2)

def cubicThetaBorelPhase : CubicThetaPoint → ℂ :=
  Classical.choose cubicThetaBorelPhase_exists

lemma cubicThetaBorelPhase_measurable : Measurable cubicThetaBorelPhase :=
  (Classical.choose_spec cubicThetaBorelPhase_exists).1

lemma cubicThetaBorelPhase_sheet (g : cubicThetaPrincipalGroup) {p : CubicThetaPoint}
    (hp : p∈cubicThetaBorelSheet g) : cubicThetaBorelPhase p=cubicThetaKubotaValue g :=
  (Classical.choose_spec cubicThetaBorelPhase_exists).2 g hp

lemma cubicThetaBorelPhase_norm (p : CubicThetaPoint) : ‖cubicThetaBorelPhase p‖=1 := by
  obtain ⟨g,hg⟩ := cubicThetaBorelSheet_cover p
  rw [cubicThetaBorelPhase_sheet g hg,cubicThetaKubotaValue_norm]

lemma cubicThetaBorelPhase_smul (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaBorelPhase (g • p)=cubicThetaKubotaValue g*cubicThetaBorelPhase p := by
  obtain ⟨h,hh⟩ := cubicThetaBorelSheet_cover p
  have hgh : g • p∈cubicThetaBorelSheet (g*h) := by
    change (g*h) • cubicThetaBorelSection (cubicThetaQuotientMap (g • p))=g • p
    rw [cubicThetaQuotient_covering.map_smul,mul_smul,hh]
  rw [cubicThetaBorelPhase_sheet (g*h) hgh,cubicThetaBorelPhase_sheet h hh,
    cubicThetaKubotaValue_mul]

def cubicThetaBorelLift (f : CubicThetaQuotient → ℂ) (p : CubicThetaPoint) : ℂ :=
  cubicThetaBorelPhase p*f (cubicThetaQuotientMap p)

lemma cubicThetaBorelLift_measurable {f : CubicThetaQuotient → ℂ} (hf : Measurable f) :
    Measurable (cubicThetaBorelLift f) :=
  cubicThetaBorelPhase_measurable.mul (hf.comp cubicThetaQuotientMap_open.continuous.measurable)

lemma cubicThetaBorelLift_norm (f : CubicThetaQuotient → ℂ) (p : CubicThetaPoint) :
    ‖cubicThetaBorelLift f p‖=‖f (cubicThetaQuotientMap p)‖ := by
  rw [cubicThetaBorelLift,norm_mul,cubicThetaBorelPhase_norm,one_mul]

theorem cubicThetaBorelLift_automorphy (f : CubicThetaQuotient → ℂ)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaBorelLift f (g • p)=cubicThetaKubotaValue g*cubicThetaBorelLift f p := by
  rw [cubicThetaBorelLift,cubicThetaBorelLift,cubicThetaBorelPhase_smul,
    cubicThetaQuotient_covering.map_smul,mul_assoc]

lemma cubicThetaBorelLift_section (F : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaBorelLift (cubicThetaSectionRepresentative F) p=F.val p := by
  obtain ⟨g,hg⟩ := cubicThetaBorelSheet_cover p
  rw [cubicThetaBorelLift,cubicThetaBorelPhase_sheet g hg,cubicThetaSectionRepresentative,
    ←F.property g]
  exact congrArg F.val hg

lemma cubicThetaBorelLift_positive_memLp {ε : ℝ} (hε : 0<ε)
    {f : CubicThetaQuotient → ℂ} (hm : Measurable f) (hf : MemLp f 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaBorelLift f) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  obtain ⟨N,_,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  have hi := (hf.integrable_norm_pow (by norm_num)).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hc := (hi.mono_measure hN).comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaBorelLift_measurable hm).aestronglyMeasurable).mpr
  simpa only [Function.comp_def,cubicThetaBorelLift_norm] using hc

end CubicFirstMoment

end

end OAI
