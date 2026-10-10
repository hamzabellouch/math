import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeC1Energy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalGradient

namespace OAI

/-! Actual gradient vectors for C1 sections on the finite prime cover.
Their norms are the intrinsic derivative energy already proved invariant. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaPrimeGradientL2 {p : Eisenstein} (hp : primaryPrime p) :=
  Lp CubicThetaGradient 2 (cubicThetaPrimeCoverMeasure hp)

lemma cubicThetaPrimeC1_differentiable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) {y : ℂ × ℝ} (hy : 0<y.2) :
    DifferentiableAt ℝ (cubicThetaPrimeSectionFunction hp F.val) y :=
  (F.property.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)).differentiableAt
    (by norm_num)

def cubicThetaPrimeSectionGradient {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (x : CubicThetaPoint) : CubicThetaGradient :=
  WithLp.toLp 2 (fun i => x.val.2 • cubicThetaPrimeSectionDifferential hp F.val x (cubicThetaTangentBasis i))

lemma cubicThetaPrimeSectionGradient_continuous {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) : Continuous (cubicThetaPrimeSectionGradient hp F) := by
  have hd : Continuous (fun x : CubicThetaPoint =>
      fderiv ℝ (cubicThetaPrimeSectionFunction hp F.val) x.val) :=
    (F.property.continuousOn_fderiv_of_isOpen (isOpen_lt continuous_const continuous_snd)
      (by norm_num)).comp_continuous continuous_subtype_val (fun x => x.property)
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact (continuous_snd.comp continuous_subtype_val).smul (hd.clm_apply continuous_const)

lemma cubicThetaPrimeSectionGradient_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (x : CubicThetaPoint) :
    ‖cubicThetaPrimeSectionGradient hp F x‖^2=cubicThetaPrimeSectionEnergy hp F.val x := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [cubicThetaPrimeSectionGradient,WithLp.ofLp_toLp,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs,cubicThetaPrimeSectionEnergy,cubicThetaFunctionEnergy,
    cubicThetaPrimeSectionDifferential,cubicThetaTangentEnergy,Finset.mul_sum]

def cubicThetaPrimeGradientRepresentative {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (q : CubicThetaPrimeCover hp) : CubicThetaGradient :=
  cubicThetaPrimeSectionGradient hp F (cubicThetaPrimeBorelSection hp q)

lemma cubicThetaPrimeGradientRepresentative_measurable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) : Measurable (cubicThetaPrimeGradientRepresentative hp F) :=
  (cubicThetaPrimeSectionGradient_continuous hp F).measurable.comp
    (cubicThetaPrimeBorelSection_measurable hp)

lemma cubicThetaPrimeGradientRepresentative_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (q : CubicThetaPrimeCover hp) :
    ‖cubicThetaPrimeGradientRepresentative hp F q‖^2=cubicThetaPrimeQuotientEnergy hp F q := by
  have he := cubicThetaPrimeQuotientEnergy_apply hp F (cubicThetaPrimeBorelSection hp q)
  rw [cubicThetaPrimeBorelSection_rightInverse hp q] at he
  exact (cubicThetaPrimeSectionGradient_norm_sq hp F _).trans he.symm

lemma cubicThetaPrimeGradientRepresentative_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (q : CubicThetaPrimeCover hp) :
    ‖cubicThetaPrimeGradientRepresentative hp F q‖=Real.sqrt (cubicThetaPrimeQuotientEnergy hp F q) := by
  rw [←cubicThetaPrimeGradientRepresentative_norm_sq hp F q,Real.sqrt_sq (_root_.norm_nonneg _)]

lemma cubicThetaPrimeAtkinGradient_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp)
    (hF : MemLp (cubicThetaPrimeGradientRepresentative hp F) 2 (cubicThetaPrimeCoverMeasure hp)) :
    MemLp (cubicThetaPrimeGradientRepresentative hp (cubicThetaPrimeC1Atkin hp F))
      2 (cubicThetaPrimeCoverMeasure hp) := by
  apply (memLp_norm_iff (cubicThetaPrimeGradientRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaPrimeGradientRepresentative_norm] at hn
  have hc := hn.comp_measurePreserving (cubicThetaPrimeCoverAtkin_measurePreserving hp)
  simpa only [Function.comp_def,cubicThetaPrimeGradientRepresentative_norm,cubicThetaPrimeC1Atkin_energy]
    using hc

lemma cubicThetaPrimeSectionGradient_add {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeC1Sections hp) (x : CubicThetaPoint) :
    cubicThetaPrimeSectionGradient hp (F+G) x=
      cubicThetaPrimeSectionGradient hp F x+cubicThetaPrimeSectionGradient hp G x := by
  ext i
  simp only [cubicThetaPrimeSectionGradient,cubicThetaPrimeSectionDifferential,
    show cubicThetaPrimeSectionFunction hp (F+G).val=
      cubicThetaPrimeSectionFunction hp F.val+cubicThetaPrimeSectionFunction hp G.val from rfl,
    fderiv_add (cubicThetaPrimeC1_differentiable hp F x.property)
      (cubicThetaPrimeC1_differentiable hp G x.property),
    ContinuousLinearMap.comp_apply,add_apply,smul_add]
  rfl

lemma cubicThetaPrimeSectionGradient_smul {p : Eisenstein} (hp : primaryPrime p)
    (c : ℂ) (F : cubicThetaPrimeC1Sections hp) (x : CubicThetaPoint) :
    cubicThetaPrimeSectionGradient hp (c • F) x=c • cubicThetaPrimeSectionGradient hp F x := by
  ext i
  simp only [cubicThetaPrimeSectionGradient,cubicThetaPrimeSectionDifferential,
    show cubicThetaPrimeSectionFunction hp (c • F).val=c • cubicThetaPrimeSectionFunction hp F.val from rfl,
    fderiv_const_smul (cubicThetaPrimeC1_differentiable hp F x.property) c,
    ContinuousLinearMap.comp_apply,smul_apply]
  exact smul_comm x.val.2 c (cubicThetaPrimeSectionDifferential hp F.val x (cubicThetaTangentBasis i))

end CubicFirstMoment

end

end OAI
