import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientEnergy

namespace OAI

/-! An actual L2 gradient vector, obtained by evaluating the differential
in an orthonormal frame at the measurable representative. Its norm is
intrinsic even though its coordinates use that representative. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaTangentIndex := Fin (Module.finrank ℝ CubicThetaTangent)
abbrev CubicThetaGradient := EuclideanSpace ℂ CubicThetaTangentIndex
abbrev CubicThetaGradientL2 := Lp CubicThetaGradient 2 cubicThetaQuotientMeasure

def cubicThetaSectionGradient (F : CubicThetaSection) (p : CubicThetaPoint) : CubicThetaGradient :=
  WithLp.toLp 2 (fun i => p.val.2 • cubicThetaSectionDifferential F p (cubicThetaTangentBasis i))

lemma cubicThetaSectionGradient_continuous (F : cubicThetaSmoothTests) :
    Continuous (cubicThetaSectionGradient F) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction F) p.val) :=
    (F.property.1.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by simp)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact (continuous_snd.comp continuous_subtype_val).smul (hd.clm_apply continuous_const)

lemma cubicThetaSectionGradient_norm_sq (F : CubicThetaSection) (p : CubicThetaPoint) :
    ‖cubicThetaSectionGradient F p‖^2=cubicThetaSectionEnergy F p := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [cubicThetaSectionGradient,WithLp.ofLp_toLp,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs,cubicThetaSectionEnergy,cubicThetaTangentEnergy,Finset.mul_sum]

def cubicThetaGradientRepresentative (F : CubicThetaSection) (q : CubicThetaQuotient) :
    CubicThetaGradient := cubicThetaSectionGradient F (cubicThetaBorelSection q)

lemma cubicThetaGradientRepresentative_measurable (F : cubicThetaSmoothTests) :
    Measurable (cubicThetaGradientRepresentative F) :=
  (cubicThetaSectionGradient_continuous F).measurable.comp cubicThetaBorelSection_measurable

lemma cubicThetaGradientRepresentative_norm (F : cubicThetaSmoothTests) (q : CubicThetaQuotient) :
    ‖cubicThetaGradientRepresentative F q‖=cubicThetaQuotientGradientNorm F q := by
  have he := cubicThetaQuotientEnergy_apply F (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse] at he
  unfold cubicThetaQuotientGradientNorm
  rw [he,← cubicThetaSectionGradient_norm_sq,Real.sqrt_sq (_root_.norm_nonneg _)]
  rfl

lemma cubicThetaGradientRepresentative_memLp (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure := by
  apply (memLp_norm_iff (cubicThetaGradientRepresentative_measurable F).aestronglyMeasurable).mp
  simpa only [cubicThetaGradientRepresentative_norm] using cubicThetaQuotientGradientNorm_memLp F

lemma cubicThetaSectionFunction_add (F G : cubicThetaSmoothTests) :
    cubicThetaSectionFunction ((F+G : cubicThetaSmoothTests) : CubicThetaSection)=
      cubicThetaSectionFunction F+cubicThetaSectionFunction G := rfl

lemma cubicThetaSectionFunction_smul (c : ℂ) (F : cubicThetaSmoothTests) :
    cubicThetaSectionFunction ((c • F : cubicThetaSmoothTests) : CubicThetaSection)=
      c • cubicThetaSectionFunction F := rfl

lemma cubicThetaSectionGradient_add (F G : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaSectionGradient ((F+G : cubicThetaSmoothTests) : CubicThetaSection) p=
      cubicThetaSectionGradient F p+cubicThetaSectionGradient G p := by
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,
    cubicThetaSectionFunction_add,fderiv_add (cubicThetaSectionFunction_differentiable F p.property)
      (cubicThetaSectionFunction_differentiable G p.property),
    ContinuousLinearMap.comp_apply,add_apply,smul_add]
  rfl

lemma cubicThetaSectionGradient_smul (c : ℂ) (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaSectionGradient ((c • F : cubicThetaSmoothTests) : CubicThetaSection) p=
      c • cubicThetaSectionGradient F p := by
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,cubicThetaSectionFunction_smul,
    fderiv_const_smul (cubicThetaSectionFunction_differentiable F p.property) c,
    ContinuousLinearMap.comp_apply,smul_apply]
  exact smul_comm p.val.2 c (cubicThetaSectionDifferential F p (cubicThetaTangentBasis i))

def cubicThetaGlobalGradient : cubicThetaSmoothTests →ₗ[ℂ] CubicThetaGradientL2 where
  toFun F := (cubicThetaGradientRepresentative_memLp F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(cubicThetaGradientRepresentative_memLp (F+G)).coeFn_toLp,
      (cubicThetaGradientRepresentative_memLp F).coeFn_toLp,
      (cubicThetaGradientRepresentative_memLp G).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaGradientRepresentative_memLp F).toLp _)
        ((cubicThetaGradientRepresentative_memLp G).toLp _)] with q hFG hF hG hadd
    simp only [Pi.add_apply] at hadd
    rw [hFG,hadd,hF,hG]
    exact cubicThetaSectionGradient_add F G _
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(cubicThetaGradientRepresentative_memLp (c • F)).coeFn_toLp,
      (cubicThetaGradientRepresentative_memLp F).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaGradientRepresentative_memLp F).toLp _)] with q hCF hF hsmul
    simp only [Pi.smul_apply] at hsmul
    simp only [RingHom.id_apply]
    rw [hCF,hsmul,hF]
    exact cubicThetaSectionGradient_smul c F _

end CubicFirstMoment

end

end OAI
