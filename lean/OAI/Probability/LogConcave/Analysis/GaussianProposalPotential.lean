import Mathlib
import OAI.Probability.LogConcave.Analysis.PrimitivePotentialModeBounds
import OAI.Probability.LogConcave.Sampling.UnitUniform

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open scoped RealInnerProductSpace

def gaussianProposalPotential (d : ℕ) (x : Point d) : ℝ := inner ℝ x x / 2

lemma gaussianProposalPotential_eq (d : ℕ) (x : Point d) :
    gaussianProposalPotential d x = ‖x‖^2/2 := by
  simp [gaussianProposalPotential]

lemma gaussianProposalPotential_hasGradientAt (d : ℕ) (x : Point d) :
    HasGradientAt (gaussianProposalPotential d) x x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := ((hasFDerivAt_id x).inner ℝ (hasFDerivAt_id x)).const_smul (1/2 : ℝ)
  convert! hd using 1
  · ext y
    simp only [gaussianProposalPotential,Pi.smul_apply,smul_eq_mul,id_eq]
    ring
  · ext y
    change inner ℝ x y = (1/2 : ℝ)*(inner ℝ x y+inner ℝ y x)
    rw [real_inner_comm y x]
    ring

@[simp] lemma gaussianProposalPotential_gradient (d : ℕ) :
    gradient (gaussianProposalPotential d) = id :=
  gradient_eq (gaussianProposalPotential_hasGradientAt d)

lemma gaussianProposalPotential_admissible (d : ℕ) :
    Admissible (gaussianProposalPotential d) := by
  refine ⟨(contDiff_id.inner ℝ contDiff_id).div_const 2, ?_, ?_, ?_⟩
  · simp [gaussianProposalPotential]
  · simp
  · intro x v
    simp only [gaussianProposalPotential_gradient,fderiv_id,ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    constructor
    · rfl
    · nlinarith [sq_nonneg ‖v‖]

lemma partition_comparison {d : ℕ} {V : Point d → ℝ} (hV : Admissible V) :
    (2:ℝ)^(- (d:ℤ)) * (partition (gaussianProposalPotential d)).toReal ≤
      (partition V).toReal ∧
    (partition V).toReal ≤ (partition (gaussianProposalPotential d)).toReal := by
  have hB := gaussianProposalPotential_admissible d
  rw [partition_toReal hV.integrable_exp_neg,partition_toReal hB.integrable_exp_neg]
  constructor
  · have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure (Point d))
      (fun x => Real.exp (-gaussianProposalPotential d x)) (2:ℝ) (hR := by norm_num)
    simp only [finrank_euclideanSpace_fin,smul_eq_mul] at hs
    have hh : Integrable (fun x : Point d => Real.exp (-gaussianProposalPotential d ((2:ℝ) • x))) := by
      convert integrable_gaussian_envelope d (b := 2) (by norm_num) using 1
      ext x
      rw [gaussianProposalPotential_eq,norm_smul,Real.norm_of_nonneg (by norm_num)]
      congr 1
      ring
    rw [zpow_neg,zpow_natCast,← hs]
    apply integral_mono hh hV.integrable_exp_neg
    intro x
    apply Real.exp_le_exp.mpr
    rw [gaussianProposalPotential_eq,norm_smul,Real.norm_of_nonneg (by norm_num)]
    have ht := (hV.quadratic_bounds x).2
    nlinarith [sq_nonneg ‖x‖]
  · apply integral_mono hV.integrable_exp_neg hB.integrable_exp_neg
    intro x
    apply Real.exp_le_exp.mpr
    rw [gaussianProposalPotential_eq]
    linarith [(hV.quadratic_bounds x).1]

def gaussianAcceptance {d : ℕ} (V : Point d → ℝ) (x : Point d) : ℝ :=
  Real.exp (-V x+gaussianProposalPotential d x)

lemma gaussianAcceptance_bounds {d : ℕ} {V : Point d → ℝ} (hV : Admissible V) (x : Point d) :
    0 ≤ gaussianAcceptance V x ∧ gaussianAcceptance V x ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  apply Real.exp_le_one_iff.mpr
  rw [gaussianProposalPotential_eq]
  linarith [(hV.quadratic_bounds x).1]

@[fun_prop] lemma measurable_gaussianAcceptance {d : ℕ} {V : Point d → ℝ} (hV : Admissible V) :
    Measurable (gaussianAcceptance V) :=
  (Real.continuous_exp.comp (hV.smooth.continuous.neg.add
    (gaussianProposalPotential_admissible d).smooth.continuous)).measurable

lemma gaussian_accepted_measure {d : ℕ} {V : Point d → ℝ} (hV : Admissible V) :
    (((gibbs (gaussianProposalPotential d)).prod unitUniform).restrict
      (acceptanceEvent (gaussianAcceptance V))).map Prod.fst =
      ENNReal.ofReal ((partition V).toReal/(partition (gaussianProposalPotential d)).toReal) • gibbs V := by
  have hB := gaussianProposalPotential_admissible d
  have := hB.isProbabilityMeasure_gibbs
  rw [accepted_measure _ (measurable_gaussianAcceptance hV)
    (fun x => (gaussianAcceptance_bounds hV x).1) (fun x => (gaussianAcceptance_bounds hV x).2)]
  rw [gibbs,withDensity_smul_measure,← withDensity_mul]
  · have he : gibbsDensity (gaussianProposalPotential d) *
        (fun x => ENNReal.ofReal (gaussianAcceptance V x)) = gibbsDensity V := by
      funext x
      simp only [Pi.mul_apply,gibbsDensity,gaussianAcceptance,← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 2
      ring
    rw [he,gibbs,smul_smul]
    congr 1
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hB.partition_pos.ne' hB.partition_ne_top),
      ENNReal.ofReal_toReal hV.partition_ne_top,ENNReal.ofReal_toReal hB.partition_ne_top,div_eq_mul_inv]
    rw [mul_right_comm,ENNReal.mul_inv_cancel hV.partition_pos.ne' hV.partition_ne_top,one_mul]
  · exact (Real.continuous_exp.comp hB.smooth.continuous.neg).measurable.ennreal_ofReal
  · exact (measurable_gaussianAcceptance hV).ennreal_ofReal

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
