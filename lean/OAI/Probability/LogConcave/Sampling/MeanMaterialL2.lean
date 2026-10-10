import Mathlib
import OAI.Probability.LogConcave.Dynamics.FullProbabilityFlow
import OAI.Probability.LogConcave.Sampling.JointMeanMaterial
import OAI.Probability.LogConcave.Analysis.InterpolationHessianBudget

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

theorem mean_material_l2 (n : ℕ) :
    ∃A : TensorSum (Unit ⊕ Unit),∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r ρ : ℝ},0 < r → 0 < lam →
        (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 → 1≤d →
        Real.sqrt (∑i : Fin d,∫y,
          (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
            (jointMean F x r i) (ρ,y))^2 ∂interpolationLaw F x r ρ)≤
          ((lam:ℝ)*r)*Real.sqrt (d:ℝ)*((A.momentBudget d 1 2).toReal+
            Real.sqrt (interpolationHessianBudget:ℝ)*(A.momentBudget d 0 2).toReal)*
            ((Real.sqrt (1-ρ^2))⁻¹)^(2*n+2) := by
  obtain ⟨A,hw,he⟩ := mean_material_representation n
  refine ⟨A,?_⟩
  intro d F lam hF x r ρ hr hlam hl h0 h1 hd
  simp_rw [he hF x hr hlam hl h0 h1,mul_pow,integral_const_mul,←Finset.mul_sum]
  rw [←mul_pow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_nonneg lam.coe_nonneg hr.le)]
  have hE := A.outer_l2 hF x hr hlam hl h0 h1 hd hw
  let R := (Real.sqrt (1-ρ^2))⁻¹
  have hR : 1≤R := by
    apply (one_le_inv₀ (Real.sqrt_pos.mpr (by nlinarith))).mpr
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])
  have hp : R^(2*n+1)≤R^(2*n+2) := pow_le_pow_right₀ hR (by omega)
  apply (mul_le_mul_of_nonneg_left hE (mul_nonneg lam.coe_nonneg hr.le)).trans
  have hb : 0≤(lam:ℝ)*r*Real.sqrt (d:ℝ)*((A.momentBudget d 1 2).toReal+
      Real.sqrt (interpolationHessianBudget:ℝ)*(A.momentBudget d 0 2).toReal) := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hb
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma joint_material_direction {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {A : ℝ × Point d → ℝ} {ρ : ℝ} {y : Point d}
    (hA : DifferentiableAt ℝ A (ρ,y)) :
    (fderiv ℝ A (ρ,y)) (1,-r • conditionalFieldMean F x r ρ y)=
      JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) A (ρ,y) := by
  have ht := joint_mdir_eq_material F x r hA
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) A (ρ,y)=_ at ht
  rw [ht]
  unfold materialScalar
  rw [JetCalculus.dir_left_slice_at hA]
  change _=JetCalculus.dir (1,0) A (ρ,y)-r*JetCalculus.dir (conditionalFieldMean F x r ρ y)
    (fun z => A (ρ,z)) y
  rw [JetCalculus.dir_right_slice_at hA]
  unfold JetCalculus.dir
  have he : ((1:ℝ),-r • conditionalFieldMean F x r ρ y)=
      (1,0)+(-r) • (0,conditionalFieldMean F x r ρ y) := by simp
  rw [he,map_add,map_smul]
  simp only [smul_eq_mul,neg_mul]
  ring

lemma fullProbabilityFlow_deriv {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) :
    HasDerivWithinAt (fun t => fullProbabilityFlow hF x hr hl t z)
      (-r • conditionalFieldMean F x r ρ (fullProbabilityFlow hF x hr hl ρ z)) (Icc 0 1) ρ := by
  have hh := GlobalODE.flow_deriv (a:=0) (b:=1)
    (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
    (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z ρ ⟨h0,h1.le⟩
  rw [fullProbabilityVelocity_eq F x r h0 h1] at hh
  exact hh

lemma material_path_chain {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    {A : ℝ × Point d → ℝ} (hA : DifferentiableAt ℝ A (ρ,fullProbabilityFlow hF x hr hl ρ z)) :
    HasDerivWithinAt (fun t => A (t,fullProbabilityFlow hF x hr hl t z))
      (JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) A
        (ρ,fullProbabilityFlow hF x hr hl ρ z)) (Icc 0 1) ρ := by
  have hh := hA.hasFDerivAt.comp_hasDerivWithinAt ρ
    ((hasDerivWithinAt_id ρ (Icc 0 1)).prodMk (fullProbabilityFlow_deriv hF x z hr hl h0 h1))
  rwa [joint_material_direction F x r hA] at hh

lemma mean_material_path_deriv {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (i : Fin d) (n : ℕ) :
    HasDerivWithinAt (fun t => JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (t,fullProbabilityFlow hF x hr hl t z))
      (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
        (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr hl ρ z)) (Icc 0 1) ρ := by
  apply material_path_chain hF x z hr hl h0 h1
  exact (JetCalculus.materialIter_timeSmooth _ _ _ (jointMean_timeSmooth hF x hr hl)
    (jointMean_timeSmooth hF x hr hl i) n _ (by dsimp; linarith) h1).differentiableAt (by simp)

lemma fullProbabilityFlow_interpolation {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0<ρ) (h1 : ρ<1) :
    (stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl ρ)=interpolationLaw F x r ρ := by
  rw [fullProbabilityFlow_eq hF x hr hl h0.le h1]
  exact probabilityFlow_pushforward hF x hr hl h0 h1
end LogConcaveSampling

namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

lemma interpolationLaw_initial {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) : interpolationLaw F x r 0=stdGaussian (Point d) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  simp [interpolationLaw,Measure.map_snd_prod]

lemma fullProbabilityFlow_initial {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) : fullProbabilityFlow hF x hr hl 0=id := by
  funext z
  exact GlobalODE.flow_initial _ _ _ _

lemma fullProbabilityFlow_interpolation_closed {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) :
    (stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl ρ)=interpolationLaw F x r ρ := by
  rcases eq_or_lt_of_le h0 with h|h
  · subst ρ
    rw [fullProbabilityFlow_initial,Measure.map_id,interpolationLaw_initial hF x hr hl]
  · exact fullProbabilityFlow_interpolation hF x hr hl h h1

lemma JetCalculus.TimeSmooth.slice_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ × E → ℝ} (hA : JetCalculus.TimeSmooth A) {ρ : ℝ} (h0 : -1<ρ) (h1 : ρ<1) :
    Continuous (fun y => A (ρ,y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (hA (ρ,y) h0 h1).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)

lemma mean_material_path_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (n : ℕ) :
    (∑i : Fin d,∫z,(JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr hl ρ z))^2 ∂stdGaussian (Point d))=
    ∑i : Fin d,∫y,(JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,y))^2 ∂interpolationLaw F x r ρ := by
  have hm := fullProbabilityFlow_interpolation_closed hF x hr hl h0 h1
  have hc := (fullProbabilityFlow_lipschitz hF x hr hl ⟨h0,h1.le⟩).continuous
  apply Finset.sum_congr rfl
  intro i _
  rw [←hm,integral_map hc.measurable.aemeasurable]
  exact ((JetCalculus.materialIter_timeSmooth _ _ _ (jointMean_timeSmooth hF x hr hl)
    (jointMean_timeSmooth hF x hr hl i) n).slice_continuous (by linarith) h1).pow 2 |>.aestronglyMeasurable
end LogConcaveSampling

end

end

end

end OAI
