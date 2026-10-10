import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkTangentError
import OAI.Probability.Perceptron.Cavity.BulkReplicaDominated

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction ContDiff

lemma bulkReplicaMean_add_dominated (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {F G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ}
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    {D E : BulkDisorder (n+1) M→ℝ}
    (hD : Integrable D (bulkDisorderLaw (n+1) M)) (hE : Integrable E (bulkDisorderLaw (n+1) M))
    (hD0 : ∀ a,0≤D a) (hE0 : ∀ a,0≤E a)
    (hbF : ∀ a x,|F a x|≤D a) (hbG : ∀ a x,|G a x|≤E a) :
    bulkReplicaMean n M f v r (fun a x => F a x+G a x)=
      bulkReplicaMean n M f v r F+bulkReplicaMean n M f v r G := by
  have he (a : BulkDisorder (n+1) M) :
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (fun x => F a x+G a x)=
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (F a)+
        gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (G a) := by
    let := tilt_law_probability_of_integrable (unitSphereLaw (n+1))
      (show Integrable (fun x => Real.exp (1*bulkHamiltonian (n+1) M f v a.1 a.2 x)) (unitSphereLaw (n+1)) from
        by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f v a)
    simp_rw [gibbsReplicaMean_integral_of_integrable (unitSphereLaw (n+1))
      (bulkHamiltonian_section_measurable _ _ _ _ a) (bulkHamiltonian_exp_integrable n M f v a)]
    exact integral_add
      (Integrable.of_bound hF.of_uncurry_left.aestronglyMeasurable (D a) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbF a x))
      (Integrable.of_bound hG.of_uncurry_left.aestronglyMeasurable (E a) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbG a x))
  unfold bulkReplicaMean
  simp_rw [he]
  exact integral_add
    (replicaMean_param_integrable_dominated _ _ r (bulkHamiltonian_continuous _ _ _ _).measurable hF hD hD0 hbF)
    (replicaMean_param_integrable_dominated _ _ r (bulkHamiltonian_continuous _ _ _ _).measurable hG hE hE0 hbG)

lemma bulkTangentDirection_bounded (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ x,‖bulkTangentDirection N v G x‖≤D := by
  obtain ⟨D,hD⟩ := (isCompact_univ : IsCompact (univ : Set (Fin 2→NormalizedSpin N))).bddAbove_image
    (bulkTangentDirection_continuous N v G).norm.continuousOn
  exact ⟨max D 0,le_max_right _ _,fun x => (hD (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)⟩

def bulkTangentPerturbation {N M : ℕ} (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    (a : BulkDisorder N M) (x : Fin 2→NormalizedSpin N) : ℝ :=
  inner ℝ (bulkTangentDirection N v G x) a.2

lemma bulkTangentPerturbation_measurable (N M : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (bulkTangentPerturbation (N:=N) (M:=M) v G)) :=
  (((bulkTangentDirection_continuous N v G).comp continuous_snd).inner continuous_fst.snd).measurable

lemma bulkTangentPerturbation_bound {N M : ℕ} (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    {D : ℝ} (hb : ∀ x,‖bulkTangentDirection N v G x‖≤D)
    (a : BulkDisorder N M) (x : Fin 2→NormalizedSpin N) :
    |bulkTangentPerturbation v G a x|≤D*‖a.2‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

lemma bulkMarkNorm_integrable (N M : ℕ) :
    Integrable (fun a : BulkDisorder N M => ‖a.2‖) (bulkDisorderLaw N M) :=
  ((((IsGaussian.memLp_id (stdGaussian (BulkMark N)) 2 (by simp)).norm).integrable (by norm_num))).comp_snd _

lemma bulkTangentPerturbation_integrable (n M : ℕ) (f G : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Integrable (fun a : BulkDisorder (n+1) M => gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) 2 (bulkTangentPerturbation v G a)) (bulkDisorderLaw (n+1) M) := by
  obtain ⟨D,hD,hb⟩ := bulkTangentDirection_bounded (n+1) v G
  exact replicaMean_param_integrable_dominated _ _ 2 (bulkHamiltonian_continuous _ _ _ _).measurable
    (bulkTangentPerturbation_measurable _ _ _ _) ((bulkMarkNorm_integrable (n+1) M).const_mul D)
    (fun a => mul_nonneg hD (norm_nonneg _)) (bulkTangentPerturbation_bound v G hb)

lemma bulk_tangent_annealed_perturbation_bound (n M : ℕ) (f G : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C) :
    |bulkReplicaMean n M f v 2 (bulkTangentPerturbation v G)|≤8*‖G‖*C^2*bulkScale (n+1)^2 := by
  unfold bulkReplicaMean
  rw [show bulkDisorderLaw (n+1) M =
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1).prod (stdGaussian (BulkMark (n+1))) from rfl]
  rw [integral_prod _ (bulkTangentPerturbation_integrable n M f G v)]
  have hb : ∀ a : Fin M→Fin (n+1)→ℝ,
      ‖∫ b : BulkMark (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v a b) 2 (bulkTangentPerturbation v G (a,b))
          ∂stdGaussian (BulkMark (n+1))‖≤8*‖G‖*C^2*bulkScale (n+1)^2 := by
    intro a
    rw [Real.norm_eq_abs]
    change |∫ b : BulkMark (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a b) 2 (fun x => inner ℝ (bulkTangentDirection (n+1) v G x) b)
        ∂stdGaussian (BulkMark (n+1))|≤_
    exact bulk_tangent_perturbation_bound n M f G v a hC hv
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) hb)

lemma continuous_real_compact_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : X→ℝ} (hF : Continuous F) : ∃ D : ℝ,0≤D ∧ ∀ x,|F x|≤D := by
  obtain ⟨D,hD⟩ := (isCompact_univ : IsCompact (univ : Set X)).bddAbove_image hF.abs.continuousOn
  exact ⟨max D 0,le_max_right _ _,fun x => (hD (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)⟩

def tangentDerivTest (N : ℕ) (G : ℝ→ᵇℝ) (x : Fin 2→NormalizedSpin N) : ℝ :=
  deriv (G : ℝ→ℝ) (spinOverlap (x 0) (x 1))*(1-spinOverlap (x 0) (x 1)^2)

lemma tangentDerivTest_continuous (N : ℕ) (G : ℝ→ᵇℝ) (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) :
    Continuous (tangentDerivTest N G) := by
  have hr : Continuous (fun x : Fin 2→NormalizedSpin N => spinOverlap (x 0) (x 1)) := by
    unfold spinOverlap; fun_prop
  exact ((hG.continuous_deriv (by norm_num)).comp hr).mul (continuous_const.sub (hr.pow 2))

lemma bulk_tangent_row_ibp_any (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (j : Fin M) :
    bulkReplicaMean n M f.f v 2 (bulkTangentPattern f G j) =
      bulkReplicaMean n M f.f v 2 (fun a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))-
      2*bulkReplicaMean n M f.f v 3 (fun a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j))) := by
  cases M with
  | zero => exact Fin.elim0 j
  | succ M => exact bulk_tangent_row_ibp n M f v G j

lemma bulk_tangent_annealed (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C) :
    |(n:ℝ)*bulkReplicaMean n M f.f v 2 (fun _ x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1)))-
      bulkReplicaMean n M f.f v 2 (fun _ => tangentDerivTest (n+1) G)-
      ∑ j : Fin M, (bulkReplicaMean n M f.f v 2 (fun a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))-
        2*bulkReplicaMean n M f.f v 3 (fun a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j))))|≤
      8*‖G‖*C^2*bulkScale (n+1)^2 := by
  let T := fun a : BulkDisorder (n+1) M => fun x : Fin 2→NormalizedSpin (n+1) => ∑ j,bulkTangentPattern f G j a x
  let D := fun a : BulkDisorder (n+1) M => ∑ j : Fin M,2*‖G‖*‖f.d1‖*bulkPatternSize j a
  have hT : Measurable (Function.uncurry T) := Finset.measurable_sum _ fun j _ => bulkTangentPattern_measurable _ _ _ _ j
  have hD : Integrable D (bulkDisorderLaw (n+1) M) := integrable_finsetSum _ fun j _ =>
    (bulkPatternSize_integrable (n+1) M j).const_mul (2*‖G‖*‖f.d1‖)
  have hD0 (a : BulkDisorder (n+1) M) : 0≤D a := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hbT (a : BulkDisorder (n+1) M) (x : Fin 2→NormalizedSpin (n+1)) : |T a x|≤D a :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => bulkTangentPattern_bound f G j a x)
  obtain ⟨E,hE,hbE⟩ := continuous_real_compact_bound (tangentDerivTest_continuous (n+1) G hG)
  have hEme : Measurable (Function.uncurry (fun _ : BulkDisorder (n+1) M => tangentDerivTest (n+1) G)) :=
    (tangentDerivTest_continuous (n+1) G hG).measurable.comp measurable_snd
  obtain ⟨K,hK,hbK⟩ := bulkTangentDirection_bounded (n+1) v G
  have hP := bulkTangentPerturbation_measurable (n+1) M v G
  have hbP := bulkTangentPerturbation_bound (M:=M) v G hbK
  have hiP := (bulkMarkNorm_integrable (n+1) M).const_mul K
  have he : (n:ℝ)*bulkReplicaMean n M f.f v 2 (fun _ x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1)))=
      bulkReplicaMean n M f.f v 2 (fun a x => tangentDerivTest (n+1) G x+T a x+bulkTangentPerturbation v G a x) := by
    unfold bulkReplicaMean
    rw [←integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun a => bulk_gibbs_replica_tangent n M f v a.1 a.2 G hG)
  have hET : Measurable (Function.uncurry (fun a x => tangentDerivTest (n+1) G x+T a x)) := hEme.add hT
  have hadd := bulkReplicaMean_add_dominated n M 2 f.f v hET hP
    ((integrable_const E).add hD) hiP (fun a => add_nonneg hE (hD0 a)) (fun a => mul_nonneg hK (norm_nonneg _))
    (fun a x => (abs_add_le _ _).trans (add_le_add (hbE x) (hbT a x))) hbP
  have hadd' := bulkReplicaMean_add_dominated n M 2 f.f v hEme hT (integrable_const E) hD
    (fun _ => hE) hD0 (fun _ x => hbE x) hbT
  rw [he,hadd,hadd']
  have hsum : bulkReplicaMean n M f.f v 2 T=∑ j : Fin M,bulkReplicaMean n M f.f v 2 (bulkTangentPattern f G j) :=
    bulkReplicaMean_sum_dominated n M 2 f.f v Finset.univ _
      (fun j _ => bulkTangentPattern_measurable _ _ _ _ j)
      (fun j a => 2*‖G‖*‖f.d1‖*bulkPatternSize j a)
      (fun j _ => (bulkPatternSize_integrable (n+1) M j).const_mul (2*‖G‖*‖f.d1‖))
      (fun j _ a => mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _))
      (fun j _ => bulkTangentPattern_bound f G j)
  rw [hsum]
  simp_rw [bulk_tangent_row_ibp_any n M f v G]
  convert bulk_tangent_annealed_perturbation_bound n M f.f G v hC hv using 1
  congr 1
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
