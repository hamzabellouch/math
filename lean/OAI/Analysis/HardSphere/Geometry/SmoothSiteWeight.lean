import Mathlib
import OAI.Analysis.HardSphere.Geometry.GroundPositionLaw
import OAI.Analysis.HardSphere.Geometry.RadiusLaw

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def smoothSiteWeight (L : Length) (A : Finset (Torus L)) (x : Torus L) : ℝ :=
  Real.exp (-smoothSpatialDistance L A x)

lemma smoothSiteWeight_pos (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    0 < smoothSiteWeight L A x := Real.exp_pos _

lemma smoothSiteWeight_bounds (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    Real.exp (-1)*Real.exp (-spatialSiteDistance L A x) ≤ smoothSiteWeight L A x ∧
    smoothSiteWeight L A x ≤ Real.exp 1*Real.exp (-spatialSiteDistance L A x) := by
  have h := abs_le.mp (smoothSpatialDistance_approximation L A x)
  constructor <;> rw [←Real.exp_add] <;> apply Real.exp_le_exp.mpr <;> linarith only [h.1,h.2]

lemma smoothSiteWeight_le (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    smoothSiteWeight L A x ≤ Real.exp 1 := by
  apply (smoothSiteWeight_bounds L A x).2.trans
  exact mul_le_of_le_one_right (Real.exp_pos 1).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (spatialSiteDistance_nonneg L A x)))

def smoothSiteWeightMultiplier (L : Length) (A : Finset (Torus L)) : SmoothMultiplier 1 L :=
  (spatialDistanceMultiplier L A).realComp (fun t ↦ Real.exp (-t))
    (Real.contDiff_exp.comp contDiff_id.neg)

lemma smoothSiteWeightMultiplier_apply (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    (smoothSiteWeightMultiplier L A).toFun X=(smoothSiteWeight L A (X 0):ℂ) := rfl

lemma smoothSiteWeightMultiplier_real (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    conj ((smoothSiteWeightMultiplier L A).toFun X)=(smoothSiteWeightMultiplier L A).toFun X := by
  rw [smoothSiteWeightMultiplier_apply,Complex.conj_ofReal]

lemma smoothSiteWeight_continuous (L : Length) (A : Finset (Torus L)) : Continuous (smoothSiteWeight L A) :=
  Real.continuous_exp.comp (smoothSpatialDistance_lipschitz L A).continuous.neg

lemma smoothSiteWeight_partial_sq (L : Length) (A : Finset (Torus L)) (j : Fin 3) (x : Torus L) :
    ‖coordDerivative 1 L (smoothSiteWeightMultiplier L A).toFun (0,j) (fun _ ↦ x)‖^2 ≤
      ((spatialMetricConstant:ℝ)^2*Real.exp 1)*smoothSiteWeight L A x := by
  rw [smoothSiteWeightMultiplier,SmoothMultiplier.partial_realComp _ _ _ (spatialDistanceMultiplier_real L A)]
  have hd (t : ℝ) : deriv (fun t : ℝ ↦ Real.exp (-t)) t= -Real.exp (-t) := by
    simpa using (((hasDerivAt_id t).neg).exp).deriv
  rw [hd,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  change (-smoothSiteWeight L A x)^2 * ‖coordDerivative 1 L (spatialDistanceMultiplier L A).toFun (0,j) (fun _ ↦ x)‖^2 ≤ _
  rw [neg_sq]
  have h := sq_le_sq₀ (norm_nonneg _) spatialMetricConstant.coe_nonneg |>.mpr
    (spatialDistanceMultiplier_partial_bound L A (0,j) (fun _ ↦ x))
  have hw := mul_le_mul_of_nonneg_left (smoothSiteWeight_le L A x) (smoothSiteWeight_pos L A x).le
  calc
    _ ≤ (smoothSiteWeight L A x)^2*(spatialMetricConstant:ℝ)^2 := mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ ≤ (Real.exp 1*smoothSiteWeight L A x)*(spatialMetricConstant:ℝ)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [hw]
    _ = _ := by ring

def smoothWeightedCount {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) : ℝ :=
  ∑ i, smoothSiteWeight L A (X i)

def smoothWeightedCountMultiplier (n : ℕ) (L : Length) (A : Finset (Torus L)) : SmoothMultiplier n L :=
  SmoothMultiplier.sum (fun i : Fin n ↦ (smoothSiteWeightMultiplier L A).liftLabel n i)

lemma smoothWeightedCountMultiplier_apply (n : ℕ) (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    (smoothWeightedCountMultiplier n L A).toFun X=(smoothWeightedCount L A X:ℂ) := by
  change (∑ i : Fin n, (smoothSiteWeightMultiplier L A).toFun (fun _ ↦ X i))=_
  simp_rw [smoothSiteWeightMultiplier_apply]
  exact (Complex.ofReal_sum _ _).symm

lemma smoothWeightedCountMultiplier_real (n : ℕ) (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    conj ((smoothWeightedCountMultiplier n L A).toFun X)=(smoothWeightedCountMultiplier n L A).toFun X := by
  rw [smoothWeightedCountMultiplier_apply,Complex.conj_ofReal]

lemma smoothWeightedCount_nonneg {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    0 ≤ smoothWeightedCount L A X := Finset.sum_nonneg (fun i _ ↦ (smoothSiteWeight_pos L A (X i)).le)

lemma smoothWeightedCount_le {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    smoothWeightedCount L A X ≤ Real.exp 1*(n:ℝ) := by
  calc
    _ ≤ ∑ _i : Fin n, Real.exp 1 := Finset.sum_le_sum (fun i _ ↦ smoothSiteWeight_le L A (X i))
    _ = _ := by simp; ring

lemma smoothWeightedCount_bounds {n : ℕ} (L : Length) (A : Finset (Torus L)) (hA : A.Nonempty) (X : Configuration n L) :
    Real.exp (-1)*weightedSiteCount L A X ≤ smoothWeightedCount L A X ∧
    smoothWeightedCount L A X ≤ Real.exp 1*weightedSiteCount L A X := by
  simp only [weightedSiteCount,ite_eq_left hA,smoothWeightedCount,Finset.mul_sum]
  exact ⟨Finset.sum_le_sum (fun i _ ↦ (smoothSiteWeight_bounds L A (X i)).1),
    Finset.sum_le_sum (fun i _ ↦ (smoothSiteWeight_bounds L A (X i)).2)⟩

lemma smoothWeightedCount_continuous {n : ℕ} (L : Length) (A : Finset (Torus L)) :
    Continuous (smoothWeightedCount (n:=n) L A) :=
  continuous_finsetSum _ (fun i _ ↦ (smoothSiteWeight_continuous L A).comp (continuous_apply i))

lemma smoothWeightedCount_gradient {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (smoothWeightedCountMultiplier n L A).toFun p X‖^2) ≤
      (3*(spatialMetricConstant:ℝ)^2*Real.exp 1)*smoothWeightedCount L A X := by
  have hp (p : Direction n) : coordDerivative n L (smoothWeightedCountMultiplier n L A).toFun p X=
      coordDerivative 1 L (smoothSiteWeightMultiplier L A).toFun (0,p.2) (fun _ ↦ X p.1) := by
    classical
    rw [smoothWeightedCountMultiplier,SmoothMultiplier.partial_sum]
    simp_rw [SmoothMultiplier.partial_liftLabel]
    simp
  simp_rw [hp]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Fin n, ∑ _j : Fin 3, ((spatialMetricConstant:ℝ)^2*Real.exp 1)*smoothSiteWeight L A (X i) := by
      exact Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ smoothSiteWeight_partial_sq L A j (X i)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,smoothWeightedCount,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory

lemma groundPositionLaw_integral {n : ℕ} {L : Length} (u : Jet n L) (f : Configuration n L → ℝ) :
    (∫ X, f X ∂groundPositionLaw n L u)=∫ X, f X*‖u.1 X‖^2 := by
  rw [groundPositionLaw,integral_withDensity_eq_integral_toReal_smul
    (((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal)
    (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,mul_comm]

lemma groundPositionLaw_integrable {n : ℕ} {L : Length} (u : Jet n L) (f : Configuration n L → ℝ) :
    Integrable f (groundPositionLaw n L u) ↔ Integrable (fun X ↦ f X*‖u.1 X‖^2) volume := by
  rw [groundPositionLaw,integrable_withDensity_iff
    (((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal)
    (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

lemma groundPositionLaw_probability {n : ℕ} {L : Length} (u : Jet n L) (hu : ‖u.1‖=1) :
    IsProbabilityMeasure (groundPositionLaw n L u) := by
  constructor
  rw [groundPositionLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp u.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
      (Eventually.of_forall (fun X ↦ sq_nonneg ‖u.1 X‖)),←IndicatorStrong.norm_sq_integral,hu]
  norm_num

lemma bounded_mgf_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Ω → ℝ} {B : ℝ} (hF : Measurable F) (hb : ∀ x, |F x| ≤B) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t*F x)) μ := by
  apply (integrable_const (Real.exp (|t| *B))).mono' (hF.const_mul t).exp.aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t*F x ≤ |t*F x| := le_abs_self _
      _ = |t| *|F x| := abs_mul _ _
      _ ≤ |t| *B := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t))

lemma bounded_integrableExpSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Ω → ℝ} {B : ℝ} (hF : Measurable F) (hb : ∀ x, |F x| ≤B) :
    integrableExpSet F μ=univ := by
  ext t
  simp only [mem_univ,iff_true]
  exact bounded_mgf_integrable μ hF hb t

lemma bounded_cgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω → ℝ} {B T C : ℝ} (hF : Measurable F) (hb : ∀ x, |F x| ≤B) (hT : 0≤T)
    (hd : ∀ t∈Icc 0 T, (∫ x, F x*Real.exp (t*F x) ∂μ)≤C*mgf F μ t) :
    ∀ t∈Icc 0 T, cgf F μ t≤C*t := by
  have hm (t : ℝ) : t∈interior (integrableExpSet F μ) := by rw [bounded_integrableExpSet μ hF hb,interior_univ]; trivial
  have hf : Differentiable ℝ (cgf F μ) := fun t ↦ (analyticAt_cgf (hm t)).differentiableAt
  have hd' (t : ℝ) (ht : t∈interior (Icc 0 T)) : deriv (cgf F μ) t≤C := by
    rw [deriv_cgf (hm t)]
    exact (div_le_iff₀ (mgf_pos (bounded_mgf_integrable μ hF hb t))).mpr (hd t (interior_subset ht))
  intro t ht
  have h := (convex_Icc (0:ℝ) T).image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn
    hf.differentiableOn hd' 0 ⟨le_rfl,hT⟩ t ht ht.1
  simpa using h

end HardSphere

end

end OAI
