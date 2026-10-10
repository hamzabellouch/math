import Mathlib
import OAI.Analysis.HardSphere.Geometry.EuclideanTorus

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
open MeasureTheory Set Filter ProbabilityTheory

def radiusLaw : Measure ℝ := expMeasure 1
instance radiusLaw_probability : IsProbabilityMeasure radiusLaw := isProbabilityMeasure_expMeasure (by norm_num)
instance radiusLaw_noAtoms : NullSingletonClass radiusLaw := by
  unfold radiusLaw expMeasure gammaMeasure
  infer_instance

lemma radiusLaw_tail_eq {t : ℝ} (ht : 0≤t) : radiusLaw.real (Ici t)=Real.exp (-t) := by
  have h := measureReal_compl (μ:=radiusLaw) (s:=Iic t) measurableSet_Iic
  rw [compl_Iic,probReal_univ,←cdf_eq_real,radiusLaw,cdf_expMeasure_eq (by norm_num),ite_eq_left ht,one_mul] at h
  have he : radiusLaw.real (Ici t)=radiusLaw.real (Ioi t) := by
    unfold Measure.real
    rw [measure_congr (Ioi_ae_eq_Ici (μ:=radiusLaw) (a:=t))]
  rw [he]
  change (expMeasure 1).real (Ioi t)=_
  rw [h]
  ring

lemma radiusLaw_tail (t : ℝ) : radiusLaw.real (Ici t)≤Real.exp (-t) := by
  by_cases ht : 0≤t
  · exact (radiusLaw_tail_eq ht).le
  · calc
      _ ≤ radiusLaw.real univ := measureReal_mono (subset_univ _)
      _ = 1 := probReal_univ
      _ ≤ Real.exp (-t) := Real.one_le_exp (by linarith)

lemma radius_integral_bound {f : ℝ → ℝ} {B d : ℝ} (hB : 0≤B)
    (hf : Measurable f) (hn : ∀ H, 0≤f H) (hb : ∀ H, f H≤B)
    (hz : ∀ H, H+3<d → f H=0) :
    Integrable f radiusLaw ∧ (∫ H, f H ∂radiusLaw)≤B*Real.exp 3*Real.exp (-d) := by
  have hi : Integrable f radiusLaw := (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun H ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hn H)]; exact hb H))
  refine ⟨hi,?_⟩
  have hdom (H : ℝ) : f H≤(Ici (d-3)).indicator (fun _ ↦ B) H := by
    by_cases hm : H∈Ici (d-3)
    · rw [Set.indicator_of_mem hm]; exact hb H
    · rw [Set.indicator_of_notMem hm,hz H (by have hnot : ¬ d-3≤H := hm; have := lt_of_not_ge hnot; linarith)]
  have hh := integral_mono hi ((integrable_const B).indicator measurableSet_Ici) hdom
  rw [integral_indicator_const _ measurableSet_Ici,smul_eq_mul] at hh
  apply hh.trans
  calc
    radiusLaw.real (Ici (d-3))*B ≤ Real.exp (-(d-3))*B := mul_le_mul_of_nonneg_right (radiusLaw_tail _) hB
    _ = B*Real.exp 3*Real.exp (-d) := by rw [show -(d-3)=3+(-d) by ring,Real.exp_add]; ring

lemma spatialSine_deriv_continuous_radius (t : ℝ) : Continuous (fun H ↦ deriv (spatialSine H) t) := by
  simp_rw [spatialSine_deriv,spatialAngle]
  have hp := (CellOrbital.profile_smooth 1).continuous
  have hd := (CellOrbital.profile_smooth 1).continuous_deriv (by simp)
  exact (Real.continuous_cos.comp (continuous_const.mul (hp.comp (continuous_const.sub continuous_id)))).mul
    (continuous_const.mul (hd.comp (continuous_const.sub continuous_id)))

lemma spatialCosine_deriv_continuous_radius (t : ℝ) : Continuous (fun H ↦ deriv (spatialCosine H) t) := by
  simp_rw [spatialCosine_deriv,spatialAngle]
  have hp := (CellOrbital.profile_smooth 1).continuous
  have hd := (CellOrbital.profile_smooth 1).continuous_deriv (by simp)
  exact (Real.continuous_sin.comp (continuous_const.mul (hp.comp (continuous_const.sub continuous_id)))).neg.mul
    (continuous_const.mul (hd.comp (continuous_const.sub continuous_id)))

def spatialEnergyError (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) : ℝ :=
  ∑ j : Fin 3, (‖coordDerivative 1 L (spatialInside L A H).toFun (0,j) (fun _ ↦ x)‖^2+
    ‖coordDerivative 1 L (spatialOutside L A H).toFun (0,j) (fun _ ↦ x)‖^2)

lemma spatialEnergyError_nonneg (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) :
    0≤ spatialEnergyError L A H x := Finset.sum_nonneg (fun _ _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma spatialEnergyError_continuous_radius (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    Continuous (fun H ↦ spatialEnergyError L A H x) := by
  unfold spatialEnergyError
  apply continuous_finsetSum
  intro j _
  simp_rw [spatialInside_partial,spatialOutside_partial]
  exact ((Complex.continuous_ofReal.comp (spatialSine_deriv_continuous_radius _)).mul continuous_const).norm.pow 2 |>.add
    (((Complex.continuous_ofReal.comp (spatialCosine_deriv_continuous_radius _)).mul continuous_const).norm.pow 2)

lemma spatialInside_average (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    Integrable (fun H ↦ ‖(spatialInside L A H).orbital x‖^2) radiusLaw ∧
    (∫ H, ‖(spatialInside L A H).orbital x‖^2 ∂radiusLaw)≤Real.exp 3*Real.exp (-spatialSiteDistance L A x) := by
  have hmeas : Measurable (fun H ↦ ‖(spatialInside L A H).orbital x‖^2) := by
    change Measurable (fun H ↦ ‖(Real.sin (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A x-H)):ℂ)‖^2)
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_const.mul ((CellOrbital.profile_smooth 1).continuous.comp
      (continuous_const.sub continuous_id))))).norm.pow 2 |>.measurable
  simpa only [one_mul] using radius_integral_bound (B:=1) (d:=spatialSiteDistance L A x) (by norm_num) hmeas
    (fun H ↦ sq_nonneg _) (fun H ↦ by nlinarith only [spatialInside_norm_le L A H x,norm_nonneg ((spatialInside L A H).orbital x)])
    (fun H hH ↦ by rw [spatialInside_zero L A H x hH.le]; simp)

theorem spatialEnergyError_average : ∃ C : ℝ, 0<C ∧
    ∀ (L : Length) (A : Finset (Torus L)) (x : Torus L),
      Integrable (fun H ↦ spatialEnergyError L A H x) radiusLaw ∧
      (∫ H, spatialEnergyError L A H x ∂radiusLaw)≤C*Real.exp (-spatialSiteDistance L A x) := by
  obtain ⟨B,hB,hbound⟩ := spatialPartition_partial_bound
  refine ⟨6*B^2*Real.exp 3,by positivity,?_⟩
  intro L A x
  apply radius_integral_bound (by positivity) (spatialEnergyError_continuous_radius L A x).measurable
    (fun H ↦ spatialEnergyError_nonneg L A H x)
  · intro H
    calc
      _ ≤ ∑ j : Fin 3, (2*B^2) := by
        apply Finset.sum_le_sum
        intro j _
        obtain ⟨h1,h2⟩ := hbound L A H (0,j) (fun _ ↦ x)
        nlinarith only [sq_le_sq₀ (norm_nonneg _) hB.le |>.mpr h1,
          sq_le_sq₀ (norm_nonneg _) hB.le |>.mpr h2]
      _ = 6*B^2 := by simp; ring
  · intro H hH
    unfold spatialEnergyError
    apply Finset.sum_eq_zero
    intro j _
    obtain ⟨h1,h2⟩ := spatialPartition_partial_zero L A H (0,j) (fun _ ↦ x) hH
    rw [h1,h2]; simp

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

lemma L2_bounded_weight_integrable {n : ℕ} {L : Length} (u : ScalarL2 n L)
    {v : Configuration n L → ℝ} {B : ℝ} (hv : Measurable v) (hb : ∀ X, |v X|≤B) :
    Integrable (fun X ↦ v X*‖u X‖^2) volume := by
  have hi := ((Lp.memLp u).integrable_norm_pow (by norm_num)).const_mul B
  apply hi.mono' (hv.mul ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2)).aestronglyMeasurable
  exact Eventually.of_forall fun X ↦ by
    change ‖v X*‖u X‖^2‖≤B*‖u X‖^2
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u X‖)]
    exact mul_le_mul_of_nonneg_right (hb X) (sq_nonneg _)

lemma radius_configuration_bound {n : ℕ} {L : Length} (u : ScalarL2 n L)
    {f : ℝ → Configuration n L → ℝ} {B M : ℝ} {v : Configuration n L → ℝ}
    (hf : Measurable (Function.uncurry f)) (hb : ∀ H X, |f H X|≤B)
    (hv : Measurable v) (hM : ∀ X, |v X|≤M)
    (havg : ∀ X, (∫ H, f H X ∂radiusLaw)≤v X) :
    Integrable (fun H ↦ ∫ X, f H X*‖u X‖^2) radiusLaw ∧
    (∫ H, (∫ X, f H X*‖u X‖^2) ∂radiusLaw)≤∫ X, v X*‖u X‖^2 := by
  have hd := ((Lp.memLp u).integrable_norm_pow (by norm_num)).comp_snd radiusLaw
  have hprod : Integrable (fun z : ℝ×Configuration n L ↦ f z.1 z.2*‖u z.2‖^2) (radiusLaw.prod volume) := by
    apply (hd.const_mul B).mono'
      (hf.mul (((Lp.stronglyMeasurable u).measurable.comp measurable_snd).norm.pow_const 2)).aestronglyMeasurable
    exact Eventually.of_forall fun z ↦ by
      change ‖f z.1 z.2*‖u z.2‖^2‖≤B*‖u z.2‖^2
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u z.2‖)]
      exact mul_le_mul_of_nonneg_right (hb z.1 z.2) (sq_nonneg _)
  refine ⟨hprod.integral_prod_left,?_⟩
  rw [integral_integral_swap hprod]
  apply integral_mono hprod.integral_prod_right (L2_bounded_weight_integrable u hv hM)
  intro X
  change (∫ H, f H X*‖u X‖^2 ∂radiusLaw)≤v X*‖u X‖^2
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (havg X) (sq_nonneg _)

lemma spatialInside_joint_continuous (L : Length) (A : Finset (Torus L)) :
    Continuous (fun z : ℝ×Torus L ↦ (spatialInside L A z.1).orbital z.2) := by
  change Continuous (fun z : ℝ×Torus L ↦
    (Real.sin (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A z.2-z.1)):ℂ))
  exact Complex.continuous_ofReal.comp (Real.continuous_sin.comp
    (continuous_const.mul ((CellOrbital.profile_smooth 1).continuous.comp
      (((smoothSpatialDistance_lipschitz L A).continuous.comp continuous_snd).sub continuous_fst))))

lemma spatialEnergyError_joint_continuous (L : Length) (A : Finset (Torus L)) :
    Continuous (fun z : ℝ×Torus L ↦ spatialEnergyError L A z.1 z.2) := by
  unfold spatialEnergyError
  apply continuous_finsetSum
  intro j _
  simp_rw [spatialInside_partial,spatialOutside_partial,spatialSine_deriv,spatialCosine_deriv,spatialAngle]
  have hh : Continuous (fun z : ℝ×Torus L ↦ smoothSpatialDistance L A z.2-z.1) :=
    ((smoothSpatialDistance_lipschitz L A).continuous.comp continuous_snd).sub continuous_fst
  have hp := (CellOrbital.profile_smooth 1).continuous.comp hh
  have hd := ((CellOrbital.profile_smooth 1).continuous_deriv (by simp)).comp hh
  have hc : Continuous (fun z : ℝ×Torus L ↦ coordDerivative 1 L (spatialDistanceMultiplier L A).toFun (0,j) (fun _ ↦ z.2)) :=
    (continuous_coordDerivative (spatialDistanceMultiplier L A).smooth (0,j)).comp (continuous_pi fun _ ↦ continuous_snd)
  exact ((Complex.continuous_ofReal.comp ((Real.continuous_cos.comp (continuous_const.mul hp)).mul
    (continuous_const.mul hd))).mul hc).norm.pow 2 |>.add
    (((Complex.continuous_ofReal.comp ((Real.continuous_sin.comp (continuous_const.mul hp)).neg.mul
    (continuous_const.mul hd))).mul hc).norm.pow 2)

def weightedSiteCount {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) : ℝ :=
  if A.Nonempty then ∑ i : Fin n, Real.exp (-spatialSiteDistance L A (X i)) else 0

lemma weightedSiteCount_nonneg {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    0≤ weightedSiteCount L A X := by
  unfold weightedSiteCount
  split_ifs <;> positivity

lemma weightedSiteCount_le {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    weightedSiteCount L A X≤(n:ℝ) := by
  unfold weightedSiteCount
  split_ifs
  · calc
      _ ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum (fun i _ ↦ Real.exp_le_one_iff.mpr (neg_nonpos.mpr (spatialSiteDistance_nonneg L A _)))
      _ = _ := by simp
  · positivity

lemma weightedSiteCount_continuous {n : ℕ} (L : Length) (A : Finset (Torus L)) :
    Continuous (weightedSiteCount (n:=n) L A) := by
  unfold weightedSiteCount
  split_ifs
  · exact continuous_finsetSum _ (fun i _ ↦ Real.continuous_exp.comp
      (((spatialSiteDistance_lipschitz L A).continuous.comp (continuous_apply i)).neg))
  · exact continuous_const

lemma spatialInside_configuration_average {n : ℕ} (L : Length) (A : Finset (Torus L))
    (hA : A.Nonempty) (u : ScalarL2 n L) :
    Integrable (fun H ↦ ∫ X, (∑ i : Fin n, ‖(spatialInside L A H).orbital (X i)‖^2)*‖u X‖^2) radiusLaw ∧
    (∫ H, (∫ X, (∑ i : Fin n, ‖(spatialInside L A H).orbital (X i)‖^2)*‖u X‖^2) ∂radiusLaw)≤
      Real.exp 3*(∫ X, weightedSiteCount L A X*‖u X‖^2) := by
  rw [← integral_const_mul]
  simp_rw [← mul_assoc]
  apply radius_configuration_bound u (B:=(n:ℝ)) (M:=Real.exp 3*(n:ℝ))
  · exact (continuous_finsetSum _ (fun i _ ↦ ((spatialInside_joint_continuous L A).comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))).norm.pow 2)).measurable
  · intro H X
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
    calc
      _ ≤ ∑ _i : Fin n, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith only [spatialInside_norm_le L A H (X i),norm_nonneg ((spatialInside L A H).orbital (X i))]
      _ = _ := by simp
  · exact (continuous_const.mul (weightedSiteCount_continuous L A)).measurable
  · intro X
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (weightedSiteCount_nonneg L A X))]
    exact mul_le_mul_of_nonneg_left (weightedSiteCount_le L A X) (Real.exp_pos _).le
  · intro X
    rw [integral_finsetSum Finset.univ (fun i _ ↦ (spatialInside_average L A (X i)).1),weightedSiteCount,ite_eq_left hA,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ (spatialInside_average L A (X i)).2)

theorem spatialEnergyError_configuration_average : ∃ C : ℝ, 0<C ∧
    ∀ (n : ℕ) (L : Length) (A : Finset (Torus L)), A.Nonempty → ∀ (u : ScalarL2 n L),
    Integrable (fun H ↦ ∫ X, (∑ i : Fin n, spatialEnergyError L A H (X i))*‖u X‖^2) radiusLaw ∧
    (∫ H, (∫ X, (∑ i : Fin n, spatialEnergyError L A H (X i))*‖u X‖^2) ∂radiusLaw)≤
      C*(∫ X, weightedSiteCount L A X*‖u X‖^2) := by
  obtain ⟨C,hC,havg⟩ := spatialEnergyError_average
  obtain ⟨B,hB,hbound⟩ := spatialPartition_partial_bound
  refine ⟨C,hC,?_⟩
  intro n L A hA u
  rw [← integral_const_mul]
  simp_rw [← mul_assoc]
  apply radius_configuration_bound u (B:=(n:ℝ)*6*B^2) (M:=C*(n:ℝ))
  · exact (continuous_finsetSum _ (fun i _ ↦ (spatialEnergyError_joint_continuous L A).comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))).measurable
  · intro H X
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ ↦ spatialEnergyError_nonneg L A H (X i)))]
    calc
      _ ≤ ∑ _i : Fin n, 6*B^2 := by
        apply Finset.sum_le_sum
        intro i _
        unfold spatialEnergyError
        calc
          _ ≤ ∑ j : Fin 3, 2*B^2 := by
            apply Finset.sum_le_sum
            intro j _
            obtain ⟨h1,h2⟩ := hbound L A H (0,j) (fun _ ↦ X i)
            nlinarith only [sq_le_sq₀ (norm_nonneg _) hB.le |>.mpr h1,
              sq_le_sq₀ (norm_nonneg _) hB.le |>.mpr h2]
          _ = _ := by simp; ring
      _ = _ := by simp; ring
  · exact (continuous_const.mul (weightedSiteCount_continuous L A)).measurable
  · intro X
    rw [abs_of_nonneg (mul_nonneg hC.le (weightedSiteCount_nonneg L A X))]
    exact mul_le_mul_of_nonneg_left (weightedSiteCount_le L A X) hC.le
  · intro X
    rw [integral_finsetSum Finset.univ (fun i _ ↦ (havg L A (X i)).1),weightedSiteCount,ite_eq_left hA,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ (havg L A (X i)).2)

end HardSphere

end

end OAI
