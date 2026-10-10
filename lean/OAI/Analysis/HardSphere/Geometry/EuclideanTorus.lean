import Mathlib
import OAI.Analysis.HardSphere.Orbitals.Profile
import OAI.Analysis.HardSphere.Geometry.SelectedEnergyAddCompl

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
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

abbrev EuclideanTorus (L : Length) := PiLp 2 (fun _ : Fin 3 ↦ AddCircle L.val)

def euclideanTorusPoint (L : Length) (x : Torus L) : EuclideanTorus L := WithLp.toLp 2 x

lemma euclideanTorusPoint_dist (L : Length) (x y : Torus L) :
    dist (euclideanTorusPoint L x) (euclideanTorusPoint L y)=torusDistance L x y :=
  PiLp.dist_eq_of_L2 _ _

def spatialSiteDistance (L : Length) (A : Finset (Torus L)) (x : Torus L) : ℝ :=
  Metric.infDist (euclideanTorusPoint L x) (euclideanTorusPoint L '' (A:Set (Torus L)))

def spatialMetricConstant : ℝ≥0 := (3:ℝ≥0)^((1/(2:ENNReal)).toReal)

lemma spatialMetricConstant_pos : 0<(spatialMetricConstant:ℝ) := by
  unfold spatialMetricConstant
  positivity

lemma spatialSiteDistance_lipschitz (L : Length) (A : Finset (Torus L)) :
    LipschitzWith spatialMetricConstant (spatialSiteDistance L A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (Metric.lipschitz_infDist_pt (euclideanTorusPoint L '' (A:Set (Torus L)))).dist_le_mul
    (euclideanTorusPoint L x) (euclideanTorusPoint L y)
  have ht := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin 3 ↦ AddCircle L.val)).dist_le_mul x y
  apply h.trans
  rw [NNReal.coe_one,one_mul]
  convert ht using 1 <;> rfl

lemma spatialSiteDistance_nonneg (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    0≤ spatialSiteDistance L A x := Metric.infDist_nonneg

lemma spatialSiteDistance_le (L : Length) (A : Finset (Torus L)) (x y : Torus L) (hy : y∈A) :
    spatialSiteDistance L A x≤torusDistance L x y := by
  rw [←euclideanTorusPoint_dist]
  exact Metric.infDist_le_dist_of_mem ⟨y,hy,rfl⟩

lemma spatialSiteDistance_attained (L : Length) (A : Finset (Torus L)) (hA : A.Nonempty) (x : Torus L) :
    ∃ y∈A, spatialSiteDistance L A x=torusDistance L x y := by
  have hc : IsCompact (euclideanTorusPoint L '' (A:Set (Torus L))) :=
    (A.finite_toSet.image _).isCompact
  obtain ⟨y,⟨z,hz,rfl⟩,he⟩ := hc.exists_infDist_eq_dist (by exact Set.Nonempty.image _ hA.to_set) (euclideanTorusPoint L x)
  exact ⟨z,hz,he.trans (euclideanTorusPoint_dist L x z)⟩

def spatialDistanceBump : ContDiffBump (0 : SpatialLift) where
  rIn := 1/(2*((spatialMetricConstant:ℝ)+1))
  rOut := 1/((spatialMetricConstant:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hp : 0<(spatialMetricConstant:ℝ)+1 := by positivity
    apply one_div_lt_one_div_of_lt hp
    linarith

def smoothSpatialDistance (L : Length) (A : Finset (Torus L)) : Torus L → ℝ :=
  torusMollify L spatialDistanceBump (spatialSiteDistance L A)

lemma smoothSpatialDistance_lipschitz (L : Length) (A : Finset (Torus L)) :
    LipschitzWith spatialMetricConstant (smoothSpatialDistance L A) :=
  torusMollify_lipschitz L _ (spatialSiteDistance_lipschitz L A)

lemma smoothSpatialDistance_approximation (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    |smoothSpatialDistance L A x-spatialSiteDistance L A x|≤1 := by
  apply (torusMollify_approximation L spatialDistanceBump (spatialSiteDistance_lipschitz L A) x).trans
  change (spatialMetricConstant:ℝ)*(1/((spatialMetricConstant:ℝ)+1))≤1
  rw [mul_one_div,(div_le_one (by positivity : 0<(spatialMetricConstant:ℝ)+1))]
  linarith

def spatialDistanceMultiplier (L : Length) (A : Finset (Torus L)) : SmoothMultiplier 1 L :=
  mollifiedSpatialMultiplier L spatialDistanceBump (spatialSiteDistance L A)
    (spatialSiteDistance_lipschitz L A).continuous

lemma spatialDistanceMultiplier_apply (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    (spatialDistanceMultiplier L A).toFun X=(smoothSpatialDistance L A (X 0):ℂ) := rfl

lemma spatialDistanceMultiplier_real (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    conj ((spatialDistanceMultiplier L A).toFun X)=(spatialDistanceMultiplier L A).toFun X := by
  rw [spatialDistanceMultiplier_apply,Complex.conj_ofReal]

lemma spatialDistanceMultiplier_partial_bound (L : Length) (A : Finset (Torus L))
    (p : Direction 1) (X : Configuration 1 L) :
    ‖coordDerivative 1 L (spatialDistanceMultiplier L A).toFun p X‖≤ spatialMetricConstant := by
  have hLip : LipschitzWith spatialMetricConstant
      (fun Y : LiftedConfiguration 1 ↦ (spatialDistanceMultiplier L A).toFun (project 1 L Y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro Y Z
    change dist ((smoothSpatialDistance L A (spatialProject L (Y 0))):ℂ)
      ((smoothSpatialDistance L A (spatialProject L (Z 0))):ℂ)≤_
    rw [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,←Real.dist_eq]
    apply ((smoothSpatialDistance_lipschitz L A).dist_le_mul _ _).trans
    apply mul_le_mul_of_nonneg_left _ spatialMetricConstant.coe_nonneg
    exact ((lipschitz_spatialProject L).dist_le_mul (Y 0) (Z 0)).trans
      (by simpa using dist_le_pi_dist Y Z 0)
  unfold coordDerivative
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hv : ‖(Pi.single p.1 (Pi.single p.2 (1:ℝ)) : LiftedConfiguration 1)‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases hi : i=p.1
    · subst i
      simp only [Pi.single_eq_same]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro j
      by_cases hj : j=p.2
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj]
    · simp [Pi.single_eq_of_ne hi]
  exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by
    simpa only [mul_one] using norm_fderiv_le_of_lipschitz ℝ hLip)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def spatialAngle (H t : ℝ) : ℝ := Real.pi/2*CellOrbital.profile 1 (t-H)
def spatialSine (H t : ℝ) : ℝ := Real.sin (spatialAngle H t)
def spatialCosine (H t : ℝ) : ℝ := Real.cos (spatialAngle H t)

lemma spatialAngle_smooth (H : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (spatialAngle H) :=
  contDiff_const.mul ((CellOrbital.profile_smooth 1).comp (contDiff_id.sub contDiff_const))
lemma spatialSine_smooth (H : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (spatialSine H) :=
  Real.contDiff_sin.comp (spatialAngle_smooth H)
lemma spatialCosine_smooth (H : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (spatialCosine H) :=
  Real.contDiff_cos.comp (spatialAngle_smooth H)

lemma spatialAngle_hasDerivAt (H t : ℝ) :
    HasDerivAt (spatialAngle H) (Real.pi/2*deriv (CellOrbital.profile 1) (t-H)) t := by
  have hd := (((CellOrbital.profile_smooth 1).differentiable (by simp)) (t-H)).hasDerivAt
  convert (hd.comp t ((hasDerivAt_id t).sub_const H)).const_mul (Real.pi/2) using 1 <;>
    first | rfl | simp only [mul_one]

lemma spatialSine_deriv (H t : ℝ) : deriv (spatialSine H) t=
    Real.cos (spatialAngle H t)*(Real.pi/2*deriv (CellOrbital.profile 1) (t-H)) :=
  (spatialAngle_hasDerivAt H t).sin.deriv
lemma spatialCosine_deriv (H t : ℝ) : deriv (spatialCosine H) t=
    -Real.sin (spatialAngle H t)*(Real.pi/2*deriv (CellOrbital.profile 1) (t-H)) :=
  (spatialAngle_hasDerivAt H t).cos.deriv

def spatialInside (L : Length) (A : Finset (Torus L)) (H : ℝ) : SmoothMultiplier 1 L :=
  (spatialDistanceMultiplier L A).realComp (spatialSine H) (spatialSine_smooth H)
def spatialOutside (L : Length) (A : Finset (Torus L)) (H : ℝ) : SmoothMultiplier 1 L :=
  (spatialDistanceMultiplier L A).realComp (spatialCosine H) (spatialCosine_smooth H)

lemma spatialInside_apply (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    (spatialInside L A H).toFun X=(spatialSine H (smoothSpatialDistance L A (X 0)):ℂ) := rfl
lemma spatialOutside_apply (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    (spatialOutside L A H).toFun X=(spatialCosine H (smoothSpatialDistance L A (X 0)):ℂ) := rfl
lemma spatialInside_real (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    conj ((spatialInside L A H).toFun X)=(spatialInside L A H).toFun X := by
  rw [spatialInside_apply,Complex.conj_ofReal]
lemma spatialOutside_real (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    conj ((spatialOutside L A H).toFun X)=(spatialOutside L A H).toFun X := by
  rw [spatialOutside_apply,Complex.conj_ofReal]

lemma spatialPartition_unity (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) :
    (spatialInside L A H).orbital x*(spatialInside L A H).orbital x+
      (spatialOutside L A H).orbital x*(spatialOutside L A H).orbital x=1 := by
  change (Real.sin (spatialAngle H (smoothSpatialDistance L A x)):ℂ)*
    (Real.sin (spatialAngle H (smoothSpatialDistance L A x)):ℂ)+
    (Real.cos (spatialAngle H (smoothSpatialDistance L A x)):ℂ)*
    (Real.cos (spatialAngle H (smoothSpatialDistance L A x)):ℂ)=1
  have h := Real.sin_sq_add_cos_sq (spatialAngle H (smoothSpatialDistance L A x))
  exact_mod_cast (show Real.sin (spatialAngle H (smoothSpatialDistance L A x))*
    Real.sin (spatialAngle H (smoothSpatialDistance L A x))+
    Real.cos (spatialAngle H (smoothSpatialDistance L A x))*Real.cos (spatialAngle H (smoothSpatialDistance L A x))=1 by nlinarith only [h])

lemma spatialInside_norm_le (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) :
    ‖(spatialInside L A H).orbital x‖≤1 := by
  change ‖(Real.sin (spatialAngle H (smoothSpatialDistance L A x)):ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

lemma spatialInside_one (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L)
    (hx : spatialSiteDistance L A x≤H) : (spatialInside L A H).orbital x=1 := by
  have hm := (abs_le.mp (smoothSpatialDistance_approximation L A x)).2
  have h : smoothSpatialDistance L A x-H≤1 := by linarith
  change (Real.sin (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A x-H)):ℂ)=1
  rw [CellOrbital.profile_one (by norm_num : (0:ℝ)<1) h,mul_one,Real.sin_pi_div_two,Complex.ofReal_one]

lemma spatialInside_zero (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L)
    (hx : H+3≤ spatialSiteDistance L A x) : (spatialInside L A H).orbital x=0 := by
  have hm := (abs_le.mp (smoothSpatialDistance_approximation L A x)).1
  have h : 2*1≤ smoothSpatialDistance L A x-H := by linarith
  change (Real.sin (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A x-H)):ℂ)=0
  rw [CellOrbital.profile_zero (by norm_num : (0:ℝ)<1) h,mul_zero,Real.sin_zero,Complex.ofReal_zero]

lemma spatialInside_partial (L : Length) (A : Finset (Torus L)) (H : ℝ)
    (p : Direction 1) (X : Configuration 1 L) :
    coordDerivative 1 L (spatialInside L A H).toFun p X=
      ((deriv (spatialSine H) (smoothSpatialDistance L A (X 0)):ℝ):ℂ)*
        coordDerivative 1 L (spatialDistanceMultiplier L A).toFun p X := by
  rw [spatialInside,SmoothMultiplier.partial_realComp _ _ _ (spatialDistanceMultiplier_real L A)]
  rfl
lemma spatialOutside_partial (L : Length) (A : Finset (Torus L)) (H : ℝ)
    (p : Direction 1) (X : Configuration 1 L) :
    coordDerivative 1 L (spatialOutside L A H).toFun p X=
      ((deriv (spatialCosine H) (smoothSpatialDistance L A (X 0)):ℝ):ℂ)*
        coordDerivative 1 L (spatialDistanceMultiplier L A).toFun p X := by
  rw [spatialOutside,SmoothMultiplier.partial_realComp _ _ _ (spatialDistanceMultiplier_real L A)]
  rfl

lemma spatialPartition_partial_zero (L : Length) (A : Finset (Torus L)) (H : ℝ)
    (p : Direction 1) (X : Configuration 1 L) (hx : H+3<spatialSiteDistance L A (X 0)) :
    coordDerivative 1 L (spatialInside L A H).toFun p X=0 ∧
      coordDerivative 1 L (spatialOutside L A H).toFun p X=0 := by
  have hm := (abs_le.mp (smoothSpatialDistance_approximation L A (X 0))).1
  have hz : deriv (CellOrbital.profile 1) (smoothSpatialDistance L A (X 0)-H)=0 :=
    CellOrbital.profile_deriv_zero (by norm_num) (by intro hh; have := hh.2; linarith)
  rw [spatialInside_partial,spatialOutside_partial,spatialSine_deriv,spatialCosine_deriv,hz]
  simp

theorem spatialPartition_partial_bound : ∃ B : ℝ, 0<B ∧
    ∀ (L : Length) (A : Finset (Torus L)) (H : ℝ) (p : Direction 1) (X : Configuration 1 L),
      ‖coordDerivative 1 L (spatialInside L A H).toFun p X‖≤B ∧
      ‖coordDerivative 1 L (spatialOutside L A H).toFun p X‖≤B := by
  obtain ⟨M,hM,hb⟩ := PeriodicCutoff.exists_transition_bound
  let B := Real.pi/2*M*(spatialMetricConstant:ℝ)
  refine ⟨B,by dsimp [B]; exact mul_pos (mul_pos (div_pos Real.pi_pos (by norm_num)) hM) spatialMetricConstant_pos,?_⟩
  intro L A H p X
  have ht := CellOrbital.profile_deriv_bound (h:=1) (by norm_num) hM.le hb (smoothSpatialDistance L A (X 0)-H)
  simp only [div_one] at ht
  have hd := spatialDistanceMultiplier_partial_bound L A p X
  have hs : |deriv (spatialSine H) (smoothSpatialDistance L A (X 0))|≤Real.pi/2*M := by
    rw [spatialSine_deriv,abs_mul,abs_mul,abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (mul_nonneg (by positivity) (abs_nonneg _))).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_left ht (by positivity : 0≤Real.pi/2))
  have hc : |deriv (spatialCosine H) (smoothSpatialDistance L A (X 0))|≤Real.pi/2*M := by
    rw [spatialCosine_deriv,abs_mul,abs_neg,abs_mul,abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (mul_nonneg (by positivity) (abs_nonneg _))).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_left ht (by positivity : 0≤Real.pi/2))
  rw [spatialInside_partial,spatialOutside_partial,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  exact ⟨mul_le_mul hs hd (norm_nonneg _) (by positivity),mul_le_mul hc hd (norm_nonneg _) (by positivity)⟩

end HardSphere

end

end OAI
