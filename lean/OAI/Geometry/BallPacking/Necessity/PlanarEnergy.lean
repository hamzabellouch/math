import Mathlib
import OAI.Geometry.BallPacking.Necessity.AffineEnergy

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

def phaseEuclidean (n : ℕ) : Phase n ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm

def euclideanNorm {n : ℕ} (v : Phase n) : ℝ := ‖phaseEuclidean n v‖

@[simp] theorem euclideanNorm_sq {n : ℕ} (v : Phase n) :
    (euclideanNorm v)^2 = stdDot n v v := by
  simp only [euclideanNorm,phaseEuclidean,PiLp.continuousLinearEquiv_symm_apply,
    EuclideanSpace.norm_sq_eq, stdDot_apply, ←Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]

theorem euclideanNorm_nonneg {n : ℕ} (v : Phase n) : 0 ≤ euclideanNorm v := norm_nonneg _

theorem euclideanNorm_add_le {n : ℕ} (v w : Phase n) :
    euclideanNorm (v+w) ≤ euclideanNorm v + euclideanNorm w := by
  simpa only [euclideanNorm,map_add] using norm_add_le (phaseEuclidean n v) (phaseEuclidean n w)

theorem standardForm_abs_le {n : ℕ} (v w : Phase n) :
    |standardForm v w| ≤ euclideanNorm v * euclideanNorm w := by
  have h := stdDot_standardForm_sq_le v w
  have hp := sq_nonneg (stdDot n v w)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))).mp
  rw [sq_abs,mul_pow,euclideanNorm_sq,euclideanNorm_sq]
  linarith

theorem standard_graph_energy_smul {n : ℕ} (A : End n) (v : Phase n) (a : ℝ) :
    stdDot n (a • v) (a • v) + stdDot n (A (a • v)) (A (a • v)) =
      a^2 * (stdDot n v v + stdDot n (A v) (A v)) := by
  rw [A.map_smul,stdDot_self_smul,stdDot_self_smul]
  ring

theorem standard_graph_area_smul {n : ℕ} (A : End n) (v : Phase n) (a : ℝ) :
    standardForm (a • v) (A (a • v)) = a^2 * standardForm v (A v) := by
  simp only [A.map_smul,←stdOmega_apply,map_smul,smul_apply,smul_eq_mul]
  ring

theorem homotopy_standard_graph_continuousOn {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) :
    ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      (stdDot n y.2 y.2 + stdDot n (lineHomotopy J y.1.1 y.1.2 y.2)
          (lineHomotopy J y.1.1 y.1.2 y.2)) /
        standardForm y.2 (lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ (Metric.sphere (0:Phase n) 1)) := by
  have hj : ContinuousOn (fun y : (ℝ × Phase n) × Phase n => lineHomotopy J y.1.1 y.1.2)
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ (Metric.sphere (0:Phase n) 1)) :=
    (lineHomotopy_smooth hJs hJ).continuousOn.comp continuous_fst.continuousOn
      (fun y hy => hy.1)
  have hv := hj.clm_apply continuous_snd.continuousOn
  have he : ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      stdDot n y.2 y.2 + stdDot n (lineHomotopy J y.1.1 y.1.2 y.2)
          (lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ (Metric.sphere (0:Phase n) 1)) :=
    (((stdDot n).continuous.comp continuous_snd).clm_apply continuous_snd).continuousOn.add
      (((stdDot n).continuous.comp_continuousOn hv).clm_apply hv)
  have hd : ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      standardForm y.2 (lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ (Metric.sphere (0:Phase n) 1)) := by
    simpa only [stdOmega_apply,Function.comp_apply] using
      (((stdOmega n).continuous.comp continuous_snd).continuousOn.clm_apply hv)
  apply he.div hd
  intro y hy
  have hv0 : y.2 ≠ 0 := by
    intro hz
    have h := hy.2
    simp [hz] at h
  exact (lineHomotopy_compatible hJ hy.1.1 _).2.2 _ hv0 |>.ne'

theorem homotopy_standard_unit_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ tsupport (fun x => J x-standardJ n),
      ∀ v : Phase n, ‖v‖ = 1 →
      stdDot n v v + stdDot n (lineHomotopy J t x v) (lineHomotopy J t x v) ≤
        C * standardForm v (lineHomotopy J t x v) := by
  let K := tsupport (fun x => J x-standardJ n)
  let L := ((Icc (0:ℝ) 1) ×ˢ K) ×ˢ Metric.sphere (0:Phase n) 1
  let f (y : (ℝ × Phase n) × Phase n) :=
    (stdDot n y.2 y.2 + stdDot n (lineHomotopy J y.1.1 y.1.2 y.2)
      (lineHomotopy J y.1.1 y.1.2 y.2)) / standardForm y.2 (lineHomotopy J y.1.1 y.1.2 y.2)
  have hL : IsCompact L := (isCompact_Icc.prod hc).prod (isCompact_sphere _ _)
  have hcont : ContinuousOn f L :=
    (homotopy_standard_graph_continuousOn hJs hJ).mono (fun y hy => ⟨⟨hy.1.1,mem_univ _⟩,hy.2⟩)
  obtain ⟨C,hC,hCb⟩ := (hL.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro t ht x hx v hv
  have hl : ((t,x),v) ∈ L := ⟨⟨ht,hx⟩,by simpa [Metric.mem_sphere,dist_zero_right] using hv⟩
  have hv0 : v ≠ 0 := fun hh => by simp [hh] at hv
  have hp := (lineHomotopy_compatible hJ ht x).2.2 v hv0
  apply (div_le_iff₀ hp).mp
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hCb _ (mem_image_of_mem f hl))

theorem homotopy_standard_energy_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ x v : Phase n,
      stdDot n v v + stdDot n (lineHomotopy J t x v) (lineHomotopy J t x v) ≤
        C * standardForm v (lineHomotopy J t x v) := by
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_unit_bound hJs hJ hc
  refine ⟨max C 2, lt_max_of_lt_left hC, ?_⟩
  intro t ht x v
  have hpos : 0 ≤ standardForm v (lineHomotopy J t x v) := by
    by_cases hv : v = 0
    · simp [hv,standardForm]
    · exact ((lineHomotopy_compatible hJ ht x).2.2 v hv).le
  by_cases hx : x ∈ tsupport (fun x => J x-standardJ n)
  · by_cases hv : v = 0
    · simp [hv,standardForm]
    have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hh := hCb t ht x hx _ hw
    rw [standard_graph_energy_smul,standard_graph_area_smul] at hh
    have hs : 0 < (‖v‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv))
    have hb : stdDot n v v + stdDot n (lineHomotopy J t x v) (lineHomotopy J t x v) ≤
        C * standardForm v (lineHomotopy J t x v) := by nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
  · have he : lineHomotopy J t x = standardJ n := by
      apply sub_eq_zero.mp
      apply image_eq_zero_of_notMem_tsupport (f := fun y => lineHomotopy J t y-standardJ n)
      exact fun hy => hx (lineHomotopy_support J ht hy)
    rw [he]
    have hi : stdDot n (standardJ n v) (standardJ n v) = stdDot n v v := by
      simp only [← standardForm_J_right]
      exact (compatible_standardJ n).2.1 v (standardJ n v)
    rw [hi,standardForm_J_right]
    nlinarith [stdDot_nonneg v,le_max_right C (2:ℝ)]

 
theorem interval_integral_sq_le {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x)^2 ≤ (b-a) * (∫ x in a..b, (f x)^2) := by
  rcases hab.eq_or_lt with h | h
  · subst b; simp
  let m : ℝ := (∫ x in a..b, f x) / (b-a)
  have hm : (b-a)*m = ∫ x in a..b, f x := by
    dsimp [m]
    field_simp
  have he : (∫ x in a..b, (f x-m)^2) =
      (∫ x in a..b, (f x)^2) - 2*m*(∫ x in a..b, f x) + (b-a)*m^2 := by
    have hfun : (fun x => (f x-m)^2) = (fun x => (f x)^2 - (2*m)*f x + m^2) := by
      funext x; ring
    have hfi : IntervalIntegrable (fun x => (f x)^2) volume a b := (hf.pow 2).intervalIntegrable _ _
    have hgi : IntervalIntegrable (fun x => (2*m)*f x) volume a b :=
      (hf.const_mul (2*m)).intervalIntegrable _ _
    have hci : IntervalIntegrable (fun _ : ℝ => m^2) volume a b :=
      continuous_const.intervalIntegrable _ _
    rw [hfun, intervalIntegral.integral_add (hfi.sub hgi) hci,
      intervalIntegral.integral_sub hfi hgi,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
    simp only [smul_eq_mul]
  have hp := intervalIntegral.integral_nonneg (μ := volume) h.le (fun x _ => sq_nonneg (f x-m))
  rw [he] at hp
  nlinarith [mul_nonneg (sub_pos.mpr h).le hp]

theorem euclidean_displacement_le_integral {n : ℕ} {v v' : ℝ → Phase n}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hd : Continuous v')
    {a b : ℝ} (hab : a ≤ b) :
    euclideanNorm (v b-v a) ≤ ∫ x in a..b, euclideanNorm (v' x) := by
  have hdu (x : ℝ) : HasDerivAt (fun t => phaseEuclidean n (v t)) (phaseEuclidean n (v' x)) x :=
    (phaseEuclidean n).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x (hv x)
  have hi : IntervalIntegrable (fun x => phaseEuclidean n (v' x)) volume a b :=
    ((phaseEuclidean n).continuous.comp hd).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdu x) hi
  have hb := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun x => phaseEuclidean n (v' x)) hab
  rw [he] at hb
  simpa only [euclideanNorm,map_sub] using hb

def planarDirichlet {n : ℕ} (v : Plane → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ v z (1,0)) (fderiv ℝ v z (1,0)) +
  stdDot n (fderiv ℝ v z (0,1)) (fderiv ℝ v z (0,1))

def horizontalSpeed {n : ℕ} (v : Plane → Phase n) (y x : ℝ) : ℝ :=
  euclideanNorm (fderiv ℝ v (x,y) (1,0))

def verticalSpeed {n : ℕ} (v : Plane → Phase n) (x y : ℝ) : ℝ :=
  euclideanNorm (fderiv ℝ v (x,y) (0,1))

theorem planar_partial_continuous {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (e : Plane) : Continuous (fun z => fderiv ℝ v z e) :=
  ((hv.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).clm_apply contDiff_const).continuous

theorem euclideanNorm_continuous {n : ℕ} : Continuous (@euclideanNorm n) :=
  (phaseEuclidean n).continuous.norm

theorem horizontalSpeed_continuous {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (y : ℝ) : Continuous (horizontalSpeed v y) :=
  euclideanNorm_continuous.comp ((planar_partial_continuous hv (1,0)).comp
    (continuous_id.prodMk continuous_const))

theorem verticalSpeed_continuous {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (x : ℝ) : Continuous (verticalSpeed v x) :=
  euclideanNorm_continuous.comp ((planar_partial_continuous hv (0,1)).comp
    (continuous_const.prodMk continuous_id))

theorem horizontal_displacement_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    euclideanNorm (v (b,y)-v (a,y)) ≤ ∫ x in a..b, horizontalSpeed v y x := by
  apply euclidean_displacement_le_integral _ _ hab
  · intro x
    exact (hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  · exact (planar_partial_continuous hv (1,0)).comp (continuous_id.prodMk continuous_const)

theorem vertical_displacement_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    euclideanNorm (v (x,b)-v (x,a)) ≤ ∫ y in a..b, verticalSpeed v x y := by
  apply euclidean_displacement_le_integral _ _ hab
  · intro y
    exact (hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  · exact (planar_partial_continuous hv (0,1)).comp (continuous_const.prodMk continuous_id)

def rectangleBoundaryLength {n : ℕ} (v : Plane → Phase n) (a b : Plane) : ℝ :=
  (∫ x in a.1..b.1, horizontalSpeed v a.2 x) +
  (∫ x in a.1..b.1, horizontalSpeed v b.2 x) +
  (∫ y in a.2..b.2, verticalSpeed v a.1 y) +
  (∫ y in a.2..b.2, verticalSpeed v b.1 y)

theorem rectangleBoundaryLength_nonneg {n : ℕ} (v : Plane → Phase n) {a b : Plane}
    (hab : a ≤ b) : 0 ≤ rectangleBoundaryLength v a b := by
  apply add_nonneg (add_nonneg (add_nonneg _ _) _) _
  · exact intervalIntegral.integral_nonneg hab.1 (fun _ _ => euclideanNorm_nonneg _)
  · exact intervalIntegral.integral_nonneg hab.1 (fun _ _ => euclideanNorm_nonneg _)
  · exact intervalIntegral.integral_nonneg hab.2 (fun _ _ => euclideanNorm_nonneg _)
  · exact intervalIntegral.integral_nonneg hab.2 (fun _ _ => euclideanNorm_nonneg _)

 
theorem planar_stokes_rectangle {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, planarCurl β z) =
      (∫ x in a.1..b.1, β (x,a.2) (1,0)) -
      (∫ x in a.1..b.1, β (x,b.2) (1,0)) +
      (∫ y in a.2..b.2, β (b.1,y) (0,1)) -
      (∫ y in a.2..b.2, β (a.1,y) (0,1)) := by
  have hf : ContDiff ℝ ∞ (fun z => β z (0,1)) := hβ.clm_apply contDiff_const
  have hg : ContDiff ℝ ∞ (fun z => -(β z (1,0))) := (hβ.clm_apply contDiff_const).neg
  have hdf (z : Plane) : HasFDerivAt (fun w => β w (0,1))
      ((fderiv ℝ β z).flip (0,1)) z := by
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      fderiv_const_apply,add_apply,zero_apply,
      map_zero,ContinuousLinearMap.comp_zero,zero_add] using
      ((hβ.differentiable (by simp) z).hasFDerivAt.clm_apply (hasFDerivAt_const (0,1) z))
  have hdg (z : Plane) : HasFDerivAt (fun w => -(β w (1,0)))
      (-((fderiv ℝ β z).flip (1,0))) z := by
    have hh : HasFDerivAt (fun w => β w (1,0)) ((fderiv ℝ β z).flip (1,0)) z := by
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
        fderiv_const_apply,add_apply,zero_apply,
        map_zero,ContinuousLinearMap.comp_zero,zero_add] using
        ((hβ.differentiable (by simp) z).hasFDerivAt.clm_apply (hasFDerivAt_const (1,0) z))
    exact hh.neg
  have hi : IntegrableOn (planarCurl β) (Icc a b) :=
    (planarCurl_contDiff hβ).continuous.continuousOn.integrableOn_Icc
  change IntegrableOn (fun z => fderiv ℝ β z (1,0) (0,1) - fderiv ℝ β z (0,1) (1,0)) (Icc a b) at hi
  have he := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fun z => β z (0,1)) (fun z => -(β z (1,0)))
    (fun z => (fderiv ℝ β z).flip (0,1)) (fun z => -((fderiv ℝ β z).flip (1,0)))
    a b hab hf.continuous.continuousOn hg.continuous.continuousOn
    (fun z _ => hdf z) (fun z _ => hdg z) (by simpa only [ContinuousLinearMap.flip_apply,neg_apply,sub_eq_add_neg] using hi)
  simp only [ContinuousLinearMap.flip_apply,neg_apply,
    ←sub_eq_add_neg,intervalIntegral.integral_neg] at he
  change (∫ z in Icc a b, planarCurl β z) = _ at he
  rw [he]
  ring

def translatedPlanarPrimitive {n : ℕ} (v : Plane → Phase n) (c : Phase n) :
    Plane → Plane →L[ℝ] ℝ := planarPullback (fun z => v z-c) stdPrimitive

theorem translatedPlanarPrimitive_smooth {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (c : Phase n) :
    ContDiff ℝ ∞ (translatedPlanarPrimitive v c) :=
  planarPullback_smooth (hv.sub contDiff_const) (stdPrimitive_smooth n)

theorem translatedPlanarPrimitive_apply {n : ℕ} (v : Plane → Phase n)
    (c : Phase n) (z e : Plane) :
    translatedPlanarPrimitive v c z e =
      (1/2:ℝ) * standardForm (v z-c) (fderiv ℝ v z e) := by
  simp only [translatedPlanarPrimitive,planarPullback,stdPrimitive,
    ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,
    stdOmega_apply,fderiv_sub_const]

theorem translatedPlanarPrimitive_curl {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (c : Phase n) (z : Plane) :
    planarCurl (translatedPlanarPrimitive v c) z =
      standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)) := by
  rw [translatedPlanarPrimitive,planarPullback_curl (hv.sub contDiff_const)
    (stdPrimitive_smooth n),stdPrimitive_extDeriv,fderiv_sub_const]

theorem rectangle_boundary_displacement {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : Plane} (hab : a ≤ b) :
    (∀ x ∈ Icc a.1 b.1, euclideanNorm (v (x,a.2)-v a) ≤ rectangleBoundaryLength v a b) ∧
    (∀ x ∈ Icc a.1 b.1, euclideanNorm (v (x,b.2)-v a) ≤ rectangleBoundaryLength v a b) ∧
    (∀ y ∈ Icc a.2 b.2, euclideanNorm (v (a.1,y)-v a) ≤ rectangleBoundaryLength v a b) ∧
    (∀ y ∈ Icc a.2 b.2, euclideanNorm (v (b.1,y)-v a) ≤ rectangleBoundaryLength v a b) := by
  have hpH (y : ℝ) : 0 ≤ ∫ x in a.1..b.1, horizontalSpeed v y x :=
    intervalIntegral.integral_nonneg hab.1 (fun _ _ => euclideanNorm_nonneg _)
  have hpV (x : ℝ) : 0 ≤ ∫ y in a.2..b.2, verticalSpeed v x y :=
    intervalIntegral.integral_nonneg hab.2 (fun _ _ => euclideanNorm_nonneg _)
  have hH (y : ℝ) (x : ℝ) (hx : x ∈ Icc a.1 b.1) :
      euclideanNorm (v (x,y)-v (a.1,y)) ≤ ∫ t in a.1..b.1, horizontalSpeed v y t := by
    refine (horizontal_displacement_bound hv hx.1 y).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall fun _ => euclideanNorm_nonneg _)
      ((horizontalSpeed_continuous hv y).intervalIntegrable _ _)
  have hV (x : ℝ) (y : ℝ) (hy : y ∈ Icc a.2 b.2) :
      euclideanNorm (v (x,y)-v (x,a.2)) ≤ ∫ t in a.2..b.2, verticalSpeed v x t := by
    refine (vertical_displacement_bound hv hy.1 x).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
      (Filter.Eventually.of_forall fun _ => euclideanNorm_nonneg _)
      ((verticalSpeed_continuous hv x).intervalIntegrable _ _)
  have htri (w u z : Phase n) : euclideanNorm (w-z) ≤ euclideanNorm (w-u)+euclideanNorm (u-z) := by
    simpa only [sub_add_sub_cancel] using euclideanNorm_add_le (w-u) (u-z)
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    have hh := hH a.2 x hx
    change euclideanNorm (v (x,a.2)-v a) ≤ _ at hh
    unfold rectangleBoundaryLength
    linarith [hpH b.2,hpV a.1,hpV b.1]
  · intro x hx
    have hh := htri (v (x,b.2)) (v (a.1,b.2)) (v a)
    have h1 := hH b.2 x hx
    have h2 := hV a.1 b.2 ⟨hab.2,le_rfl⟩
    change euclideanNorm (v (a.1,b.2)-v a) ≤ _ at h2
    unfold rectangleBoundaryLength
    linarith [hpH a.2,hpV b.1]
  · intro y hy
    have hh := hV a.1 y hy
    change euclideanNorm (v (a.1,y)-v a) ≤ _ at hh
    unfold rectangleBoundaryLength
    linarith [hpH a.2,hpH b.2,hpV b.1]
  · intro y hy
    have hh := htri (v (b.1,y)) (v (b.1,a.2)) (v a)
    have h1 := hV b.1 y hy
    have h2 := hH a.2 b.1 ⟨hab.1,le_rfl⟩
    change euclideanNorm (v (b.1,a.2)-v a) ≤ _ at h2
    unfold rectangleBoundaryLength
    linarith [hpH b.2,hpV a.1]

 
theorem standard_area_rectangle_le_length_sq {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) ≤
      (1/2:ℝ) * (rectangleBoundaryLength v a b)^2 := by
  let β := translatedPlanarPrimitive v (v a)
  let L := rectangleBoundaryLength v a b
  have hβ := translatedPlanarPrimitive_smooth hv (v a)
  have hcurl : (fun z => standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) =
      planarCurl β := by
    funext z
    exact (translatedPlanarPrimitive_curl hv (v a) z).symm
  rw [hcurl,planar_stokes_rectangle hβ hab]
  have hbd := rectangle_boundary_displacement hv hab
  have hbound (l r : ℝ) (c : ℝ → Plane) (e : Plane) (hc : Continuous c)
      (he : Continuous (fun t => euclideanNorm (fderiv ℝ v (c t) e)))
      (hlr : l ≤ r) (hd : ∀ t ∈ Icc l r, euclideanNorm (v (c t)-v a) ≤ L) :
      |∫ t in l..r, β (c t) e| ≤ (1/2:ℝ)*L*(∫ t in l..r, euclideanNorm (fderiv ℝ v (c t) e)) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hlr).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hlr
    · exact (((hβ.continuous.comp hc).clm_apply continuous_const).abs).intervalIntegrable _ _
    · exact (he.const_mul _).intervalIntegrable _ _
    intro t ht
    rw [translatedPlanarPrimitive_apply,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    calc
      (1/2:ℝ) * |standardForm (v (c t)-v a) (fderiv ℝ v (c t) e)| ≤
          (1/2:ℝ)*(euclideanNorm (v (c t)-v a)*euclideanNorm (fderiv ℝ v (c t) e)) :=
        mul_le_mul_of_nonneg_left (standardForm_abs_le _ _) (by norm_num)
      _ ≤ (1/2:ℝ)*(L*euclideanNorm (fderiv ℝ v (c t) e)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hd t ht) (euclideanNorm_nonneg _)) (by norm_num)
      _ = _ := by ring
  have h0 := hbound a.1 b.1 (fun x => (x,a.2)) (1,0)
    (continuous_id.prodMk continuous_const) (horizontalSpeed_continuous hv a.2) hab.1 hbd.1
  have h1 := hbound a.1 b.1 (fun x => (x,b.2)) (1,0)
    (continuous_id.prodMk continuous_const) (horizontalSpeed_continuous hv b.2) hab.1 hbd.2.1
  have h2 := hbound a.2 b.2 (fun y => (a.1,y)) (0,1)
    (continuous_const.prodMk continuous_id) (verticalSpeed_continuous hv a.1) hab.2 hbd.2.2.1
  have h3 := hbound a.2 b.2 (fun y => (b.1,y)) (0,1)
    (continuous_const.prodMk continuous_id) (verticalSpeed_continuous hv b.1) hab.2 hbd.2.2.2
  have hh0 := le_abs_self (∫ x in a.1..b.1, β (x,a.2) (1,0))
  have hh1 := neg_le_abs (∫ x in a.1..b.1, β (x,b.2) (1,0))
  have hh2 := neg_le_abs (∫ y in a.2..b.2, β (a.1,y) (0,1))
  have hh3 := le_abs_self (∫ y in a.2..b.2, β (b.1,y) (0,1))
  change _ ≤ (1/2:ℝ)*L^2
  have hL : L = (∫ x in a.1..b.1, euclideanNorm (fderiv ℝ v (x,a.2) (1,0))) +
      (∫ x in a.1..b.1, euclideanNorm (fderiv ℝ v (x,b.2) (1,0))) +
      (∫ y in a.2..b.2, euclideanNorm (fderiv ℝ v (a.1,y) (0,1))) +
      (∫ y in a.2..b.2, euclideanNorm (fderiv ℝ v (b.1,y) (0,1))) := rfl
  dsimp only [β] at h0 h1 h2 h3 hh0 hh1 hh2 hh3
  nlinarith [congrArg (fun x : ℝ => L*x) hL]

theorem planarDirichlet_nonneg {n : ℕ} (v : Plane → Phase n) (z : Plane) :
    0 ≤ planarDirichlet v z := add_nonneg (stdDot_nonneg _) (stdDot_nonneg _)

theorem planarDirichlet_continuous {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) : Continuous (planarDirichlet v) := by
  have hx := planar_partial_continuous hv (1,0)
  have hy := planar_partial_continuous hv (0,1)
  exact (((stdDot n).continuous.comp hx).clm_apply hx).add
    (((stdDot n).continuous.comp hy).clm_apply hy)

def rectangleBoundaryEnergy {n : ℕ} (v : Plane → Phase n) (a b : Plane) : ℝ :=
  (∫ x in a.1..b.1, planarDirichlet v (x,a.2)) +
  (∫ x in a.1..b.1, planarDirichlet v (x,b.2)) +
  (∫ y in a.2..b.2, planarDirichlet v (a.1,y)) +
  (∫ y in a.2..b.2, planarDirichlet v (b.1,y))

theorem rectangleBoundaryLength_sq_le {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : Plane} (hab : a ≤ b)
    {d : ℝ} (h1 : b.1-a.1 ≤ d) (h2 : b.2-a.2 ≤ d) :
    (rectangleBoundaryLength v a b)^2 ≤ 4*d*rectangleBoundaryEnergy v a b := by
  have hH (y : ℝ) : (∫ x in a.1..b.1, horizontalSpeed v y x)^2 ≤
      d * (∫ x in a.1..b.1, planarDirichlet v (x,y)) := by
    refine (interval_integral_sq_le (horizontalSpeed_continuous hv y) hab.1).trans ?_
    have hi : (∫ x in a.1..b.1, (horizontalSpeed v y x)^2) ≤
        ∫ x in a.1..b.1, planarDirichlet v (x,y) := by
      apply intervalIntegral.integral_mono_on hab.1
        (((horizontalSpeed_continuous hv y).pow 2).intervalIntegrable _ _)
        (((planarDirichlet_continuous hv).comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
      intro x hx
      change (euclideanNorm (fderiv ℝ v (x,y) (1,0)))^2 ≤
        stdDot n (fderiv ℝ v (x,y) (1,0)) (fderiv ℝ v (x,y) (1,0)) +
          stdDot n (fderiv ℝ v (x,y) (0,1)) (fderiv ℝ v (x,y) (0,1))
      rw [euclideanNorm_sq]
      exact le_add_of_nonneg_right (stdDot_nonneg _)
    calc
      (b.1-a.1) * (∫ x in a.1..b.1, (horizontalSpeed v y x)^2) ≤
          (b.1-a.1) * (∫ x in a.1..b.1, planarDirichlet v (x,y)) :=
        mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab.1)
      _ ≤ d * (∫ x in a.1..b.1, planarDirichlet v (x,y)) :=
        mul_le_mul_of_nonneg_right h1 (intervalIntegral.integral_nonneg hab.1 (fun _ _ => planarDirichlet_nonneg _ _))
  have hV (x : ℝ) : (∫ y in a.2..b.2, verticalSpeed v x y)^2 ≤
      d * (∫ y in a.2..b.2, planarDirichlet v (x,y)) := by
    refine (interval_integral_sq_le (verticalSpeed_continuous hv x) hab.2).trans ?_
    have hi : (∫ y in a.2..b.2, (verticalSpeed v x y)^2) ≤
        ∫ y in a.2..b.2, planarDirichlet v (x,y) := by
      apply intervalIntegral.integral_mono_on hab.2
        (((verticalSpeed_continuous hv x).pow 2).intervalIntegrable _ _)
        (((planarDirichlet_continuous hv).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      intro y hy
      change (euclideanNorm (fderiv ℝ v (x,y) (0,1)))^2 ≤
        stdDot n (fderiv ℝ v (x,y) (1,0)) (fderiv ℝ v (x,y) (1,0)) +
          stdDot n (fderiv ℝ v (x,y) (0,1)) (fderiv ℝ v (x,y) (0,1))
      rw [euclideanNorm_sq]
      exact le_add_of_nonneg_left (stdDot_nonneg _)
    calc
      (b.2-a.2) * (∫ y in a.2..b.2, (verticalSpeed v x y)^2) ≤
          (b.2-a.2) * (∫ y in a.2..b.2, planarDirichlet v (x,y)) :=
        mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab.2)
      _ ≤ d * (∫ y in a.2..b.2, planarDirichlet v (x,y)) :=
        mul_le_mul_of_nonneg_right h2 (intervalIntegral.integral_nonneg hab.2 (fun _ _ => planarDirichlet_nonneg _ _))
  let l0 := ∫ x in a.1..b.1, horizontalSpeed v a.2 x
  let l1 := ∫ x in a.1..b.1, horizontalSpeed v b.2 x
  let l2 := ∫ y in a.2..b.2, verticalSpeed v a.1 y
  let l3 := ∫ y in a.2..b.2, verticalSpeed v b.1 y
  have hs : (l0+l1+l2+l3)^2 ≤ 4*(l0^2+l1^2+l2^2+l3^2) := by
    nlinarith [sq_nonneg (l0-l1),sq_nonneg (l0-l2),sq_nonneg (l0-l3),
      sq_nonneg (l1-l2),sq_nonneg (l1-l3),sq_nonneg (l2-l3)]
  apply hs.trans
  dsimp only [l0,l1,l2,l3,rectangleBoundaryEnergy]
  nlinarith [hH a.2,hH b.2,hV a.1,hV b.1]

theorem standard_area_rectangle_le_boundaryEnergy {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : Plane} (hab : a ≤ b)
    {d : ℝ} (h1 : b.1-a.1 ≤ d) (h2 : b.2-a.2 ≤ d) :
    (∫ z in Icc a b, standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) ≤
      2*d*rectangleBoundaryEnergy v a b := by
  have hh := standard_area_rectangle_le_length_sq hv hab
  have he := rectangleBoundaryLength_sq_le hv hab h1 h2
  linarith

end HigherDimensionalBallPacking.Rigidity

end

end OAI
