import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.ChordLift
import OAI.Analysis.HardSphere.Operators.TransitionDerivative

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
namespace PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

abbrev ThreeTorus := Fin 3 → AddCircle L

def box (R : ℝ) (x : ThreeTorus L) : Set (ThreeTorus L) :=
  Set.univ.pi (fun j ↦ Metric.closedBall (x j) R)

omit hL in
lemma box_measurable (R : ℝ) (x : ThreeTorus L) : MeasurableSet (box L R x) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_closedBall)

lemma box_volume_le {R : ℝ} (hR : 0≤R) (x : ThreeTorus L) :
    volume.real (box L R x)≤(2*R)^3 := by
  have he : volume (box L R x)=ENNReal.ofReal (min L (2*R))^3 := by
    rw [volume_pi,box,Measure.pi_pi]
    simp_rw [AddCircle.volume_closedBall]
    simp
  rw [measureReal_def,he,ENNReal.toReal_pow,ENNReal.toReal_ofReal
    (le_min hL.out.le (mul_nonneg (by norm_num) hR))]
  exact pow_le_pow_left₀ (le_min hL.out.le (mul_nonneg (by norm_num) hR)) (min_le_right _ _) 3

def pairQ (y x : ThreeTorus L) : ℝ := ∑ j : Fin 3, chord L (y j-x j)

def qLift (z : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, chordLift L (z j)

lemma pairQ_continuous : Continuous (fun p : ThreeTorus L × ThreeTorus L ↦ pairQ L p.1 p.2) := by
  unfold pairQ
  apply continuous_finsetSum
  intro j _
  exact (chord_continuous L).comp (by fun_prop)

@[simp] lemma pairQ_coe (y x : Fin 3 → ℝ) :
    pairQ L (fun j ↦ (y j : AddCircle L)) (fun j ↦ (x j : AddCircle L))=qLift L (y-x) := by
  unfold pairQ qLift
  apply Finset.sum_congr rfl
  intro j _
  change chord L ((y j : AddCircle L)-(x j : AddCircle L))=chordLift L (y j-x j)
  have he : ((y j-x j : ℝ) : AddCircle L)=(y j : AddCircle L)-(x j : AddCircle L) :=
    map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples L)) _ _
  rw [← he,chord_coe]

lemma pairQ_nonneg (y x : ThreeTorus L) : 0≤pairQ L y x :=
  Finset.sum_nonneg fun j _ ↦ chord_nonneg L (y j-x j)

lemma pairQ_le (y x : ThreeTorus L) : pairQ L y x≤∑ j : Fin 3,dist (y j) (x j)^2 := by
  apply Finset.sum_le_sum
  intro j _
  simpa only [dist_eq_norm] using chord_le_norm_sq L (y j-x j)

lemma not_mem_box_pairQ {r : ℝ} (hr : 0<r) {y x : ThreeTorus L}
    (hx : y∉box L (Real.pi*r) x) : 4*r^2<pairQ L y x := by
  obtain ⟨j,hj⟩ : ∃ j, Real.pi*r<dist (y j) (x j) := by
    by_contra! hn
    exact hx (by simpa only [box,Set.mem_univ_pi,Metric.mem_closedBall] using hn)
  have hq := norm_sq_le_chord L (y j-x j)
  have hs : chord L (y j-x j)≤pairQ L y x :=
    Finset.single_le_sum (fun i _ ↦ chord_nonneg L (y i-x i)) (Finset.mem_univ j)
  rw [← dist_eq_norm] at hq
  have hd2 : (Real.pi*r)^2<dist (y j) (x j)^2 :=
    (sq_lt_sq₀ (mul_nonneg Real.pi_pos.le hr.le) dist_nonneg).mpr hj
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.pi/2)),sq_pos_of_pos Real.pi_pos]

def angle (r : ℝ) (y x : ThreeTorus L) : ℝ :=
  Real.pi/2*Real.smoothTransition ((pairQ L y x-2*r^2)/(2*r^2))

def angleLift (r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  Real.pi/2*Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2))

omit hL in
lemma angleLift_smooth (r : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (angleLift L r) := by
  have hq : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (qLift L) := by
    apply ContDiff.sum
    intro j _
    exact (chordLift_smooth L).comp (contDiff_apply ℝ ℝ j)
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((hq.sub contDiff_const).div_const _))

lemma angle_bounds (r : ℝ) (y x : ThreeTorus L) : 0≤angle L r y x ∧ angle L r y x≤Real.pi/2 := by
  constructor
  · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg _)
  · simpa only [angle,mul_one] using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _)
      (show 0≤Real.pi/2 by positivity)

lemma angle_zero {r : ℝ} (hr : 0<r) {y x : ThreeTorus L} (hq : pairQ L y x≤2*r^2) :
    angle L r y x=0 := by
  unfold angle
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) (by positivity)),mul_zero]

lemma angle_one {r : ℝ} (hr : 0<r) {y x : ThreeTorus L} (hq : 4*r^2≤pairQ L y x) :
    angle L r y x=Real.pi/2 := by
  unfold angle
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity)).mpr (by nlinarith)),mul_one]

lemma angle_one_outside {r : ℝ} (hr : 0<r) {y x : ThreeTorus L}
    (hx : y∉box L (Real.pi*r) x) : angle L r y x=Real.pi/2 :=
  angle_one L hr (not_mem_box_pairQ L hr hx).le

def angleFactor (r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  Real.pi/(4*r^2)*deriv Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2))

def anglePartial (r : ℝ) (z : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  angleFactor L r z*deriv (chordLift L) (z j)

omit hL in
lemma angleLift_derivative (r : ℝ) (z : Fin 3 → ℝ → ℝ)
    (d : Fin 3 → ℝ) (t : ℝ) (hd : ∀ j, HasDerivAt (z j) (d j) t) :
    HasDerivAt (fun s ↦ angleLift L r (fun j ↦ z j s))
      (∑ j : Fin 3, anglePartial L r (fun k ↦ z k t) j*d j) t := by
  have hc j := ((chordLift_smooth L).differentiable (by simp) (z j t)).hasDerivAt.comp t (hd j)
  have hq := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3))) (fun j _ ↦ hc j)
  have h := ((transition_derivative ((qLift L (fun j ↦ z j t)-2*r^2)/(2*r^2))).comp t
    ((hq.sub_const (2*r^2)).div_const (2*r^2))).const_mul (Real.pi/2)
  apply h.congr_deriv
  dsimp [anglePartial,angleFactor]
  calc
    _ = (Real.pi/(4*r^2)*deriv Real.smoothTransition ((qLift L (fun j ↦ z j t)-2*r^2)/(2*r^2)))*
        ∑ j : Fin 3, deriv (chordLift L) (z j t)*d j := by ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

omit hL in
lemma qLift_nonneg (z : Fin 3 → ℝ) : 0≤qLift L z := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit hL in
lemma chordLift_le_qLift (z : Fin 3 → ℝ) (j : Fin 3) : chordLift L (z j)≤qLift L z :=
  Finset.single_le_sum (fun k _ ↦ sq_nonneg (L/Real.pi*Real.sin (Real.pi/L*z k))) (Finset.mem_univ j)

omit hL in
lemma angleFactor_eq_zero {r : ℝ} (hr : 0<r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc (2*r^2) (4*r^2)) : angleFactor L r z=0 := by
  have ht : (qLift L z-2*r^2)/(2*r^2)∉Icc (0:ℝ) 1 := by
    intro hc
    apply hz
    have h0 := (le_div_iff₀ (show 0<2*r^2 by positivity)).mp hc.1
    have h1 := (div_le_iff₀ (show 0<2*r^2 by positivity)).mp hc.2
    constructor <;> nlinarith
  simp only [angleFactor,transition_deriv_eq_zero ht,mul_zero]

omit hL in
lemma anglePartial_eq_zero {r : ℝ} (hr : 0<r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc (2*r^2) (4*r^2)) (j : Fin 3) : anglePartial L r z j=0 := by
  rw [anglePartial,angleFactor_eq_zero L hr hz,zero_mul]

lemma anglePartial_sq_le {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (z : Fin 3 → ℝ) (j : Fin 3) :
    anglePartial L r z j^2 ≤ Real.pi^2*M^2/r^2 := by
  by_cases hz : qLift L z∈Icc (2*r^2) (4*r^2)
  · have hc : (deriv (chordLift L) (z j))^2≤16*r^2 := by
      have hs := chordLift_le_qLift L z j
      have hd := chordLift_derivative_sq_le L (z j)
      nlinarith [hz.2]
    have ht : (deriv Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2)))^2≤M^2 := by
      rw [← sq_abs (deriv Real.smoothTransition _)]
      exact (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb _)
    calc
      _ = (Real.pi/(4*r^2))^2*((deriv Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2)))^2*
          (deriv (chordLift L) (z j))^2) := by dsimp [anglePartial,angleFactor]; ring
      _ ≤ (Real.pi/(4*r^2))^2*(M^2*(16*r^2)) := by gcongr
      _ = _ := by field_simp [hr.ne']; ring
  · rw [anglePartial_eq_zero L hr hz j,zero_pow (by norm_num)]
    positivity

end PeriodicCutoff

end

end OAI
