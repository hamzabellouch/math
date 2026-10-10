import Mathlib
import OAI.Analysis.HardSphere.Model
import OAI.Analysis.HardSphere.Cutoffs.ThreeTorus

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set
noncomputable section

variable (L : ℝ) [hL : Fact (0<L)]

def near (r : ℝ) (x : ThreeTorus L) : Set (ThreeTorus L) :=
  {y | pairQ L y x≤(3/2)*r^2}

lemma near_measurable (r : ℝ) (x : ThreeTorus L) : MeasurableSet (near L r x) :=
  (isClosed_le ((pairQ_continuous L).comp (continuous_id.prodMk continuous_const)) continuous_const).measurableSet

lemma distance_sum_le_pairQ (y x : ThreeTorus L) :
    (∑ j : Fin 3, dist (y j) (x j)^2) ≤ (Real.pi/2)^2*pairQ L y x := by
  rw [pairQ,Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ by simpa only [dist_eq_norm] using norm_sq_le_chord L (y j-x j)

lemma near_distance_sum {r : ℝ} (hr : 0<r) {y x : ThreeTorus L}
    (hy : y∈near L r x) : (∑ j : Fin 3, dist (y j) (x j)^2) < (2*r)^2 := by
  have hp : Real.pi^2<10 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hq := distance_sum_le_pairQ L y x
  have hs := mul_le_mul_of_nonneg_left hy (sq_nonneg (Real.pi/2))
  have hh := mul_lt_mul_of_pos_right hp (sq_pos_of_pos hr)
  nlinarith

lemma near_subset_box {r : ℝ} (hr : 0<r) (x : ThreeTorus L) : near L r x⊆box L (2*r) x := by
  intro y hy
  simp only [box,Set.mem_univ_pi,Metric.mem_closedBall]
  intro j
  have hs := Finset.single_le_sum (f := fun j : Fin 3 ↦ dist (y j) (x j)^2)
    (fun j _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have hh := near_distance_sum L hr hy
  exact (sq_le_sq₀ dist_nonneg (by positivity)).mp (hs.trans hh.le)

lemma near_volume_le {r : ℝ} (hr : 0<r) (x : ThreeTorus L) :
    volume.real (near L r x)≤(4*r)^3 := by
  calc
    _ ≤ volume.real (box L (2*r) x) := measureReal_mono (near_subset_box L hr x)
    _ ≤ (2*(2*r))^3 := box_volume_le L (by positivity) x
    _ = _ := by ring

lemma near_distance {K : Length} {r : ℝ} (hr : 0<r) {y x : Torus K}
    (hy : y∈near K.val r x) : torusDistance K y x≤2*r := by
  have h := near_distance_sum K.val hr hy
  exact Real.sqrt_le_iff.mpr ⟨by positivity,h.le⟩

end
end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
noncomputable section
variable (L : ℝ) [hL : Fact (0<L)]

def angle (r : ℝ) (y x : ThreeTorus L) : ℝ :=
  Real.pi/2*Real.smoothTransition ((pairQ L y x-(5/4)*r^2)/((1/4)*r^2))

def angleLift (r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  Real.pi/2*Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2))

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

lemma angle_zero {r : ℝ} (hr : 0<r) {y x : ThreeTorus L} (hq : pairQ L y x≤(5/4)*r^2) :
    angle L r y x=0 := by
  unfold angle
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) (by positivity)),mul_zero]

lemma angle_one {r : ℝ} (hr : 0<r) {y x : ThreeTorus L} (hq : (3/2)*r^2≤pairQ L y x) :
    angle L r y x=Real.pi/2 := by
  unfold angle
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity)).mpr (by nlinarith)),mul_one]

lemma angle_one_outside {r : ℝ} (hr : 0<r) {y x : ThreeTorus L}
    (hx : y∉near L r x) : angle L r y x=Real.pi/2 :=
  angle_one L hr (not_le.mp hx).le
end
end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

def angleFactor (r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  2*Real.pi/r^2*deriv Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2))

def anglePartial (r : ℝ) (z : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  angleFactor L r z*deriv (chordLift L) (z j)

omit hL in
lemma angleLift_derivative (r : ℝ) (z : Fin 3 → ℝ → ℝ)
    (d : Fin 3 → ℝ) (t : ℝ) (hd : ∀ j, HasDerivAt (z j) (d j) t) :
    HasDerivAt (fun s ↦ angleLift L r (fun j ↦ z j s))
      (∑ j : Fin 3, anglePartial L r (fun k ↦ z k t) j*d j) t := by
  have hc j := ((chordLift_smooth L).differentiable (by simp) (z j t)).hasDerivAt.comp t (hd j)
  have hq := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3))) (fun j _ ↦ hc j)
  have h := ((transition_derivative ((qLift L (fun j ↦ z j t)-(5/4)*r^2)/((1/4)*r^2))).comp t
    ((hq.sub_const ((5/4)*r^2)).div_const ((1/4)*r^2))).const_mul (Real.pi/2)
  apply h.congr_deriv
  dsimp [anglePartial,angleFactor]
  calc
    _ = (2*Real.pi/r^2*deriv Real.smoothTransition ((qLift L (fun j ↦ z j t)-(5/4)*r^2)/((1/4)*r^2)))*
        ∑ j : Fin 3, deriv (chordLift L) (z j t)*d j := by ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

omit hL in
lemma angleFactor_eq_zero {r : ℝ} (hr : 0<r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc ((5/4)*r^2) ((3/2)*r^2)) : angleFactor L r z=0 := by
  have ht : (qLift L z-(5/4)*r^2)/((1/4)*r^2)∉Icc (0:ℝ) 1 := by
    intro hc
    apply hz
    have h0 := (le_div_iff₀ (show 0<(1/4)*r^2 by positivity)).mp hc.1
    have h1 := (div_le_iff₀ (show 0<(1/4)*r^2 by positivity)).mp hc.2
    constructor <;> nlinarith
  simp only [angleFactor,transition_deriv_eq_zero ht,mul_zero]

omit hL in
lemma anglePartial_eq_zero {r : ℝ} (hr : 0<r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc ((5/4)*r^2) ((3/2)*r^2)) (j : Fin 3) : anglePartial L r z j=0 := by
  rw [anglePartial,angleFactor_eq_zero L hr hz,zero_mul]

lemma anglePartial_sq_le {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (z : Fin 3 → ℝ) (j : Fin 3) :
    anglePartial L r z j^2 ≤ 24*Real.pi^2*M^2/r^2 := by
  by_cases hz : qLift L z∈Icc ((5/4)*r^2) ((3/2)*r^2)
  · have hc : (deriv (chordLift L) (z j))^2≤6*r^2 := by
      have hs := chordLift_le_qLift L z j
      have hd := chordLift_derivative_sq_le L (z j)
      nlinarith [hz.2]
    have ht : (deriv Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2)))^2≤M^2 := by
      rw [← sq_abs (deriv Real.smoothTransition _)]
      exact (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb _)
    calc
      _ = (2*Real.pi/r^2)^2*((deriv Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2)))^2*
          (deriv (chordLift L) (z j))^2) := by dsimp [anglePartial,angleFactor]; ring
      _ ≤ (2*Real.pi/r^2)^2*(M^2*(6*r^2)) := by gcongr
      _ = _ := by field_simp [hr.ne']; ring
  · rw [anglePartial_eq_zero L hr hz j,zero_pow (by norm_num)]
    positivity

end HardSphere.TightCutoff

end
end
end
end
end
end

end OAI
