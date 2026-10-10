import OAI.Geometry.IsometricImmersion.Pulses.PulseProfiles
import OAI.Geometry.IsometricImmersion.Flows.FlowImageFirstBounds
import OAI.Geometry.IsometricImmersion.Caps.FixedMetricLowerCap

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted

theorem scalar_fderiv_coordinate_bound {q : Coord → ℝ} {p v : Coord} {M : ℝ}
    (_hM : 0 ≤ M) (hpartial : ∀ i : Fin 2, |coordPartial i q p| ≤ M) :
    |fderiv ℝ q p v| ≤ M*(|v 0|+|v 1|) := by
  have he : v = (v 0) • Pi.single 0 (1 : ℝ) + (v 1) • Pi.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [he, map_add, map_smul, map_smul]
  change |v 0 * coordPartial 0 q p + v 1 * coordPartial 1 q p| ≤ _
  calc
    _ ≤ |v 0 * coordPartial 0 q p| + |v 1 * coordPartial 1 q p| := abs_add_le _ _
    _ = |v 0| * |coordPartial 0 q p|+|v 1| * |coordPartial 1 q p| := by rw [abs_mul,abs_mul]
    _ ≤ |v 0| * M+|v 1| * M := add_le_add
      (mul_le_mul_of_nonneg_left (hpartial 0) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hpartial 1) (abs_nonneg _))
    _ = _ := by ring

theorem quotient_change_from_origin
    {q : Coord → ℝ} {U : Set Coord} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (hM : 0 ≤ M)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    {p : Coord} (hp : p ∈ modelSquare) : |q p-q 0| ≤ M*(|p 0|+|p 1|) := by
  have hz : (0 : Coord) ∈ modelSquare := by constructor <;> intro i <;> norm_num
  have hconv : Convex ℝ modelSquare := convex_Icc _ _
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • p ∈ modelSquare := by
    have h := hconv hp hz ht.1 (sub_nonneg.mpr ht.2) (by ring)
    simpa only [smul_zero, add_zero] using h
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => q (s • p)) (fderiv ℝ q (t • p) p) t := by
    have hdq := ((hq.contDiffAt (hU.mem_nhds (hSU (hseg t ht)))).differentiableAt (by simp)).hasFDerivAt
    have hdp : HasDerivAt (fun s : ℝ => s • p) p t := by
      have ht := (hasDerivAt_id t).smul_const p
      change HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) t at ht
      rw [one_smul] at ht
      exact ht
    exact hdq.comp_hasDerivAt t hdp
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv (fun s : ℝ => q (s • p)) t‖ ≤ M*(|p 0|+|p 1|) := by
    rw [(hder t ht).deriv, Real.norm_eq_abs]
    exact scalar_fderiv_coordinate_bound hM (hpartial (t • p) (hseg t ht))
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hder t ht).differentiableAt) hb
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  simpa only [zero_smul, one_smul, sub_zero, norm_one, mul_one, Real.norm_eq_abs] using h

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flow_segment_coordinate_sum
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {q0 T r s t u : ℝ} (hq0 : |q0| ≤ 1/20) (_hT : 0 < T) (hT2 : T < 2)
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T) (hu : u ∈ Icc (-T) T)
    (htheta : |Y s t+q0*t| ≤ r) :
    |u|+|Y s u| ≤ r+107*T/100 := by
  have ht' : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hu' : u ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have habst : |t| ≤ T := abs_le.mpr ht
  have habsu : |u| ≤ T := abs_le.mpr hu
  have hdt : |u-t| ≤ 2*T := (abs_sub u t).trans (by linarith)
  have hmove := (cap_flow_time_lipschitz hq hU hSU hY hrange hstart hode hsmall hs ht' hu').trans
    (mul_le_mul_of_nonneg_left hdt (by norm_num : (0 : ℝ) ≤ 1/100))
  have hprod : |q0*t| ≤ (1/20)*T := by
    rw [abs_mul]
    exact mul_le_mul hq0 habst (abs_nonneg _) (by norm_num)
  have hyt : |Y s t| ≤ r+(1/20)*T := by
    calc
      |Y s t| = |(Y s t+q0*t)-q0*t| := by congr 1; ring
      _ ≤ |Y s t+q0*t|+|q0*t| := abs_sub _ _
      _ ≤ _ := add_le_add htheta hprod
  have hyu : |Y s u| ≤ |Y s u-Y s t|+|Y s t| := by
    calc
      |Y s u| = |(Y s u-Y s t)+Y s t| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

theorem flow_segment_quotient_near_center
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L T r s t : ℝ} (hM : 0 ≤ M) (hL : 0 < L)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : 0 < T) (hT2 : T < 2) (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T)
    (htheta : |Y s t+q0*t| ≤ r)
    (hrsmall : M*(r+107*T/100) ≤ 9/(100*L)) :
    ∀ u ∈ Icc (-T) T, |q (coordinatePoint u (Y s u))-q0| ≤ 1/(10*L) := by
  intro u hu
  have hu2 : u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hp : coordinatePoint u (Y s u) ∈ modelSquare := coordinatePoint_mem_modelSquare
    ⟨by linarith [hu2.1],by linarith [hu2.2]⟩
    (hrange s ⟨hs.1.le,hs.2.le⟩ u hu2)
  have hnorm := flow_segment_coordinate_sum hq hU hSU hY hrange hstart hode
    hsmall hq0 hT hT2 hs ht hu htheta
  have hlocal : |q (coordinatePoint u (Y s u))-q 0| ≤ M*(|u|+|Y s u|) := by
    simpa [coordinatePoint] using quotient_change_from_origin hq hU hSU hM hpartial hp
  have hsum : |q (coordinatePoint u (Y s u))-q0| ≤
      |q (coordinatePoint u (Y s u))-q 0|+|q 0-q0| := by
    calc
      _ = |(q (coordinatePoint u (Y s u))-q 0)+(q 0-q0)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have ha := hsum.trans (add_le_add (hlocal.trans
    (mul_le_mul_of_nonneg_left hnorm hM)) hcenter)
  have heq : 9/(100*L)+1/(100*L) = 1/(10*L) := by field_simp [hL.ne']; ring
  exact ha.trans ((add_le_add hrsmall le_rfl).trans_eq heq)

theorem actual_shear_seed_distance
    {q0 epsilon T s t : ℝ} (hT : 0 < T) (hT2 : T < 2)
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T)
    (hclose : ∀ u ∈ Icc (-T) T, |q (coordinatePoint u (Y s u))-q0| ≤ epsilon) :
    |Y s t+q0*t-s| ≤ epsilon*|t| := by
  have hd (u : ℝ) (hu : u ∈ Icc (-T) T) :
      HasDerivAt (fun a => Y s a+q0*a) (-q (coordinatePoint u (Y s u))+q0) u := by
    have hu2 : u ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hh := (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs hu2).add
      ((hasDerivAt_id u).const_mul q0)
    change HasDerivAt (fun a : ℝ => Y s a + q0 * a)
      (-q (coordinatePoint u (Y s u)) + q0 * 1) u at hh
    rw [mul_one] at hh
    exact hh
  have hb (u : ℝ) (hu : u ∈ Icc (-T) T) :
      ‖deriv (fun a => Y s a+q0*a) u‖ ≤ epsilon := by
    rw [(hd u hu).deriv, Real.norm_eq_abs]
    have heq : -q (coordinatePoint u (Y s u))+q0 = -(q (coordinatePoint u (Y s u))-q0) := by ring
    rw [heq,abs_neg]
    exact hclose u hu
  have h := (convex_Icc (-T) T).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hd u hu).differentiableAt) hb
    (show (0 : ℝ) ∈ Icc (-T) T by constructor <;> linarith) ht
  simpa only [hstart s ⟨hs.1.le,hs.2.le⟩, mul_zero, add_zero, sub_zero, Real.norm_eq_abs] using h

end SmoothLocal.Pulse

end

end OAI
