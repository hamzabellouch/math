import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

/-! # A quantitative open-image lemma for the finite coordinate maps

Minimizing distance to the target plus a smooth distance penalty proves
local surjectivity from a uniform lower differential bound. This is the
finite-dimensional special case needed to pass openness to the limit.
-/

open Set Metric Filter
open scoped Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A lower bound on every differential forces a definite ball in the image.
No injectivity or global inverse is required. -/
theorem ball_subset_image_of_differential_bound {f : E → E} {x : E} {r M : ℝ}
    (hr : 0 < r) (hM : 0 < M)
    (hf : ContinuousOn f (closedBall x r))
    (hd : ∀ z ∈ ball x r, DifferentiableAt ℝ f z)
    (hb : ∀ z ∈ ball x r, ∀ v, ‖v‖ ≤ M * ‖fderiv ℝ f z v‖) :
    ball (f x) (r / (8*M)) ⊆ f '' closedBall x r := by
  intro y hy
  let a := 1 / (2*M)
  let penalty : E → ℝ := fun z => Real.sqrt (‖z-x‖^2+(r/2)^2)
  let q : E → ℝ := fun z => ‖f z-y‖+a*penalty z
  have ha : 0 < a := by dsimp only [a]; positivity
  have hp (z : E) : 0 < penalty z := Real.sqrt_pos.mpr (by positivity)
  have hpnorm (z : E) : ‖z-x‖ ≤ penalty z := by
    dsimp only [penalty]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (r/2)])
  have hpc : Continuous penalty := by dsimp only [penalty]; fun_prop
  have hqc : ContinuousOn q (closedBall x r) :=
    (hf.sub continuousOn_const).norm.add (continuousOn_const.mul hpc.continuousOn)
  have hx : x ∈ closedBall x r := mem_closedBall_self hr.le
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall x r).exists_isMinOn ⟨x,hx⟩ hqc
  have hqx : q x < a*r := by
    have hp0 : penalty x = r/2 := by simp [penalty, Real.sqrt_sq (by linarith : 0≤r/2)]
    have hxy : ‖f x-y‖ < r/(8*M) := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hy
    dsimp only [q]
    rw [hp0]
    have he : r/(8*M) = a*r/4 := by dsimp only [a]; field_simp; ring
    rw [he] at hxy
    nlinarith
  have hqz : q z < a*r := (hmin hx).trans_lt hqx
  have hzi : z ∈ ball x r := by
    have hlow : a*‖z-x‖ ≤ q z := by
      dsimp only [q]
      exact (mul_le_mul_of_nonneg_left (hpnorm z) ha.le).trans (le_add_of_nonneg_left (norm_nonneg _))
    rw [mem_ball, dist_eq_norm]
    nlinarith
  by_contra hnot
  have hne : f z-y ≠ 0 := by
    intro he
    exact hnot ⟨z,hz,sub_eq_zero.mp he⟩
  let J := fderiv ℝ f z
  have hJinj : Function.Injective J := by
    apply (injective_iff_map_eq_zero J.toLinearMap).mpr
    intro v hv
    change J v = 0 at hv
    have hh := hb z hzi v
    change ‖v‖ ≤ M*‖J v‖ at hh
    rw [hv, norm_zero, mul_zero] at hh
    exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  obtain ⟨v, hv⟩ := (LinearMap.surjective_of_injective (f := J.toLinearMap) hJinj) (y-f z)
  change J v = y-f z at hv
  have hvb : ‖v‖ ≤ M*‖f z-y‖ := by
    have hh := hb z hzi v
    change ‖v‖ ≤ M*‖J v‖ at hh
    rw [hv, norm_sub_rev] at hh
    exact hh
  let c : ℝ → E := fun t => z+t • v
  have hc : HasDerivAt c v 0 := by
    simpa only [c, one_smul, id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have hc0 : c 0 = z := by simp [c]
  have hfc : HasDerivAt (fun t => f (c t)-y) (y-f z) 0 := by
    have hdf : HasFDerivAt f J (c 0) := by simpa only [hc0] using (hd z hzi).hasFDerivAt
    have hh := (hdf.comp_hasDerivAt 0 hc).sub_const y
    simpa only [hv, Function.comp_def] using hh
  have hnorm : HasDerivAt (fun t => ‖f (c t)-y‖) (-‖f z-y‖) 0 := by
    have hh := hfc.norm_sq.sqrt (by simpa only [hc0] using pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
    simp only [hc0, ← neg_sub (f z) y, inner_neg_right, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)] at hh
    convert hh using 1
    field_simp [norm_ne_zero_iff.mpr hne]
  have hpcd : HasDerivAt (fun t => penalty (c t))
      (⟪z-x,v⟫_ℝ / penalty z) 0 := by
    have hh := ((hc.sub_const x).norm_sq.add_const ((r/2)^2)).sqrt
      (by simp only [hc0]; positivity)
    simpa only [penalty, hc0, mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)] using hh
  have hinner : ⟪z-x,v⟫_ℝ / penalty z ≤ ‖v‖ := by
    apply (div_le_iff₀ (hp z)).mpr
    calc
      _ ≤ ‖z-x‖*‖v‖ := real_inner_le_norm _ _
      _ ≤ penalty z*‖v‖ := mul_le_mul_of_nonneg_right (hpnorm z) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hloc : IsLocalMin q z := hmin.isLocalMin (closedBall_mem_nhds_of_mem hzi)
  have hlocc : IsLocalMin (q ∘ c) 0 :=
    (show IsLocalMin q (c 0) by simpa only [hc0] using hloc).comp_continuous hc.continuousAt
  have hqd := hnorm.add (hpcd.const_mul a)
  have hzero := hlocc.hasDerivAt_eq_zero hqd
  have hlt : -‖f z-y‖+a*(⟪z-x,v⟫_ℝ / penalty z) < 0 := by
    have hstep := mul_le_mul_of_nonneg_left (hinner.trans hvb) ha.le
    have he : a*M = 1/2 := by dsimp only [a]; field_simp
    rw [← mul_assoc, he] at hstep
    have hpos : 0 < ‖f z-y‖ := norm_pos_iff.mpr hne
    nlinarith [he]
  exact (ne_of_lt hlt) hzero

/-- A uniform limit of maps with a uniform lower differential bound has
open image, provided the limit is continuous. -/
theorem isOpen_image_of_uniform_limit_differential_bound
    {O : Set E} (hO : IsOpen O) {f : ℕ → E → E} {H : E → E}
    (hH : ContinuousOn H O) {M : ℝ} (hM : 0 < M)
    (hd : ∀ i z, z ∈ O → DifferentiableAt ℝ (f i) z)
    (hb : ∀ i z, z ∈ O → ∀ v, ‖v‖ ≤ M*‖fderiv ℝ (f i) z v‖)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (herr : ∀ i z, z ∈ O → dist (f i z) (H z) ≤ e i) :
    IsOpen (H '' O) := by
  apply Metric.isOpen_iff.mpr
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hO x hx
  let r := s/2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hK : closedBall x r ⊆ O := by
    intro z hz
    apply hball
    have hh : dist z x ≤ r := hz
    change dist z x < s
    dsimp only [r] at hh
    linarith
  let R := r/(8*M)
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨R/2, by positivity, ?_⟩
  intro y hy
  have hxy : dist y (H x) < R/2 := hy
  have hgap : 0 < R-dist y (H x) := by linarith
  have hclosed : IsClosed (H '' closedBall x r) :=
    ((isCompact_closedBall x r).image_of_continuousOn (hH.mono hK)).isClosed
  apply Set.image_mono hK
  apply hclosed.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨i,hi⟩ := (he.eventually (gt_mem_nhds (lt_min hε hgap))).exists
  have htarget : y ∈ ball (f i x) R := by
    rw [mem_ball]
    calc
      dist y (f i x) ≤ dist y (H x)+dist (H x) (f i x) := dist_triangle _ _ _
      _ = dist y (H x)+dist (f i x) (H x) := by rw [dist_comm (H x)]
      _ ≤ dist y (H x)+e i := add_le_add_right (herr i x hx) _
      _ < R := by linarith [lt_of_lt_of_le hi (min_le_right _ _)]
  obtain ⟨z,hz,hzy⟩ := ball_subset_image_of_differential_bound hr hM
    (fun z hz => (hd i z (hK hz)).continuousAt.continuousWithinAt)
    (fun z hz => hd i z (hK (ball_subset_closedBall hz)))
    (fun z hz => hb i z (hK (ball_subset_closedBall hz))) htarget
  refine ⟨H z, ⟨z,hz,rfl⟩, ?_⟩
  rw [← hzy]
  exact (herr i z (hK hz)).trans_lt (lt_of_lt_of_le hi (min_le_left _ _))

end RegularPointCoordinates

end

end OAI
