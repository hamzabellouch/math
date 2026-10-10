import OAI.Geometry.IsometricImmersion.Energy.WeightedMultiplier
import OAI.Geometry.IsometricImmersion.Calculus.QuotientCalculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Real.Sqrt

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem smoothTransition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y)

theorem smoothTransition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y)

theorem exists_smoothTransition_derivative_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  by_cases hx : x ≤ 0
  · rw [smoothTransition_deriv_zero_of_nonpos hx, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  by_cases hx1 : 1 ≤ x
  · rw [smoothTransition_deriv_zero_of_one_le hx1, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  have hxc : x ∈ Icc (0 : ℝ) 1 := ⟨(lt_of_not_ge hx).le, (lt_of_not_ge hx1).le⟩
  have hcx : |deriv Real.smoothTransition x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x hxc
  exact hcx.trans (le_max_right _ _)

def transitionDerivativeBound : ℝ :=
  Classical.choose exists_smoothTransition_derivative_bound

theorem transitionDerivativeBound_pos : 0 < transitionDerivativeBound :=
  (Classical.choose_spec exists_smoothTransition_derivative_bound).1

theorem smoothTransition_deriv_abs_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ transitionDerivativeBound :=
  (Classical.choose_spec exists_smoothTransition_derivative_bound).2 x

def intervalCutoff (a b x : ℝ) : ℝ := Real.smoothTransition ((x - a) / (b - a))

theorem intervalCutoff_contDiff (a b : ℝ) : ContDiff ℝ ∞ (intervalCutoff a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a))

theorem intervalCutoff_range (a b x : ℝ) :
    0 ≤ intervalCutoff a b x ∧ intervalCutoff a b x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem intervalCutoff_zero {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    intervalCutoff a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le)

theorem intervalCutoff_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    intervalCutoff a b x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)

theorem intervalCutoff_hasDerivAt (a b x : ℝ) :
    HasDerivAt (intervalCutoff a b)
      (deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) x := by
  have htheta := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have ht : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((x - a) / (b - a))) ((x - a) / (b - a)) :=
    (htheta _).hasDerivAt
  have ha : HasDerivAt (fun y : ℝ => (y - a) / (b - a)) (1 / (b - a)) x :=
    ((hasDerivAt_id x).sub_const a).div_const (b - a)
  have hd := ht.comp x ha
  change HasDerivAt (Real.smoothTransition ∘ fun y : ℝ => (y - a) / (b - a)) _ x
  have he : deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a) =
      deriv Real.smoothTransition ((x - a) / (b - a)) * (1 / (b - a)) := by ring
  rw [he]
  exact hd

theorem intervalCutoff_deriv (a b x : ℝ) :
    deriv (intervalCutoff a b) x =
      deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a) :=
  (intervalCutoff_hasDerivAt a b x).deriv

theorem intervalCutoff_deriv_zero_left {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    deriv (intervalCutoff a b) x = 0 := by
  rw [intervalCutoff_deriv, smoothTransition_deriv_zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le), zero_div]

theorem intervalCutoff_deriv_zero_right {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    deriv (intervalCutoff a b) x = 0 := by
  rw [intervalCutoff_deriv, smoothTransition_deriv_zero_of_one_le
    ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)), zero_div]

theorem intervalCutoff_deriv_abs_le {a b : ℝ} (hab : a < b) (x : ℝ) :
    |deriv (intervalCutoff a b) x| ≤ transitionDerivativeBound / (b - a) := by
  rw [intervalCutoff_deriv, abs_div, abs_of_pos (sub_pos.mpr hab)]
  exact div_le_div_of_nonneg_right (smoothTransition_deriv_abs_le _) (sub_pos.mpr hab).le

theorem intervalCutoff_deriv_support {a b x : ℝ} (hab : a < b)
    (hx : deriv (intervalCutoff a b) x ≠ 0) : a < x ∧ x < b := by
  constructor
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_left hab (le_of_not_gt h))
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_right hab (le_of_not_gt h))

def ellipticPhi (c x : ℝ) : ℝ := intervalCutoff (c / 2) c x

theorem ellipticPhi_contDiff (c : ℝ) : ContDiff ℝ ∞ (ellipticPhi c) :=
  intervalCutoff_contDiff _ _

theorem ellipticPhi_zero {c x : ℝ} (hc : 0 < c) (hx : x ≤ c / 2) :
    ellipticPhi c x = 0 := intervalCutoff_zero (by linarith) hx

theorem ellipticPhi_one {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    ellipticPhi c x = 1 := intervalCutoff_one (by linarith) hx

theorem ellipticPhi_deriv_abs_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    |deriv (ellipticPhi c) x| ≤ 2 * transitionDerivativeBound / c := by
  have hh := intervalCutoff_deriv_abs_le (a := c / 2) (b := c) (by linarith) x
  change |deriv (intervalCutoff (c / 2) c) x| ≤ _
  have he : transitionDerivativeBound / (c - c / 2) =
      2 * transitionDerivativeBound / c := by field_simp; ring
  rw [he] at hh
  exact hh

theorem ellipticPhi_deriv_support {c x : ℝ} (hc : 0 < c)
    (hx : deriv (ellipticPhi c) x ≠ 0) : c / 2 < x ∧ x < c := by
  constructor
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_left (by linarith) (le_of_not_gt h))
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_right (by linarith) (le_of_not_gt h))

def threeEdgeCutoff (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) : ℝ :=
  intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
    intervalCutoff a0 a1 (p 1)

theorem threeEdgeCutoff_contDiff (l0 l1 r1 r0 a0 a1 : ℝ) :
    ContDiff ℝ ∞ (threeEdgeCutoff l0 l1 r1 r0 a0 a1) := by
  exact (((intervalCutoff_contDiff l0 l1).comp (contDiff_apply ℝ ℝ 0)).mul
    ((intervalCutoff_contDiff (-r0) (-r1)).comp (contDiff_apply ℝ ℝ 0).neg)).mul
      ((intervalCutoff_contDiff a0 a1).comp (contDiff_apply ℝ ℝ 1))

theorem threeEdgeCutoff_range (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) :
    0 ≤ threeEdgeCutoff l0 l1 r1 r0 a0 a1 p ∧
      threeEdgeCutoff l0 l1 r1 r0 a0 a1 p ≤ 1 := by
  have hL := intervalCutoff_range l0 l1 (p 0)
  have hR := intervalCutoff_range (-r0) (-r1) (-p 0)
  have hS := intervalCutoff_range a0 a1 (p 1)
  constructor
  · exact mul_nonneg (mul_nonneg hL.1 hR.1) hS.1
  · have hLR : intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) ≤ 1 := by
      nlinarith
    change intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
      intervalCutoff a0 a1 (p 1) ≤ 1
    nlinarith [mul_nonneg hL.1 hR.1]

theorem threeEdgeCutoff_one {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord)
    (hp : l1 ≤ p 0 ∧ p 0 ≤ r1 ∧ a1 ≤ p 1) :
    threeEdgeCutoff l0 l1 r1 r0 a0 a1 p = 1 := by
  rw [threeEdgeCutoff, intervalCutoff_one hL hp.1,
    intervalCutoff_one (neg_lt_neg hR) (neg_le_neg hp.2.1),
    intervalCutoff_one hS hp.2.2]
  norm_num

theorem threeEdgeCutoff_zero {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord)
    (hp : p 0 ≤ l0 ∨ r0 ≤ p 0 ∨ p 1 ≤ a0) :
    threeEdgeCutoff l0 l1 r1 r0 a0 a1 p = 0 := by
  rcases hp with h | h | h
  · simp [threeEdgeCutoff, intervalCutoff_zero hL h]
  · simp [threeEdgeCutoff, intervalCutoff_zero (neg_lt_neg hR) (neg_le_neg h)]
  · simp [threeEdgeCutoff, intervalCutoff_zero hS h]

theorem threeEdgeCutoff_partial (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p =
      if i = 0 then
        deriv (intervalCutoff l0 l1) (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
          intervalCutoff a0 a1 (p 1) -
        intervalCutoff l0 l1 (p 0) * deriv (intervalCutoff (-r0) (-r1)) (-p 0) *
          intervalCutoff a0 a1 (p 1)
      else intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
        deriv (intervalCutoff a0 a1) (p 1) := by
  have hL := (((intervalCutoff_contDiff l0 l1).differentiable (by simp) (p 0)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 0 p)
  have hR := (((intervalCutoff_contDiff (-r0) (-r1)).differentiable (by simp) (-p 0)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 0 p).neg
  have hS := (((intervalCutoff_contDiff a0 a1).differentiable (by simp) (p 1)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hd := (hL.fun_mul hR).fun_mul hS
  simp only [Function.comp_def, Pi.neg_apply] at hd
  change fderiv ℝ (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p (Pi.single i 1) = _
  change fderiv ℝ (fun q => intervalCutoff l0 l1 (q 0) *
    intervalCutoff (-r0) (-r1) (-q 0) * intervalCutoff a0 a1 (q 1)) p _ = _
  rw [hd.fderiv]
  fin_cases i <;> simp
  ring

theorem abs_mul_two_cutoffs_le (a b c : ℝ) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) : |a * b * c| ≤ |a| := by
  rw [abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hc.1]
  calc
    |a| * b * c ≤ |a| * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg a)) hc.2 hc.1
        (mul_nonneg (abs_nonneg a) zero_le_one)
    _ = |a| := by ring

theorem threeEdgeCutoff_partial_bounds {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord) :
    |coordPartial 0 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
        transitionDerivativeBound / (l1 - l0) + transitionDerivativeBound / (r0 - r1) ∧
      |coordPartial 1 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
        transitionDerivativeBound / (a1 - a0) := by
  have hleft := intervalCutoff_range l0 l1 (p 0)
  have hright := intervalCutoff_range (-r0) (-r1) (-p 0)
  have hbottom := intervalCutoff_range a0 a1 (p 1)
  constructor
  · rw [threeEdgeCutoff_partial]
    simp only [↓reduceIte]
    refine (abs_sub _ _).trans ?_
    apply add_le_add
    · exact (abs_mul_two_cutoffs_le _ _ _ hright hbottom).trans
        (intervalCutoff_deriv_abs_le hL _)
    · rw [mul_comm (intervalCutoff l0 l1 (p 0))]
      exact (abs_mul_two_cutoffs_le _ _ _ hleft hbottom).trans
        (by simpa only [neg_sub_neg] using intervalCutoff_deriv_abs_le (neg_lt_neg hR) (-p 0))
  · rw [threeEdgeCutoff_partial]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    have he : intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
        deriv (intervalCutoff a0 a1) (p 1) = deriv (intervalCutoff a0 a1) (p 1) *
        intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) := by ring
    rw [he]
    exact (abs_mul_two_cutoffs_le _ _ _ hleft hright).trans (intervalCutoff_deriv_abs_le hS _)

theorem threeEdgeCutoff_partial_t_support {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (p : Coord)
    (hp : coordPartial 0 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p ≠ 0) :
    p 0 ∈ Ioo l0 l1 ∨ p 0 ∈ Ioo r1 r0 := by
  by_cases hl : deriv (intervalCutoff l0 l1) (p 0) = 0
  · have hr : deriv (intervalCutoff (-r0) (-r1)) (-p 0) ≠ 0 := by
      intro h
      apply hp
      rw [threeEdgeCutoff_partial]
      simp [hl, h]
    have hs := intervalCutoff_deriv_support (neg_lt_neg hR) hr
    exact Or.inr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · exact Or.inl (intervalCutoff_deriv_support hL hl)

theorem threeEdgeCutoff_partial_s_support {l0 l1 r1 r0 a0 a1 : ℝ}
    (hS : a0 < a1) (p : Coord)
    (hp : coordPartial 1 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p ≠ 0) :
    p 1 ∈ Ioo a0 a1 := by
  apply intervalCutoff_deriv_support hS
  intro hz
  apply hp
  rw [threeEdgeCutoff_partial]
  simp [hz]

def capInnerEdge (x : ℝ) : ℝ := (-2 + min x (-3 / 2)) / 2
def capOuterEdge (x : ℝ) : ℝ := (-2 + capInnerEdge x) / 2

theorem capEdges_bounds {x : ℝ} (hx : -2 < x) :
    -2 < capOuterEdge x ∧ capOuterEdge x < capInnerEdge x ∧
      capInnerEdge x < -3 / 2 ∧ capInnerEdge x < x := by
  have hm : -2 < min x (-3 / 2 : ℝ) := lt_min hx (by norm_num)
  have hmx := min_le_left x (-3 / 2 : ℝ)
  have hmh := min_le_right x (-3 / 2 : ℝ)
  unfold capInnerEdge capOuterEdge
  dsimp only [capInnerEdge]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

def capSpatialCutoff (L R A : ℝ) : Coord → ℝ :=
  threeEdgeCutoff (capOuterEdge L) (capInnerEdge L)
    (-capInnerEdge (-R)) (-capOuterEdge (-R)) (capOuterEdge A) (capInnerEdge A)

theorem capSpatialCutoff_contDiff (L R A : ℝ) :
    ContDiff ℝ ∞ (capSpatialCutoff L R A) := threeEdgeCutoff_contDiff _ _ _ _ _ _

theorem capSpatialCutoff_range (L R A : ℝ) (p : Coord) :
    0 ≤ capSpatialCutoff L R A p ∧ capSpatialCutoff L R A p ≤ 1 :=
  threeEdgeCutoff_range _ _ _ _ _ _ p

theorem capSpatialCutoff_one {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord)
    (hp : L ≤ p 0 ∧ p 0 ≤ R ∧ A ≤ p 1) : capSpatialCutoff L R A p = 1 := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  apply threeEdgeCutoff_one hli (neg_lt_neg hri) hai p
  exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩

theorem capSpatialCutoff_zero {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord)
    (hp : p 0 ≤ -2 ∨ 2 ≤ p 0 ∨ p 1 ≤ -2) : capSpatialCutoff L R A p = 0 := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai p
  rcases hp with h | h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

theorem capSpatialCutoff_derivative_bands {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord) (i : Fin 2)
    (hp : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    (3 / 2 < |p 0| ∧ |p 0| < 2) ∨ (-2 < p 1 ∧ p 1 < -3 / 2) := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  fin_cases i
  · rcases threeEdgeCutoff_partial_t_support hli (neg_lt_neg hri) p hp with ht | ht
    · left
      rw [abs_of_neg (by linarith [ht.2] : p 0 < 0)]
      constructor <;> linarith [ht.1, ht.2]
    · left
      rw [abs_of_pos (by linarith [ht.1] : 0 < p 0)]
      constructor <;> linarith [ht.1, ht.2]
  · have hs := threeEdgeCutoff_partial_s_support hai p hp
    exact Or.inr ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem ellipticPhi_ratio_derivative_bound
    {c d k ki di M : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hM : 0 ≤ M) (hki : |ki| ≤ M) (hdi : |di| ≤ 1) :
    |deriv (ellipticPhi c) (k / d) * ((ki * d - k * di) / d ^ 2)| ≤
      (2 * transitionDerivativeBound / c) * (M + c) / d := by
  have hC : 0 ≤ 2 * transitionDerivativeBound / c :=
    div_nonneg (mul_nonneg (by norm_num) transitionDerivativeBound_pos.le) hc.le
  by_cases hzero : deriv (ellipticPhi c) (k / d) = 0
  · rw [hzero, zero_mul, abs_zero]
    exact div_nonneg (mul_nonneg hC (add_nonneg hM hc.le)) hd.le
  have hsupp := ellipticPhi_deriv_support hc hzero
  have hkpos : 0 < k := by
    have hpos : 0 < k / d := lt_trans (by linarith : 0 < c / 2) hsupp.1
    exact (div_pos_iff.mp hpos).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge hd.le h.2))
  have hkupper : |k| ≤ c * d := by
    rw [abs_of_pos hkpos]
    exact ((div_lt_iff₀ hd).mp hsupp.2).le
  have hnum : |ki * d - k * di| ≤ (M + c) * d := by
    calc
      |ki * d - k * di| ≤ |ki| * d + |k| * |di| := by
        simpa only [abs_mul, abs_of_pos hd] using abs_sub (ki * d) (k * di)
      _ ≤ M * d + (c * d) * 1 := add_le_add
        (mul_le_mul_of_nonneg_right hki hd.le)
        (mul_le_mul hkupper hdi (abs_nonneg di) (mul_nonneg hc.le hd.le))
      _ = (M + c) * d := by ring
  rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg d)]
  calc
    |deriv (ellipticPhi c) (k / d)| * (|ki * d - k * di| / d ^ 2) ≤
        (2 * transitionDerivativeBound / c) * (((M + c) * d) / d ^ 2) :=
      mul_le_mul (ellipticPhi_deriv_abs_le hc _) (div_le_div_of_nonneg_right hnum (sq_nonneg d))
        (div_nonneg (abs_nonneg _) (sq_nonneg d)) hC
    _ = (2 * transitionDerivativeBound / c) * (M + c) / d := by
      field_simp [hd.ne']

def ellipticWeight (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 6 * (chi p) ^ 2 * (ellipticPhi c (K p / edgeDistance b p)) ^ 2

def ellipticGate (b c : ℝ) (K : Coord → ℝ) (p : Coord) : ℝ :=
  ellipticPhi c (K p / edgeDistance b p)

def ellipticAmplitude (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 3 * chi p * ellipticGate b c K p

theorem ellipticAmplitude_sq (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    ellipticAmplitude b c chi K p ^ 2 = ellipticWeight b c chi K p := by
  unfold ellipticAmplitude ellipticGate ellipticWeight
  ring

theorem edgeDistance_partial (b : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (edgeDistance b) p = -(if (1 : Fin 2) = i then 1 else 0) := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  simp only [Pi.sub_def] at hd
  unfold coordPartial edgeDistance
  rw [hd.fderiv]
  fin_cases i <;> simp

theorem ellipticGate_differentiableAt {b c : ℝ} {K : Coord → ℝ} {p : Coord}
    (hK : DifferentiableAt ℝ K p) (hd : edgeDistance b p ≠ 0) :
    DifferentiableAt ℝ (ellipticGate b c K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hquot : DifferentiableAt ℝ (fun q => K q / edgeDistance b q) p := by
    have hm : DifferentiableAt ℝ (fun q => K q * (edgeDistance b q)⁻¹) p :=
      hK.mul (hD.inv hd)
    simpa only [div_eq_mul_inv] using hm
  exact ((ellipticPhi_contDiff c).differentiable (by simp) _).comp p hquot

theorem ellipticGate_partial {b c : ℝ} {K : Coord → ℝ} {p : Coord}
    (hK : DifferentiableAt ℝ K p) (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticGate b c K) p =
      deriv (ellipticPhi c) (K p / edgeDistance b p) *
        ((coordPartial i K p * edgeDistance b p - K p * coordPartial i (edgeDistance b) p) /
          edgeDistance b p ^ 2) := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hquot : DifferentiableAt ℝ (fun q => K q / edgeDistance b q) p := by
    have hm : DifferentiableAt ℝ (fun q => K q * (edgeDistance b q)⁻¹) p :=
      hK.mul (hD.inv hd)
    simpa only [div_eq_mul_inv] using hm
  have hh := (((ellipticPhi_contDiff c).differentiable (by simp)
    (K p / edgeDistance b p)).hasDerivAt).comp_hasFDerivAt p hquot.hasFDerivAt
  simp only [Function.comp_def] at hh
  have he : coordPartial i (ellipticGate b c K) p =
      deriv (ellipticPhi c) (K p / edgeDistance b p) *
        coordPartial i (fun q => K q / edgeDistance b q) p := by
    unfold coordPartial ellipticGate
    rw [hh.fderiv]
    simp only [smul_apply, smul_eq_mul]
  rw [he, coordPartial_div hK hD hd i]

theorem ellipticGate_partial_bound {b c M : ℝ} {K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hM : 0 ≤ M)
    (hK : DifferentiableAt ℝ K p) (i : Fin 2) (hKi : |coordPartial i K p| ≤ M) :
    |coordPartial i (ellipticGate b c K) p| ≤
      (2 * transitionDerivativeBound / c) * (M + c) / edgeDistance b p := by
  rw [ellipticGate_partial hK hd.ne' i]
  apply ellipticPhi_ratio_derivative_bound hc hd hM hKi
  rw [edgeDistance_partial]
  fin_cases i <;> norm_num

theorem ellipticAmplitude_differentiableAt {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) : DifferentiableAt ℝ (ellipticAmplitude b c chi K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  exact ((hD.pow 3).mul hchi).mul (ellipticGate_differentiableAt hK hd)

theorem ellipticAmplitude_partial {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticAmplitude b c chi K) p =
      3 * edgeDistance b p ^ 2 * coordPartial i (edgeDistance b) p * chi p * ellipticGate b c K p +
      edgeDistance b p ^ 3 * coordPartial i chi p * ellipticGate b c K p +
      edgeDistance b p ^ 3 * chi p * coordPartial i (ellipticGate b c K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hG := ellipticGate_differentiableAt (b := b) (c := c) hK hd
  have hdpow : coordPartial i (fun q => edgeDistance b q ^ 3) p =
      3 * edgeDistance b p ^ 2 * coordPartial i (edgeDistance b) p := by
    unfold coordPartial
    rw [(hD.hasFDerivAt.pow 3).fderiv]
    simp only [smul_apply, smul_eq_mul]
    ring
  unfold ellipticAmplitude
  rw [HessianCalculus.coordPartial_mul_at
      (f := fun q => edgeDistance b q ^ 3 * chi q) (h := ellipticGate b c K)
      ((hD.pow 3).mul hchi) hG i,
    HessianCalculus.coordPartial_mul_at (f := fun q => edgeDistance b q ^ 3) (h := chi)
      (hD.pow 3) hchi i, hdpow]
  ring

theorem ellipticWeight_partial {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticWeight b c chi K) p =
      2 * ellipticAmplitude b c chi K p * coordPartial i (ellipticAmplitude b c chi K) p := by
  have hA := ellipticAmplitude_differentiableAt (c := c) hchi hK hd
  have he : ellipticWeight b c chi K =
      fun q => ellipticAmplitude b c chi K q * ellipticAmplitude b c chi K q := by
    funext q
    rw [← ellipticAmplitude_sq, pow_two]
  rw [he, HessianCalculus.coordPartial_mul_at hA hA i]
  ring

theorem amplitude_derivative_algebra_bound
    {d x g di xi gi X P : ℝ} (hd : 0 < d)
    (hx : 0 ≤ x ∧ x ≤ 1) (hg : 0 ≤ g ∧ g ≤ 1)
    (hdi : |di| ≤ 1) (hxi : |xi| ≤ X) (hgi : |gi| ≤ P / d) :
    |3 * d ^ 2 * di * x * g + d ^ 3 * xi * g + d ^ 3 * x * gi| ≤
      3 * d ^ 2 + d ^ 3 * X + d ^ 2 * P := by
  have hfirst : |3 * d ^ 2 * di * x * g| ≤ 3 * d ^ 2 := by
    calc
      _ ≤ |3 * d ^ 2 * di| := abs_mul_two_cutoffs_le _ _ _ hx hg
      _ = (3 * d ^ 2) * |di| := by rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (3 * d ^ 2) * 1 := mul_le_mul_of_nonneg_left hdi (by positivity)
      _ = 3 * d ^ 2 := mul_one _
  have hsecond : |d ^ 3 * xi * g| ≤ d ^ 3 * X := by
    calc
      _ = |(d ^ 3 * xi) * g * 1| := by rw [mul_one]
      _ ≤ |d ^ 3 * xi| := abs_mul_two_cutoffs_le _ _ _ hg ⟨zero_le_one, le_rfl⟩
      _ = d ^ 3 * |xi| := by rw [abs_mul, abs_of_pos (pow_pos hd _)]
      _ ≤ d ^ 3 * X := mul_le_mul_of_nonneg_left hxi (pow_pos hd _).le
  have hthird : |d ^ 3 * x * gi| ≤ d ^ 2 * P := by
    calc
      _ = |(d ^ 3 * gi) * x * 1| := by congr 1; ring
      _ ≤ |d ^ 3 * gi| := abs_mul_two_cutoffs_le _ _ _ hx ⟨zero_le_one, le_rfl⟩
      _ = d ^ 3 * |gi| := by rw [abs_mul, abs_of_pos (pow_pos hd _)]
      _ ≤ d ^ 3 * (P / d) := mul_le_mul_of_nonneg_left hgi (pow_pos hd _).le
      _ = d ^ 2 * P := by field_simp [hd.ne']
  calc
    _ ≤ |3 * d ^ 2 * di * x * g + d ^ 3 * xi * g| + |d ^ 3 * x * gi| :=
      abs_add_le _ _
    _ ≤ (|3 * d ^ 2 * di * x * g| + |d ^ 3 * xi * g|) + |d ^ 3 * x * gi| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (3 * d ^ 2 + d ^ 3 * X) + d ^ 2 * P :=
      add_le_add (add_le_add hfirst hsecond) hthird

theorem ellipticWeight_partial_bound {b c M X : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hM : 0 ≤ M)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1) (i : Fin 2)
    (hchii : |coordPartial i chi p| ≤ X) (hKi : |coordPartial i K p| ≤ M) :
    |coordPartial i (ellipticWeight b c chi K) p| ≤
      2 * Real.sqrt (ellipticWeight b c chi K p) *
        (3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
          edgeDistance b p ^ 2 * ((2 * transitionDerivativeBound / c) * (M + c))) := by
  have hGRange : 0 ≤ ellipticGate b c K p ∧ ellipticGate b c K p ≤ 1 :=
    intervalCutoff_range _ _ _
  have hAi : |coordPartial i (ellipticAmplitude b c chi K) p| ≤
      3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
        edgeDistance b p ^ 2 * ((2 * transitionDerivativeBound / c) * (M + c)) := by
    rw [ellipticAmplitude_partial hchi hK hd.ne' i]
    apply amplitude_derivative_algebra_bound hd hchiRange hGRange _ hchii
      (ellipticGate_partial_bound hc hd hM hK i hKi)
    rw [edgeDistance_partial]
    fin_cases i <;> norm_num
  have hAmp : 0 ≤ ellipticAmplitude b c chi K p :=
    mul_nonneg (mul_nonneg (pow_pos hd _).le hchiRange.1) hGRange.1
  have hsqrt : Real.sqrt (ellipticWeight b c chi K p) = ellipticAmplitude b c chi K p := by
    rw [← ellipticAmplitude_sq, Real.sqrt_sq hAmp]
  rw [ellipticWeight_partial hchi hK hd.ne' i, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num) hAmp), hsqrt]
  exact mul_le_mul_of_nonneg_left hAi (mul_nonneg (by norm_num) hAmp)

theorem ellipticWeight_contDiffOn {chi K : Coord → ℝ} {U : Set Coord}
    (b c : ℝ) (hchi : ContDiffOn ℝ ∞ chi U) (hK : ContDiffOn ℝ ∞ K U)
    (hd : ∀ p ∈ U, p 1 < b) : ContDiffOn ℝ ∞ (ellipticWeight b c chi K) U := by
  have hD : ContDiffOn ℝ ∞ (edgeDistance b) U :=
    contDiffOn_const.sub (contDiffOn_apply ℝ ℝ 1 U)
  have hratio := hK.div hD (fun p hp => (sub_pos.mpr (hd p hp)).ne')
  exact ((hD.pow 6).mul (hchi.pow 2)).mul
    (((ellipticPhi_contDiff c).comp_contDiffOn hratio).pow 2)

theorem ellipticWeight_nonneg (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    0 ≤ ellipticWeight b c chi K p := by
  unfold ellipticWeight
  positivity

theorem ellipticWeight_le_distance_six (b c : ℝ) (chi K : Coord → ℝ) (p : Coord)
    (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    ellipticWeight b c chi K p ≤ (edgeDistance b p) ^ 6 := by
  have hphi := intervalCutoff_range (c / 2) c (K p / edgeDistance b p)
  have hc2 : (chi p) ^ 2 ≤ 1 := by nlinarith [hchi.1, hchi.2]
  have hp2 : (ellipticPhi c (K p / edgeDistance b p)) ^ 2 ≤ 1 := by
    change (intervalCutoff (c / 2) c (K p / edgeDistance b p)) ^ 2 ≤ 1
    nlinarith
  have hprod : (chi p) ^ 2 * (ellipticPhi c (K p / edgeDistance b p)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (chi p), sq_nonneg (ellipticPhi c (K p / edgeDistance b p))]
  have hpow : 0 ≤ (edgeDistance b p) ^ 6 := by positivity
  unfold ellipticWeight
  nlinarith [mul_le_mul_of_nonneg_left hprod hpow]

theorem ellipticWeight_edge_zero (b c : ℝ) (chi K : Coord → ℝ) (p : Coord)
    (hp : p 1 = b) : ellipticWeight b c chi K p = 0 := by
  simp [ellipticWeight, edgeDistance, hp]

theorem ellipticWeight_tendsto_edge_zero (b c : ℝ) (chi K : Coord → ℝ)
    (hchi : ∀ q, 0 ≤ chi q ∧ chi q ≤ 1) {p : Coord} (hp : p 1 = b) :
    Tendsto (ellipticWeight b c chi K) (𝓝 p) (𝓝 0) := by
  have hD : Continuous (fun q : Coord => (edgeDistance b q) ^ 6) :=
    (continuous_const.sub (continuous_apply 1)).pow 6
  have ht : Tendsto (fun q : Coord => (edgeDistance b q) ^ 6) (𝓝 p) (𝓝 0) := by
    simpa only [edgeDistance, hp, sub_self, zero_pow (by norm_num : 6 ≠ 0)] using hD.tendsto p
  exact squeeze_zero (ellipticWeight_nonneg b c chi K)
    (fun q => ellipticWeight_le_distance_six b c chi K q (hchi q)) ht

theorem ellipticWeight_flux_tendsto_edge_zero (b c : ℝ) (chi K H : Coord → ℝ)
    (hchi : ∀ q, 0 ≤ chi q ∧ chi q ≤ 1) {p : Coord} (hp : p 1 = b)
    (hH : ContinuousAt H p) :
    Tendsto (fun q => ellipticWeight b c chi K q * H q) (𝓝 p) (𝓝 0) := by
  simpa only [zero_mul] using (ellipticWeight_tendsto_edge_zero b c chi K hchi hp).mul hH

theorem ellipticWeight_partial_zero_of_zero (b c : ℝ) (chi K : Coord → ℝ)
    {p : Coord} (hweight : DifferentiableAt ℝ (ellipticWeight b c chi K) p)
    (hv : ellipticWeight b c chi K p = 0) (i : Fin 2) :
    coordPartial i (ellipticWeight b c chi K) p = 0 := by
  have hmin : IsLocalMin (ellipticWeight b c chi K) p :=
    Filter.Eventually.of_forall (fun q => by
      rw [hv]
      exact ellipticWeight_nonneg b c chi K q)
  unfold coordPartial
  rw [hmin.hasFDerivAt_eq_zero hweight.hasFDerivAt]
  rfl

theorem ellipticWeight_pos_implies_curvature {b c : ℝ} {chi K : Coord → ℝ}
    {p : Coord} (hc : 0 < c) (hd : p 1 < b)
    (hv : 0 < ellipticWeight b c chi K p) :
    c / 2 * edgeDistance b p < K p := by
  have hdist : 0 < edgeDistance b p := sub_pos.mpr hd
  by_contra h
  have hratio : K p / edgeDistance b p ≤ c / 2 :=
    (div_le_iff₀ hdist).mpr (by linarith)
  have hz := ellipticPhi_zero hc hratio
  simp [ellipticWeight, hz] at hv

end SmoothLocal.Weighted

end

end OAI
