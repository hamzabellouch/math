import Mathlib
import OAI.Analysis.AffineBernstein.Basic
import OAI.Analysis.AffineBernstein.ConvexLocalLimits

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section InteriorLimits
open Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Quantitative inner containment from distance-function closeness. This is
an actual projection argument for convex bodies, not an assumed stability axiom. -/
theorem ball_subset_of_infDist_lt {K : Set E} (hK : IsClosed K)
    (hcv : Convex ℝ K) (hne : K.Nonempty) (a : E) {r : ℝ} (hr : 0 < r)
    (happ : ∀ y ∈ Metric.closedBall a r, infDist y K < r / 2) :
    Metric.ball a (r / 2) ⊆ K := by
  intro x hx
  by_contra hxn
  obtain ⟨p, hp, hpx⟩ := hK.exists_infDist_eq_dist hne x
  have hd : 0 < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by rintro rfl; exact hxn hp))
  have hproj : ∀ z ∈ K, ⟪x - p, z - p⟫_ℝ ≤ 0 := by
    apply (norm_eq_iInf_iff_real_inner_le_zero hcv hp).mp
    simpa only [infDist_eq_iInf, dist_eq_norm] using hpx.symm
  let v : E := ‖x - p‖⁻¹ • (x - p)
  have hvn : ‖v‖ = 1 := by simp [v, norm_smul, hd.ne']
  have hvp : ⟪v, x - p⟫_ℝ = ‖x - p‖ := by
    simp only [v, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hvproj : ∀ z ∈ K, ⟪v, z - p⟫_ℝ ≤ 0 := by
    intro z hz
    simp only [v, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hd.le) (hproj z hz)
  let y : E := x + (r / 2) • v
  have hxa : ‖x - a‖ < r / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hy : y ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : y - a = (x - a) + (r / 2) • v := by dsimp [y]; abel
    rw [heq]
    calc
      _ ≤ ‖x - a‖ + ‖(r / 2) • v‖ := norm_add_le _ _
      _ ≤ r := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr), hvn]; linarith
  obtain ⟨z, hz, hzdist⟩ := hK.exists_infDist_eq_dist hne y
  have hyz : ‖y - z‖ < r / 2 := by simpa [hzdist, dist_eq_norm] using happ y hy
  have hei : ⟪v, y - z⟫_ℝ = ‖x - p‖ + r / 2 - ⟪v, z - p⟫_ℝ := by
    have heq : y - z = (x - p) + (r / 2) • v - (z - p) := by dsimp [y]; abel
    rw [heq, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hvp, hvn]
    ring
  have hCS : ⟪v, y - z⟫_ℝ ≤ ‖y - z‖ := by simpa [hvn] using real_inner_le_norm v (y - z)
  have he := hvproj z hz
  rw [hei] at hCS
  linarith

/- An interior ball of the limit has a fixed smaller ball lying in the
interiors of all late approximants. -/
theorem LocalDistanceConverges.eventually_ball_subset_interior
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {a : E} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ C) :
    ∀ᶠ j in atTop, Metric.ball a (r / 2) ⊆ interior (Cj j) := by
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp h (Metric.closedBall a r)
    (isCompact_closedBall a r)
  have he := Metric.tendstoUniformlyOn_iff.mp hU (r / 2) (half_pos hr)
  filter_upwards [he] with j hj
  have hsub : Metric.ball a (r / 2) ⊆ Cj j :=
    ball_subset_of_infDist_lt (hclj j) (hcvj j) (hnej j) a hr (fun y hy => by
      have he := hj y hy
      rw [infDist_zero_of_mem (hball hy), dist_zero_left, Real.norm_eq_abs,
        abs_of_nonneg infDist_nonneg] at he
      exact he)
  exact isOpen_ball.subset_interior_iff.mpr hsub

/- Compact subsets of the interior are eventually interior subsets of the
approximants, as required by the model normalization argument. -/
theorem LocalDistanceConverges.eventually_compact_subset_interior
    {Cj : ℕ → Set E} {C S : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) (hS : IsCompact S)
    (hSC : S ⊆ interior C) : ∀ᶠ j in atTop, S ⊆ interior (Cj j) := by
  classical
  have hex : ∀ x : S, ∃ r > 0, Metric.closedBall (x : E) r ⊆ C := by
    intro x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (x : E) (hSC x.2)
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (by linarith)).trans
      (hball.trans interior_subset)⟩
  choose r hr hball using hex
  obtain ⟨t, ht⟩ := hS.elim_nhds_subcover' (fun x hx => Metric.ball x (r ⟨x, hx⟩ / 2))
    (fun x hx => Metric.ball_mem_nhds x (half_pos (hr ⟨x, hx⟩)))
  have he : ∀ x ∈ t, ∀ᶠ j in atTop, Metric.ball (x : E) (r x / 2) ⊆ interior (Cj j) :=
    fun x _ => h.eventually_ball_subset_interior hclj hcvj hnej (hr x) (hball x)
  filter_upwards [(t.eventually_all).mpr he] with j hj
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact hj y hyt hxy

end InteriorLimits

open Filter Metric
open scoped Topology Pointwise

/- The geometric conditions of a k-model, in its distinguished coordinates.
Membership in the affine local-limit family is separate from these conditions. -/
structure IsModelShape {k m : ℕ} (C : Set (Space k × Space m)) : Prop where
  closed : IsClosed C
  convex : Convex ℝ C
  interior_nonempty : (interior C).Nonempty
  orthant : ∀ s : Space k, (∀ i, 0 ≤ s i) → (s, 0) ∈ C
  support : ∀ p ∈ C, ∀ i, 0 ≤ p.1 i
  compact_cap : ∀ T : ℝ, 0 ≤ T → IsCompact (C ∩ {p | ∑ i, p.1 i ≤ T})

/- The transverse fiber, including lower-dimensional and boundary fibers. -/
def modelFiber {k m : ℕ} (C : Set (Space k × Space m)) (s : Space k) : Set (Space m) :=
  {y | (s, y) ∈ C}

/- The ray containment recession argument in geometry.tex does not need
full-dimensionality. -/
theorem closed_convex_add_of_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hc : IsClosed C) (hv : Convex ℝ C) {x v : E}
    (hx : x ∈ C) (hray : ∀ t : ℝ, 0 ≤ t → t • v ∈ C) : x + v ∈ C := by
  have htend : Tendsto (fun t : ℝ => (1 - t) • x + v) (𝓝[>] 0) (𝓝 (x + v)) := by
    have hc : Continuous (fun t : ℝ => (1 - t) • x + v) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hc.mem_of_tendsto htend
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
  have ht0 : 0 < t := ht
  have h := hv hx (hray t⁻¹ (inv_nonneg.mpr ht0.le))
    (show 0 ≤ 1 - t by linarith) ht0.le (by ring)
  simpa only [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul] using h

namespace IsModelShape

variable {k m : ℕ} {C : Set (Space k × Space m)} (h : IsModelShape C)
include h

theorem zero_mem : (0 : Space k × Space m) ∈ C := by
  exact h.orthant 0 (by simp)

theorem add_nonnegative_base {s v : Space k} {y : Space m}
    (hy : (s, y) ∈ C) (hv : ∀ i, 0 ≤ v i) : (s + v, y) ∈ C := by
  have hh := closed_convex_add_of_ray h.closed h.convex hy (v := (v, 0)) (by
    intro t ht
    simpa only [Prod.smul_mk, smul_zero] using
      h.orthant (t • v) (fun i => mul_nonneg ht (hv i)))
  simpa using hh

theorem fiber_mono {s t : Space k} (hst : ∀ i, s i ≤ t i) :
    modelFiber C s ⊆ modelFiber C t := by
  intro y hy
  have hh := h.add_nonnegative_base hy (v := t - s) (by intro i; exact sub_nonneg.mpr (hst i))
  simpa only [add_sub_cancel, modelFiber, mem_ofPred_eq] using hh

theorem fiber_zero {s : Space k} (hs : ∀ i, 0 ≤ s i) : (0 : Space m) ∈ modelFiber C s :=
  h.orthant s hs

theorem fiber_convex (s : Space k) : Convex ℝ (modelFiber C s) := by
  intro x hx y hy a b ha hb hab
  have hh := h.convex hx hy ha hb hab
  change (s, a • x + b • y) ∈ C
  simpa only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] using hh

theorem fiber_closed (s : Space k) : IsClosed (modelFiber C s) :=
  h.closed.preimage (continuous_const.prodMk continuous_id)

theorem fiber_compact {s : Space k} (hs : ∀ i, 0 ≤ s i) : IsCompact (modelFiber C s) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨h.fiber_closed s, ?_⟩
  have hc := (h.compact_cap (∑ i, s i) (Finset.sum_nonneg fun i _ => hs i)).image continuous_snd
  apply hc.isBounded.subset
  intro y hy
  exact ⟨(s, y), ⟨hy, show ∑ i, s i ≤ ∑ i, s i from le_rfl⟩, rfl⟩

theorem fiber_contract {s : Space k} {a : ℝ} (ha : 1 ≤ a) :
    modelFiber C (a • s) ⊆ a • modelFiber C s := by
  have hp : 0 < a := by linarith
  intro y hy
  have hh := h.convex.smul_mem_of_zero_mem h.zero_mem hy
    (show a⁻¹ ∈ Icc (0 : ℝ) 1 from ⟨inv_nonneg.mpr hp.le, inv_le_one_of_one_le₀ ha⟩)
  have hm : a⁻¹ • y ∈ modelFiber C s := by
    simpa only [modelFiber, mem_ofPred_eq, Prod.smul_mk, smul_smul,
      inv_mul_cancel₀ hp.ne', one_smul] using hh
  exact Set.mem_smul_set.mpr ⟨a⁻¹ • y, hm, by simp [smul_smul, hp.ne']⟩

/- Every strictly positive fiber is full dimensional; this proof also covers
m=0, using the ordinary topology of the zero-dimensional space. -/
theorem fiber_interior_nonempty {s : Space k} (hs : ∀ i, 0 < s i) :
    (interior (modelFiber C s)).Nonempty := by
  obtain ⟨p, hp⟩ := h.interior_nonempty
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hfit : ∀ i : Fin k, ∀ᶠ t : ℝ in 𝓝[>] 0, t * p.1 i < s i := by
    intro i
    exact ((continuous_id.mul continuous_const).tendsto 0 |>.mono_left nhdsWithin_le_nhds).eventually_lt_const
      (by simpa using hs i)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht0, ht1, hti⟩ := (hpos.and (hsmall.and (Filter.eventually_all.mpr hfit))).exists
  have ht : 0 < t := ht0
  have hsub : Metric.ball (t • p.2) (t * r) ⊆ modelFiber C s := by
    intro y hy
    have hyr : dist (t⁻¹ • y) p.2 < r := by
      have he : t⁻¹ • y - p.2 = t⁻¹ • (y - t • p.2) := by simp [smul_sub, smul_smul, ht.ne']
      rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), ← dist_eq_norm]
      have hy' : dist y (t • p.2) < t * r := hy
      exact (inv_mul_lt_iff₀ ht).mpr hy'
    have hmem : (p.1, t⁻¹ • y) ∈ C := hball (by simpa [Prod.dist_eq] using hyr)
    have hc := h.convex.smul_mem_of_zero_mem h.zero_mem hmem ⟨ht.le, ht1⟩
    have hc' : (t • p.1, y) ∈ C := by simpa [Prod.smul_mk, smul_smul, ht.ne'] using hc
    have hh := h.add_nonnegative_base hc' (v := s - t • p.1) (by intro i; exact sub_nonneg.mpr (hti i).le)
    simpa [modelFiber] using hh
  exact ⟨t • p.2, mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.ball_mem_nhds _ (mul_pos ht hr)) hsub)⟩

/- Monotonicity and homothety turn a bound on the distinguished fiber into
a uniform bound on every fixed base box. -/
theorem fiber_box_bound {R T : ℝ} (hT : 1 ≤ T)
    (hR : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) ⊆ Metric.closedBall 0 R)
    {s : Space k} (hs : ∀ i, s i ≤ T) {y : Space m} (hy : y ∈ modelFiber C s) :
    ‖y‖ ≤ T * R := by
  have hp : 0 < T := by linarith
  have hmono : y ∈ modelFiber C (T • WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) :=
    h.fiber_mono (fun i => by simpa using hs i) hy
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp (h.fiber_contract hT hmono)
  have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hz
  simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hp] using mul_le_mul_of_nonneg_left hzR hp.le

end IsModelShape

end AffineBernstein
end

end OAI
