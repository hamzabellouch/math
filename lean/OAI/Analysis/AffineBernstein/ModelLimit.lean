import Mathlib
import OAI.Analysis.AffineBernstein.InteriorLimits

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise

open Filter Metric
open scoped Topology Pointwise

variable {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}

/- Normalized model limits retain the genuine geometric model conditions.
The fixed inner balls prevent collapse; the distinguished-fiber outer bound
controls every cap by the already proved recession/fiber inequalities. -/
theorem LocalDistanceConverges.isModelShape_of_normalized
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    (hclosed : IsClosed C) (hconvex : Convex ℝ C) (hne : C.Nonempty)
    {cj : ℕ → Space m} {c : Space m} (hc : Tendsto cj atTop (𝓝 c))
    {R : ℝ}
    (hinner : ∀ j, closedBall (cj j) 1 ⊆ modelFiber (Cj j)
      (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))))
    (houter : ∀ j, modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) ⊆ closedBall 0 R) :
    IsModelShape C := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  have hsupp : ∀ p ∈ C, ∀ i, 0 ≤ p.1 i := by
    intro p hp i
    obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating (fun j => (hj j).closed)
      (fun j => ⟨0, (hj j).zero_mem⟩) hp
    have ht : Tendsto (fun j => (pj j).1 i) atTop (𝓝 (p.1 i)) := by
      exact (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst).tendsto p).comp hpt
    exact ge_of_tendsto ht (Eventually.of_forall fun j => (hj j).support _ (hpj j) i)
  refine ⟨hclosed, hconvex, ?_, ?_, hsupp, ?_⟩
  · have hball : ball (2 • e, c) (1 / 2 : ℝ) ⊆ C := by
      intro q hq
      have hd : dist q.1 (2 • e) < (1 / 2 : ℝ) ∧ dist q.2 c < (1 / 2 : ℝ) := by
        simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
      have hbase : ∀ i, e i ≤ q.1 i := by
        intro i
        have hn := PiLp.norm_apply_le (q.1 - 2 • e) i
        have hi : |q.1 i - 2| < (1 / 2 : ℝ) := by
          have hn' : |q.1 i - 2| ≤ ‖q.1 - 2 • e‖ := by simpa [e, Real.norm_eq_abs] using hn
          exact hn'.trans_lt (by simpa [dist_eq_norm] using hd.1)
        simpa [e] using (by linarith [(abs_lt.mp hi).1] : (1 : ℝ) ≤ q.1 i)
      have hm : ∀ j, (q.1, cj j + (q.2 - c)) ∈ Cj j := by
        intro j
        apply (hj j).fiber_mono hbase
        apply hinner j
        have hn' : ‖q.2 - c‖ ≤ (1 / 2 : ℝ) := by simpa [dist_eq_norm] using hd.2.le
        simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using
          hn'.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
      apply h.mem_of_tendsto hclosed hne hm
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => q.1) atTop (𝓝 q.1)).prodMk_nhds
        (hc.add_const (q.2 - c))
    exact ⟨(2 • e, c), mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2)) hball)⟩
  · intro s hs
    exact h.mem_of_tendsto hclosed hne (fun j => (hj j).orthant s hs) tendsto_const_nhds
  · intro T hT
    let B : Set (Space k) := (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm ''
      Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => T)
    have hB : IsCompact B := isCompact_Icc.image (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm.continuous
    have hcapclosed : IsClosed (C ∩ {p | ∑ i, p.1 i ≤ T}) := hclosed.inter
      (isClosed_le (by fun_prop) continuous_const)
    apply (hB.prod (isCompact_closedBall (0 : Space m) ((T + 1) * R))).of_isClosed_subset hcapclosed
    rintro p ⟨hp, hpT⟩
    have hsT : ∀ i, p.1 i ≤ T := by
      intro i
      exact (Finset.single_le_sum (fun a _ => hsupp p hp a) (Finset.mem_univ i)).trans hpT
    refine ⟨?_, ?_⟩
    · refine ⟨fun i => p.1 i, ⟨(fun i => hsupp p hp i), (fun i => hsT i)⟩, ?_⟩
      rfl
    · obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating (fun j => (hj j).closed)
        (fun j => ⟨0, (hj j).zero_mem⟩) hp
      have hcoord : ∀ i : Fin k, ∀ᶠ j in atTop, (pj j).1 i ≤ T + 1 := by
        intro i
        have ht : Tendsto (fun j => (pj j).1 i) atTop (𝓝 (p.1 i)) :=
          (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst).tendsto p).comp hpt
        exact ht.eventually_le_const (by linarith [hsT i])
      have hb : ∀ᶠ j in atTop, ‖(pj j).2‖ ≤ (T + 1) * R := by
        filter_upwards [Filter.eventually_all.mpr hcoord] with j hbase
        exact (hj j).fiber_box_bound (by linarith) (houter j) hbase (hpj j)
      have ht := (((continuous_snd.tendsto p).comp hpt).norm)
      simpa only [mem_closedBall, dist_zero_right] using le_of_tendsto ht hb

/- The shrinking factor avoids any positivity assumption on approximating
base coordinates. It tends to one and contracts each coordinate below one. -/
theorem model_base_contraction (s : Space k) (i : Fin k) :
    (1 + ‖s - WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))‖)⁻¹ * s i ≤ 1 := by
  have hn := PiLp.norm_apply_le (s - WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) i
  have hi : s i - 1 ≤ ‖s - WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))‖ :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hn)
  apply (inv_mul_le_iff₀ (by positivity : 0 < 1 + ‖s - WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))‖)).mpr
  linarith

/- Exact-fiber approximation in geometry.tex:285–300. The actual contracting
points are used, not an assumed commutation of slicing with local limits. -/
theorem LocalDistanceConverges.exists_exact_fiber_approximating
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    {y : Space m} (hy : y ∈ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) :
    ∃ yj : ℕ → Space m,
      (∀ j, yj j ∈ modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) ∧
      Tendsto yj atTop (𝓝 y) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating (fun j => (hj j).closed)
    (fun j => ⟨0, (hj j).zero_mem⟩) hy
  let a : ℕ → ℝ := fun j => (1 + ‖(pj j).1 - e‖)⁻¹
  have ha0 : ∀ j, 0 < a j := fun j => inv_pos.mpr (by positivity)
  have ha1 : ∀ j, a j ≤ 1 := fun j => inv_le_one_of_one_le₀ (by linarith [norm_nonneg ((pj j).1 - e)])
  refine ⟨fun j => a j • (pj j).2, ?_, ?_⟩
  · intro j
    have hh := (hj j).convex.smul_mem_of_zero_mem (hj j).zero_mem (hpj j) ⟨(ha0 j).le, ha1 j⟩
    have hbase : ∀ i, (a j • (pj j).1) i ≤ e i := by
      intro i
      simpa [a, e] using model_base_contraction (pj j).1 i
    exact (hj j).fiber_mono hbase hh
  · have hp1 : Tendsto (fun j => (pj j).1 - e) atTop (𝓝 0) := by
      simpa [e] using ((continuous_fst.tendsto _).comp hpt).sub_const e
    have ha : Tendsto a atTop (𝓝 1) := by
      simpa [a, one_div] using ((tendsto_const_nhds.add hp1.norm).inv₀ (by norm_num : (1:ℝ) + ‖(0 : Space k)‖ ≠ 0))
    simpa using ha.smul ((continuous_snd.tendsto _).comp hpt)

/- Uniform reverse Hausdorff inclusion follows by compactness of the actual
positive limit fiber and the preceding exact approximations. -/
theorem LocalDistanceConverges.eventually_infDist_fiber_lt_uniform
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    (hC : IsModelShape C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ y ∈ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))),
      infDist y (modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) < ε := by
  classical
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  let F := modelFiber C e
  have hc : IsCompact F := hC.fiber_compact (by simp [e])
  have hat : ∀ y ∈ F, ∀ᶠ j in atTop, infDist y (modelFiber (Cj j) e) < ε / 2 := by
    intro y hy
    obtain ⟨yj, hyj, hyt⟩ := h.exists_exact_fiber_approximating hj hy
    have hd : Tendsto (fun j => dist y (yj j)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).dist hyt
    filter_upwards [hd.eventually_lt_const (half_pos hε)] with j hj
    exact (infDist_le_dist_of_mem (hyj j)).trans_lt hj
  obtain ⟨t, htF, ht⟩ := hc.elim_nhds_subcover (fun y => Metric.ball y (ε / 2))
    (fun y _ => Metric.ball_mem_nhds y (half_pos hε))
  filter_upwards [(t.eventually_all).mpr (fun y hy => hat y (htF y hy))] with j hj y hy
  obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (ht hy)
  have hd : dist y z < ε / 2 := hyz
  exact (infDist_le_infDist_add_dist (x := y) (y := z)).trans_lt (by linarith [hj z hzt])

/- Exact-fiber Hausdorff convergence with a common outer radius. This is
stronger than pointwise local convergence but follows from the model recession
structure; arbitrary slices of arbitrary converging bodies need not converge. -/
theorem LocalDistanceConverges.tendsto_hausdorffDist_fibers
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    (hC : IsModelShape C) {R : ℝ}
    (hR : ∀ j, modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) ⊆ closedBall 0 R) :
    Tendsto (fun j => hausdorffDist (modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))))
      (modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))))) atTop (𝓝 0) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  let F := modelFiber C e
  apply tendsto_order.2
  constructor
  · intro a ha; exact Eventually.of_forall fun _ => ha.trans_le hausdorffDist_nonneg
  · intro ε hε
    let S : Set (Space m) := closedBall 0 R ∩ {y | ε / 2 ≤ infDist y F}
    have hSc : IsCompact S := (isCompact_closedBall (0 : Space m) R).inter_right
      (isClosed_le continuous_const (continuous_infDist_pt F))
    have hdis : Disjoint C ((fun y : Space m => (e, y)) '' S) := by
      rw [Set.disjoint_left]
      rintro p hp ⟨y, hy, rfl⟩
      have he : ε / 2 ≤ infDist y F := hy.2
      rw [infDist_zero_of_mem (s := F) hp] at he
      linarith
    have he := h.eventually_disjoint_compact hC.closed ⟨0, hC.zero_mem⟩
      (hSc.image (continuous_const.prodMk continuous_id)) hdis
    have hr := h.eventually_infDist_fiber_lt_uniform hj hC (half_pos hε)
    filter_upwards [he, hr] with j hjS hjrev
    have hfwd : ∀ y ∈ modelFiber (Cj j) e, infDist y F < ε / 2 := by
      intro y hy
      by_contra hn
      exact Set.disjoint_left.mp hjS hy ⟨y, ⟨hR j hy, not_lt.mp hn⟩, rfl⟩
    exact (hausdorffDist_le_of_infDist (half_pos hε).le
      (fun y hy => (hfwd y hy).le) (fun y hy => (hjrev y hy).le)).trans_lt (by linarith)

/- A failure of all growing centering constants forces the origin onto the
boundary of the limit fiber. No centering stability is assumed. -/
theorem LocalDistanceConverges.zero_mem_frontier_fiber_of_asymmetry
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    (hC : IsModelShape C) {R : ℝ}
    (hR : ∀ j, modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) ⊆ closedBall 0 R)
    (hfail : ∀ j : ℕ, 1 ≤ j →
      ¬ -(modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) ⊆
        (j : ℝ) • modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) :
    (0 : Space m) ∈ frontier (modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  let F : Set (Space m) := modelFiber C e
  have hz : (0 : Space m) ∈ F := hC.fiber_zero (by simp [e])
  have hnint : (0 : Space m) ∉ interior F := by
    intro hzi
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hzi
    have hclosedball : closedBall (0 : Space m) (r / 2) ⊆ F :=
      (closedBall_subset_ball (by linarith)).trans (hball.trans interior_subset)
    have he := h.eventually_infDist_fiber_lt_uniform hj hC (show 0 < r / 4 by linarith)
    have hinner : ∀ᶠ j in atTop, ball (0 : Space m) (r / 4) ⊆ modelFiber (Cj j) e := by
      filter_upwards [he] with j hjdist
      simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using
        (ball_subset_of_infDist_lt ((hj j).fiber_closed e) ((hj j).fiber_convex e)
          ⟨0, (hj j).fiber_zero (by simp [e])⟩ 0 (half_pos hr)
          (fun y hy => by
            rw [show r / 2 / 2 = r / 4 by ring]
            exact hjdist y (hclosedball hy)))
    obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (4 * R / r))
    obtain ⟨j, hji, hjN⟩ := (hinner.and (eventually_ge_atTop N)).exists
    have hjlarge : max 1 (4 * R / r) < (j : ℝ) := hN.trans_le (by exact_mod_cast hjN)
    have hj1 : 1 ≤ j := by have he := (le_max_left 1 (4 * R / r)).trans_lt hjlarge; exact_mod_cast he.le
    have hjpos : 0 < (j : ℝ) := by
      have hh : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
    have hmult : 4 * R < (j : ℝ) * r := (div_lt_iff₀ hr).mp
      ((le_max_right 1 (4 * R / r)).trans_lt hjlarge)
    apply hfail j hj1
    intro x hx
    change -x ∈ modelFiber (Cj j) e at hx
    have hynorm : ‖x‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hR j hx
    have hm : (j : ℝ)⁻¹ • x ∈ modelFiber (Cj j) e := by
      apply hji
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hjpos)]
      apply (inv_mul_lt_iff₀ hjpos).mpr
      nlinarith
    exact mem_smul_set.mpr ⟨(j : ℝ)⁻¹ • x, hm, by simp [smul_smul, hjpos.ne']⟩
  rw [frontier, (hC.fiber_closed e).closure_eq]
  exact ⟨hz, hnint⟩

/- A fiber support at zero extends to the whole model by the same actual
contraction and recession operation used for exact-fiber approximation. -/
theorem IsModelShape.support_from_fiber (hC : IsModelShape C)
    (ell : Space m →L[ℝ] ℝ)
    (hell : ∀ y ∈ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))), 0 ≤ ell y) :
    ∀ p ∈ C, 0 ≤ ell p.2 := by
  intro p hp
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  let a : ℝ := (1 + ‖p.1 - e‖)⁻¹
  have ha : 0 < a := inv_pos.mpr (by positivity)
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg (p.1 - e)])
  have hm := hC.convex.smul_mem_of_zero_mem hC.zero_mem hp ⟨ha.le, ha1⟩
  have hbase : ∀ i, (a • p.1) i ≤ e i := by
    intro i; simpa [a, e] using model_base_contraction p.1 i
  have hs := hell (a • p.2) (hC.fiber_mono hbase hm)
  simpa only [map_smul, smul_eq_mul, mul_nonneg_iff_of_pos_left ha] using hs

/- The nonzero supporting functional whose new positive coordinate is used
in the thin-slice blowup. Hahn–Banach is reused from pinned Mathlib. -/
theorem IsModelShape.exists_global_support_of_zero_boundary (hC : IsModelShape C)
    (hzero : (0 : Space m) ∉ interior (modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))))) :
    ∃ ell : Space m →L[ℝ] ℝ, ell ≠ 0 ∧ (∀ p ∈ C, 0 ≤ ell p.2) := by
  obtain ⟨f, hf, hF⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (hC.fiber_convex (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) hzero
    (hC.fiber_interior_nonempty (by simp))
  refine ⟨-f, neg_ne_zero.mpr hf, hC.support_from_fiber (-f) ?_⟩
  intro y hy
  simpa only [neg_apply, map_zero, neg_nonneg] using hF y hy

end AffineBernstein
end

end OAI
