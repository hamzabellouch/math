import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Topology NNReal

open Filter Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- The local distance-function topology used in geometry.tex:70–101. Sets
are separately required to be nonempty and closed when those properties enter. -/
def LocalDistanceConverges (Cj : ℕ → Set E) (C : Set E) : Prop :=
  TendstoLocallyUniformly (fun j x => infDist x (Cj j)) (fun x => infDist x C) atTop

omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.pointwise {Cj : ℕ → Set E} {C : Set E}
    (h : LocalDistanceConverges Cj C) (x : E) :
    Tendsto (fun j => infDist x (Cj j)) atTop (𝓝 (infDist x C)) := by
  exact ((tendstoLocallyUniformly_iff_forall_isCompact.mp h) {x}
    (isCompact_singleton)).tendsto_at (mem_singleton x)

/- Every point of a local limit has an actual sequence of nearby points
in the approximating closed convex bodies (convexity is not needed here). -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.exists_approximating {Cj : ℕ → Set E} {C : Set E}
    (h : LocalDistanceConverges Cj C) (hcl : ∀ j, IsClosed (Cj j))
    (hne : ∀ j, (Cj j).Nonempty) {x : E} (hx : x ∈ C) :
    ∃ xj : ℕ → E, (∀ j, xj j ∈ Cj j) ∧ Tendsto xj atTop (𝓝 x) := by
  choose xj hmem heq using fun j => (hcl j).exists_infDist_eq_dist (hne j) x
  refine ⟨xj, hmem, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_comm, ← heq, infDist_zero_of_mem hx] using h.pointwise x

/- Local convergence prevents approximants from meeting any fixed compact
set disjoint from the closed limit. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.eventually_disjoint_compact
    {Cj : ℕ → Set E} {C S : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hne : C.Nonempty) (hS : IsCompact S)
    (hdis : Disjoint C S) : ∀ᶠ j in atTop, Disjoint (Cj j) S := by
  rcases S.eq_empty_or_nonempty with rfl | hSn
  · simp
  obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn hSn (continuous_infDist_pt C).continuousOn
  have hxnot : x ∉ C := fun hc => Set.disjoint_left.mp hdis hc hx
  have hδ : 0 < infDist x C := (hcl.notMem_iff_infDist_pos hne).mp hxnot
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp h S hS
  have he := Metric.tendstoUniformlyOn_iff.mp hU (infDist x C) hδ
  filter_upwards [he] with j hj
  rw [Set.disjoint_left]
  intro y hyC hyS
  have hd := hj y hyS
  have hmin' : infDist x C ≤ infDist y C := hmin hyS
  rw [infDist_zero_of_mem hyC, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at hd
  linarith

/- Limits of convergent points of approximants belong to the local limit. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.mem_of_tendsto
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hne : C.Nonempty) {xj : ℕ → E}
    (hmem : ∀ j, xj j ∈ Cj j) {x : E} (hx : Tendsto xj atTop (𝓝 x)) : x ∈ C := by
  apply (hcl.mem_iff_infDist_zero hne).mpr
  have hle : ∀ j, infDist x (Cj j) ≤ dist x (xj j) :=
    fun j => infDist_le_dist_of_mem (hmem j)
  have hd : Tendsto (fun j => dist x (xj j)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).dist hx
  exact le_antisymm (le_of_tendsto_of_tendsto (h.pointwise x) hd (Filter.Eventually.of_forall hle))
    infDist_nonneg

/- Uniform cap compactness, geometry.tex:104–125. The proof traps a chord
on a fixed compact sphere, rather than choosing escaping directions. -/
theorem LocalDistanceConverges.eventually_bounded_caps
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hclj : ∀ j, IsClosed (Cj j))
    (hcvj : ∀ j, Convex ℝ (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (ell : E →L[ℝ] ℝ) (b : ℝ)
    (hbounded : Bornology.IsBounded (C ∩ {x | ell x ≤ b}))
    {q : E} (hq : q ∈ C) (hqb : ell q < b) :
    ∃ R > 0, ∀ᶠ j in atTop, Cj j ∩ {x | ell x ≤ b} ⊆ Metric.ball 0 R := by
  obtain ⟨R, hR, hcap⟩ := hbounded.subset_ball_lt (0 : ℝ) (0 : E)
  have hqR : ‖q‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hcap ⟨hq, hqb.le⟩
  let S : Set E := Metric.sphere (0 : E) R ∩ {x | ell x ≤ b}
  have hSc : IsCompact S := (isCompact_sphere (0 : E) R).inter_right
    (isClosed_le ell.continuous continuous_const)
  have hSd : Disjoint C S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    have he : ‖x‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hxs.1
    have hl : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hcap ⟨hx, hxs.2⟩
    linarith
  obtain ⟨qj, hqj, hqjt⟩ := h.exists_approximating hclj hnej hq
  have hqjR : ∀ᶠ j in atTop, ‖qj j‖ < R := hqjt.norm.eventually_lt_const hqR
  have hqjb : ∀ᶠ j in atTop, ell (qj j) < b :=
    (ell.continuous.tendsto q |>.comp hqjt).eventually_lt_const hqb
  refine ⟨R, hR, ?_⟩
  filter_upwards [h.eventually_disjoint_compact hcl ⟨q, hq⟩ hSc hSd, hqjR, hqjb]
    with j hj hqRj hqbj
  intro p hp
  by_contra hn
  have hpR : R ≤ ‖p‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hn
  let f : ℝ → E := fun t => (1 - t) • qj j + t • p
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = qj j := by simp [f]
  have hf1 : f 1 = p := by simp [f]
  have hRim : R ∈ (fun t => ‖f t‖) '' Icc (0 : ℝ) 1 :=
    intermediate_value_Icc (by norm_num) hf.norm.continuousOn (by simp [hf0, hf1, hqRj.le, hpR])
  obtain ⟨t, ht, htR⟩ := hRim
  have hft : f t ∈ Cj j := hcvj j (hqj j) hp.1 (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hfb : ell (f t) ≤ b := by
    dsimp [f]
    simp only [map_add, map_smul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hqbj.le (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left hp.2 ht.1
    nlinarith
  exact Set.disjoint_left.mp hj hft ⟨by simpa [Metric.mem_sphere, dist_zero_right] using htR, hfb⟩

/- A point on the top of a limit cap is approximated from strictly below
its top by contracting toward a fixed strict point. -/
theorem LocalDistanceConverges.eventually_infDist_cap_lt_at
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (hcv : Convex ℝ C) (ell : E →L[ℝ] ℝ) {b : ℝ}
    {q : E} (hq : q ∈ C) (hqb : ell q < b)
    {x : E} (hx : x ∈ C) (hxb : ell x ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, infDist x (Cj j ∩ {y | ell y ≤ b}) < ε := by
  let t : ℝ := min (1 / 2) (ε / (4 * (1 + dist x q)))
  have hden : 0 < 4 * (1 + dist x q) := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε hden)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htmul : t * (4 * (1 + dist x q)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  let a : E := (1 - t) • x + t • q
  have haC : a ∈ C := hcv hx hq (sub_nonneg.mpr ht1) ht.le (by ring)
  have hab : ell a < b := by
    dsimp [a]
    simp only [map_add, map_smul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hxb (sub_nonneg.mpr ht1)
    have h2 := mul_lt_mul_of_pos_left hqb ht
    nlinarith
  have hxa : dist x a < ε / 2 := by
    have he : x - a = t • (x - q) := by dsimp [a]; module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← dist_eq_norm]
    nlinarith [dist_nonneg (x := x) (y := q)]
  obtain ⟨aj, haj, hat⟩ := h.exists_approximating hclj hnej haC
  have he1 : ∀ᶠ j in atTop, ell (aj j) < b :=
    (ell.continuous.tendsto a |>.comp hat).eventually_lt_const hab
  have he2 : ∀ᶠ j in atTop, dist x (aj j) < ε :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).dist hat).eventually_lt_const
      (hxa.trans (by linarith))
  filter_upwards [he1, he2] with j hj1 hj2
  exact (infDist_le_dist_of_mem (s := Cj j ∩ {y | ell y ≤ b}) ⟨haj j, hj1.le⟩).trans_lt hj2

/- Reverse Hausdorff inclusion for a compact cap. -/
theorem LocalDistanceConverges.eventually_infDist_cap_lt_uniform
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (hcv : Convex ℝ C) (ell : E →L[ℝ] ℝ) {b : ℝ}
    (hcap : IsCompact (C ∩ {x | ell x ≤ b}))
    {q : E} (hq : q ∈ C) (hqb : ell q < b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ C ∩ {y | ell y ≤ b},
      infDist x (Cj j ∩ {y | ell y ≤ b}) < ε := by
  classical
  obtain ⟨t, htC, ht⟩ := hcap.elim_nhds_subcover (fun x => Metric.ball x (ε / 2))
    (fun x _ => Metric.ball_mem_nhds x (half_pos hε))
  have he : ∀ x ∈ t, ∀ᶠ j in atTop, infDist x (Cj j ∩ {y | ell y ≤ b}) < ε / 2 :=
    fun x hx => h.eventually_infDist_cap_lt_at hclj hnej hcv ell hq hqb
      (htC x hx).1 (htC x hx).2 (half_pos hε)
  filter_upwards [(t.eventually_all).mpr he] with j hj x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  have hd : dist x y < ε / 2 := hxy
  exact (infDist_le_infDist_add_dist (x := x) (y := y)).trans_lt (by linarith [hj y hyt])

/- Full Hausdorff cap convergence, geometry.tex:104–125, with no asserted
smoothness of the limiting boundary. -/
theorem LocalDistanceConverges.tendsto_hausdorffDist_caps
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hcv : Convex ℝ C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) (ell : E →L[ℝ] ℝ) {b : ℝ}
    (hcap : IsCompact (C ∩ {x | ell x ≤ b}))
    {q : E} (hq : q ∈ C) (hqb : ell q < b) :
    Tendsto (fun j => hausdorffDist (Cj j ∩ {x | ell x ≤ b})
      (C ∩ {x | ell x ≤ b})) atTop (𝓝 0) := by
  obtain ⟨R, hR, hRj⟩ := h.eventually_bounded_caps hcl hclj hcvj hnej ell b hcap.isBounded hq hqb
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le hausdorffDist_nonneg
  · intro ε hε
    let S : Set E := Metric.closedBall 0 R ∩ {x | ell x ≤ b} ∩
      {x | ε / 2 ≤ infDist x (C ∩ {y | ell y ≤ b})}
    have hSc : IsCompact S := ((isCompact_closedBall (0 : E) R).inter_right
      (isClosed_le ell.continuous continuous_const)).inter_right
        (isClosed_le continuous_const (continuous_infDist_pt _))
    have hSd : Disjoint C S := by
      rw [Set.disjoint_left]
      intro x hx hxs
      have he : ε / 2 ≤ infDist x (C ∩ {y | ell y ≤ b}) := hxs.2
      rw [infDist_zero_of_mem (s := C ∩ {y | ell y ≤ b}) ⟨hx, hxs.1.2⟩] at he
      linarith
    have he := h.eventually_disjoint_compact hcl ⟨q, hq⟩ hSc hSd
    have hreverse := h.eventually_infDist_cap_lt_uniform hclj hnej hcv ell hcap hq hqb (half_pos hε)
    filter_upwards [hRj, he, hreverse] with j hjR hjS hjrev
    have hforward : ∀ x ∈ Cj j ∩ {y | ell y ≤ b},
        infDist x (C ∩ {y | ell y ≤ b}) < ε / 2 := by
      intro x hx
      by_contra hn
      exact Set.disjoint_left.mp hjS hx.1 ⟨⟨ball_subset_closedBall (hjR hx), hx.2⟩,
        not_lt.mp hn⟩
    exact (hausdorffDist_le_of_infDist (half_pos hε).le
      (fun x hx => (hforward x hx).le) (fun x hx => (hjrev x hx).le)).trans_lt (by linarith)

/- Compactness of the bounded-at-one-point nonnegative unit-Lipschitz
family in the compact-open topology. This is the actual Arzelà–Ascoli input
for local convex-set compactness. -/
omit [NormedSpace ℝ E] [ProperSpace E] in
theorem isCompact_nonneg_unitLipschitz (R : ℝ) :
    IsCompact {f : C(E, ℝ) | LipschitzWith 1 f ∧ f 0 ≤ R ∧ ∀ x, 0 ≤ f x} := by
  classical
  let P : Set (E → ℝ) := {f | LipschitzWith 1 f ∧ f 0 ≤ R ∧ ∀ x, 0 ≤ f x}
  have hPcl : IsClosed P := by
    have hnonneg : IsClosed {f : E → ℝ | ∀ x, 0 ≤ f x} := by
      simpa only [Set.ofPred_forall] using
        (isClosed_iInter fun x : E => isClosed_le (continuous_const : Continuous (fun _ : E → ℝ => (0 : ℝ)))
          (continuous_apply x))
    exact (isClosed_setOfPred_lipschitzWith (1 : ℝ≥0)).inter
      ((isClosed_le (continuous_apply 0) continuous_const).inter hnonneg)
  have hPc : IsCompact P := by
    apply (isCompact_univ_pi fun x : E => isCompact_Icc (a := (0 : ℝ)) (b := ‖x‖ + R)).of_isClosed_subset hPcl
    intro f hf x _
    refine ⟨hf.2.2 x, ?_⟩
    have he := hf.1.dist_le_mul x 0
    simp only [NNReal.coe_one, one_mul, dist_zero_right, Real.dist_eq] at he
    have hfup := (abs_le.mp he).2
    linarith [hf.2.1]
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · have him : ContinuousMap.toFun ''
        {f : C(E, ℝ) | LipschitzWith 1 f ∧ f 0 ≤ R ∧ ∀ x, 0 ≤ f x} = P := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hf
        exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
    rwa [him]
  · exact (LipschitzWith.uniformEquicontinuous _ 1 (fun f => f.2.1)).equicontinuous

/- Extract locally uniformly convergent distance functions. At this stage
we do not yet assert that the limit is a distance function. -/
omit [NormedSpace ℝ E] in
theorem exists_distance_function_subsequence {Cj : ℕ → Set E}
    {R : ℝ} (hbound : ∀ j, infDist (0 : E) (Cj j) ≤ R) :
    ∃ (f : C(E, ℝ)) (φ : ℕ → ℕ), StrictMono φ ∧
      LipschitzWith 1 f ∧ (∀ x, 0 ≤ f x) ∧
      TendstoLocallyUniformly (fun j x => infDist x (Cj (φ j))) f atTop := by
  let dj : ℕ → C(E, ℝ) := fun j => ⟨fun x => infDist x (Cj j), continuous_infDist_pt _⟩
  obtain ⟨f, hf, φ, hφ, hconv⟩ := (isCompact_nonneg_unitLipschitz (E := E) R).tendsto_subseq
    (x := dj) (fun j => ⟨lipschitz_infDist_pt _, hbound j, fun _ => infDist_nonneg⟩)
  exact ⟨f, φ, hφ, hf.1, hf.2.2, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv⟩

/- A pointwise limit of nonnegative unit-Lipschitz distance functions of
nonempty closed sets, on a proper space, is itself their zero-set's distance
function. Nearest points supply the nonempty zero set and attain the distance. -/
omit [NormedSpace ℝ E] in
theorem distance_function_limit_representation {Cj : ℕ → Set E} {f : E → ℝ}
    (hcl : ∀ j, IsClosed (Cj j)) (hne : ∀ j, (Cj j).Nonempty)
    (hlip : LipschitzWith 1 f) (hpos : ∀ x, 0 ≤ f x)
    (hpt : ∀ x, Tendsto (fun j => infDist x (Cj j)) atTop (𝓝 (f x))) :
    ∃ C : Set E, IsClosed C ∧ C.Nonempty ∧ ∀ x, infDist x C = f x := by
  let C : Set E := {x | f x = 0}
  have hCc : IsClosed C := isClosed_eq hlip.continuous continuous_const
  have hnear : ∀ x : E, ∃ y ∈ C, dist x y = f x := by
    intro x
    choose pj hpj heq using fun j => (hcl j).exists_infDist_eq_dist (hne j) x
    have hev : ∀ᶠ j in atTop, pj j ∈ Metric.closedBall x (f x + 1) := by
      filter_upwards [(hpt x).eventually_lt_const (lt_add_one (f x))] with j hj
      simpa only [Metric.mem_closedBall, dist_comm, ← heq] using hj.le
    obtain ⟨y, hy, φ, hφ, hφy⟩ := (isCompact_closedBall x (f x + 1)).tendsto_subseq' hev.frequently
    have hzero : f y = 0 := by
      apply le_antisymm _ (hpos y)
      have hd : Tendsto (fun j => dist y (pj (φ j))) atTop (𝓝 0) := by
        simpa only [dist_self, Function.comp_def] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).dist hφy
      exact le_of_tendsto_of_tendsto ((hpt y).comp hφ.tendsto_atTop) hd
        (Eventually.of_forall fun j => infDist_le_dist_of_mem (hpj (φ j)))
    have hd1 : Tendsto (fun j => dist x (pj (φ j))) atTop (𝓝 (dist x y)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).dist hφy
    have hd2 : Tendsto (fun j => dist x (pj (φ j))) atTop (𝓝 (f x)) := by
      simpa only [Function.comp_def, ← heq] using (hpt x).comp hφ.tendsto_atTop
    exact ⟨y, hzero, tendsto_nhds_unique hd1 hd2⟩
  have hCne : C.Nonempty := let ⟨y, hy, _⟩ := hnear 0; ⟨y, hy⟩
  refine ⟨C, hCc, hCne, fun x => ?_⟩
  obtain ⟨y, hy, heq⟩ := hnear x
  apply le_antisymm (heq ▸ infDist_le_dist_of_mem hy)
  rw [Metric.le_infDist hCne]
  intro z hz
  have he := hlip.dist_le_mul x z
  have hfz : f z = 0 := hz
  simpa only [Real.dist_eq, hfz, sub_zero, abs_of_nonneg (hpos x), NNReal.coe_one, one_mul] using he

/- Local compactness of nonempty closed convex sets meeting a fixed bounded
set, the extraction used in geometry.tex:70–101. The topology and the limit
are literal sets and Euclidean distance functions. -/
theorem exists_convex_local_limit {Cj : ℕ → Set E}
    (hcl : ∀ j, IsClosed (Cj j)) (hcv : ∀ j, Convex ℝ (Cj j))
    (hne : ∀ j, (Cj j).Nonempty) {R : ℝ}
    (hbound : ∀ j, infDist (0 : E) (Cj j) ≤ R) :
    ∃ (C : Set E) (φ : ℕ → ℕ), StrictMono φ ∧ IsClosed C ∧ C.Nonempty ∧
      Convex ℝ C ∧ LocalDistanceConverges (fun j => Cj (φ j)) C := by
  obtain ⟨f, φ, hφ, hfL, hfpos, hconv⟩ := exists_distance_function_subsequence hbound
  have hpt : ∀ x, Tendsto (fun j => infDist x (Cj (φ j))) atTop (𝓝 (f x)) := fun x =>
    ((tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) {x} isCompact_singleton).tendsto_at
      (mem_singleton x)
  obtain ⟨C, hCc, hCne, heq⟩ := distance_function_limit_representation
    (fun j => hcl (φ j)) (fun j => hne (φ j)) hfL hfpos hpt
  have hloc : LocalDistanceConverges (fun j => Cj (φ j)) C := by
    unfold LocalDistanceConverges
    simpa only [heq] using hconv
  refine ⟨C, φ, hφ, hCc, hCne, ?_, hloc⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨xj, hxj, hxt⟩ := hloc.exists_approximating (fun j => hcl (φ j)) (fun j => hne (φ j)) hx
  obtain ⟨yj, hyj, hyt⟩ := hloc.exists_approximating (fun j => hcl (φ j)) (fun j => hne (φ j)) hy
  exact hloc.mem_of_tendsto hCc hCne
    (fun j => hcv (φ j) (hxj j) (hyj j) ha hb hab)
    ((hxt.const_smul a).add (hyt.const_smul b))

end AffineBernstein
end

end OAI
