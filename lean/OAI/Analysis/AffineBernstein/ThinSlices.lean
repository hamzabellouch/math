import Mathlib
import OAI.Analysis.AffineBernstein.InteriorLimits
import OAI.Analysis.AffineBernstein.AffineFamily

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise
variable {k d : ℕ}

/- Thin slices and rescalings before reordering the k+1 base coordinates. -/
def thinSlice (C : Set (Space k × (ℝ × Space d))) (ε : ℝ) : Set (Space d) :=
  {z | (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), (ε, z)) ∈ C}

def thinRescaling (C : Set (Space k × (ℝ × Space d))) (ε : ℝ)
    (A : Space d ≃L[ℝ] Space d) : Set (Space k × (ℝ × Space d)) :=
  {p | (p.1, (ε * p.2.1, A.symm p.2.2)) ∈ C}

/- Supports and the original orthant after a support-coordinate split. -/
structure IsSupportedSplitModel (C : Set (Space k × (ℝ × Space d))) : Prop where
  closed : IsClosed C
  convex : Convex ℝ C
  orthant : ∀ s : Space k, (∀ i, 0 ≤ s i) → (s, (0, 0)) ∈ C
  base_support : ∀ p ∈ C, ∀ i, 0 ≤ p.1 i
  new_support : ∀ p ∈ C, 0 ≤ p.2.1
  compact_cap : ∀ T : ℝ, 0 ≤ T → IsCompact (C ∩ {p | ∑ i, p.1 i ≤ T})
  interior_one : (1, (0 : Space d)) ∈ interior
    {y | (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), y) ∈ C}

namespace IsSupportedSplitModel
variable {C : Set (Space k × (ℝ × Space d))} (h : IsSupportedSplitModel C)
include h

theorem zero_mem : (0 : Space k × (ℝ × Space d)) ∈ C :=
  h.orthant 0 (by simp)

theorem one_mem : (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), (1, 0)) ∈ C :=
  (interior_subset (s := {y | (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), y) ∈ C})) h.interior_one

theorem base_mono {s t : Space k} {y : ℝ × Space d}
    (hst : ∀ i, s i ≤ t i) (hy : (s, y) ∈ C) : (t, y) ∈ C := by
  have hh := closed_convex_add_of_ray h.closed h.convex hy (v := (t - s, 0))
    (fun a ha => by
      simpa only [Prod.smul_mk, smul_zero, Prod.zero_eq_mk] using h.orthant (a • (t - s))
        (by intro i; exact mul_nonneg ha (sub_nonneg.mpr (hst i))))
  simpa using hh

/- Every slice at a sufficiently low positive support level contains a real
ball about zero, obtained by contraction of the interior ball at (1,0). -/
theorem slice_interior_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (0 : Space d) ∈ interior (thinSlice C ε) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (1, (0 : Space d)) h.interior_one
  have hb : ball (0 : Space d) (ε * r) ⊆ thinSlice C ε := by
    intro z hz
    have hz' : ‖z‖ < ε * r := by simpa [mem_ball, dist_zero_right] using hz
    have hy : ((1 : ℝ), ε⁻¹ • z) ∈ ball ((1 : ℝ), (0 : Space d)) r := by
      simp only [mem_ball, Prod.dist_eq, dist_self, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), max_lt_iff]
      exact ⟨hr, (inv_mul_lt_iff₀ hε).mpr hz'⟩
    have hm : (e, (1, ε⁻¹ • z)) ∈ C :=
      (interior_subset (s := {y | (e, y) ∈ C})) (hball hy)
    have hc := h.convex.smul_mem_of_zero_mem h.zero_mem hm ⟨hε.le, hε1⟩
    have hc' : (ε • e, (ε, z)) ∈ C := by
      simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_smul, mul_inv_cancel₀ hε.ne', one_smul] using hc
    exact h.base_mono (by intro i; simpa [e] using hε1) hc'
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (ball_mem_nhds _ (mul_pos hε hr)) hb)

theorem slice_closed (ε : ℝ) : IsClosed (thinSlice C ε) :=
  h.closed.preimage (by fun_prop)

theorem slice_convex (ε : ℝ) : Convex ℝ (thinSlice C ε) := by
  intro x hx y hy a b ha hb hab
  have hh := h.convex hx hy ha hb hab
  simpa [thinSlice, ← add_smul, ← add_mul, hab] using hh

theorem slice_compact (ε : ℝ) : IsCompact (thinSlice C ε) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨h.slice_closed ε, ?_⟩
  have hc := (h.compact_cap k (by positivity)).image (continuous_snd.comp continuous_snd)
  apply hc.isBounded.subset
  intro z hz
  exact ⟨(WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), (ε, z)), ⟨hz, by simp⟩, rfl⟩

theorem rescaling_closed (ε : ℝ) (A : Space d ≃L[ℝ] Space d) :
    IsClosed (thinRescaling C ε A) := h.closed.preimage (by fun_prop)

theorem rescaling_convex (ε : ℝ) (A : Space d ≃L[ℝ] Space d) :
    Convex ℝ (thinRescaling C ε A) := by
  intro x hx y hy a b ha hb hab
  have hh := h.convex hx hy ha hb hab
  change (a • x.1 + b • y.1, (ε * (a * x.2.1 + b * y.2.1),
    A.symm (a • x.2.2 + b • y.2.2))) ∈ C
  simpa only [Prod.smul_mk, Prod.mk_add_mk, map_add, map_smul,
    smul_eq_mul, mul_add, mul_left_comm ε] using hh

omit h in
theorem rescaling_one_slice (_h : IsSupportedSplitModel C)
    (ε : ℝ) (A : Space d ≃L[ℝ] Space d) :
    {z | (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), (1, z)) ∈ thinRescaling C ε A} =
      A '' thinSlice C ε := by
  ext z
  simp only [thinRescaling, thinSlice, mem_ofPred_eq, mul_one, Set.mem_image]
  constructor
  · intro hz
    exact ⟨A.symm z, hz, A.apply_symm_apply z⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/- The uniform cap bound has constant 2*T*R for an arbitrary slice outer
radius R (including d=0). -/
theorem rescaling_cap_bound {ε T R : ℝ} (hε : 0 < ε) (hε2 : 2 * ε ≤ 1)
    (A : Space d ≃L[ℝ] Space d) (hT : 1 ≤ T)
    (hR : A '' thinSlice C ε ⊆ closedBall 0 R)
    {s : Space k} {r : ℝ} {z : Space d}
    (hp : (s, (r, z)) ∈ thinRescaling C ε A)
    (hs : ∀ i, s i ≤ T) (hr : r ≤ T) : ‖z‖ ≤ 2 * T * R := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  have hTp : 0 < T := by linarith
  have hr0 : 0 ≤ r := (mul_nonneg_iff_of_pos_left hε).mp (h.new_support _ hp)
  have hm : (T • e, (ε * r, A.symm z)) ∈ C :=
    h.base_mono (by intro i; simpa [e] using hs i) hp
  have hc := h.convex.smul_mem_of_zero_mem h.zero_mem hm
    ⟨inv_nonneg.mpr hTp.le, inv_le_one_of_one_le₀ hT⟩
  have hq : (e, (ε * (r / T), A.symm (T⁻¹ • z))) ∈ C := by
    simpa only [Prod.smul_mk, smul_smul, inv_mul_cancel₀ hTp.ne', one_smul,
      map_smul, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hc
  have hp2 := h.convex.smul_mem_of_zero_mem h.zero_mem h.one_mem
    (show 2 * ε ∈ Icc (0 : ℝ) 1 from ⟨by positivity, hε2⟩)
  have hp2' : (e, (2 * ε, (0 : Space d))) ∈ C := by
    apply h.base_mono (s := (2 * ε) • e) (by intro i; simpa [e] using hε2)
    simpa [Prod.smul_mk, e] using hp2
  let q := r / T
  have hq0 : 0 ≤ q := div_nonneg hr0 hTp.le
  have hq1 : q ≤ 1 := (div_le_one hTp).mpr hr
  let a := (2 - q)⁻¹
  have hd : 0 < 2 - q := by linarith
  have ha : 0 < a := inv_pos.mpr hd
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have ha2 : (1 : ℝ) / 2 ≤ a := by
    simpa [a, one_div] using one_div_le_one_div_of_le hd (by linarith : 2 - q ≤ 2)
  have hcomb := h.convex hq hp2' ha.le (sub_nonneg.mpr ha1) (by ring : a + (1-a) = 1)
  have hrr : a * (ε * q) + (1-a) * (2*ε) = ε := by
    dsimp [a]
    field_simp
    ring
  dsimp [q] at hrr
  have hmem : a • (T⁻¹ • z) ∈ A '' thinSlice C ε := by
    rw [← h.rescaling_one_slice ε A]
    change (e, (ε * 1, A.symm (a • (T⁻¹ • z)))) ∈ C
    rw [mul_one]
    have hb : a • e + (1 - a) • e = e := by rw [← add_smul]; simp
    simpa only [Prod.smul_mk, Prod.mk_add_mk, hb, smul_eq_mul, hrr,
      map_smul, smul_zero, add_zero] using hcomb
  have hn : ‖a • (T⁻¹ • z)‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hR hmem
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ha, abs_of_pos (inv_pos.mpr hTp)] at hn
  have hmult : a * ‖z‖ ≤ T * R := by
    have hh := mul_le_mul_of_nonneg_left hn hTp.le
    simpa [mul_assoc, mul_left_comm, mul_comm, hTp.ne'] using hh
  nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (norm_nonneg z)]

end IsSupportedSplitModel

/- Eventual membership of a fixed point is sufficient for passage to the
local limit, including initial rescalings on which it is not yet present. -/
theorem LocalDistanceConverges.mem_of_eventually_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hc : IsClosed C) (hne : C.Nonempty) {x : E}
    (hx : ∀ᶠ j in atTop, x ∈ Cj j) : x ∈ C := by
  apply (hc.mem_iff_infDist_zero hne).mpr
  have he : (fun j => infDist x (Cj j)) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [hx] with j hj
    exact infDist_zero_of_mem hj
  exact tendsto_nhds_unique (h.pointwise x) (tendsto_const_nhds.congr' he.symm)

/- All the geometric properties of the (k+1)-direction model supplied by the
thin-slice limit. The new base is still written (s,r), before reindexing it as
R^(k+1). This theorem includes the zero-dimensional transverse endpoint. -/
theorem LocalDistanceConverges.thin_limit
    {C C₀ : Set (Space k × (ℝ × Space d))} (hC : IsSupportedSplitModel C)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε2 : ∀ j, 2 * ε j ≤ 1)
    (hεt : Tendsto ε atTop (𝓝 0))
    (A : ℕ → (Space d ≃L[ℝ] Space d))
    (h : LocalDistanceConverges (fun j => thinRescaling C (ε j) (A j)) C₀)
    (hclosed : IsClosed C₀) (hconvex : Convex ℝ C₀) (hne : C₀.Nonempty)
    {cj : ℕ → Space d} {c : Space d} (hc : Tendsto cj atTop (𝓝 c)) {R : ℝ}
    (hinner : ∀ j, closedBall (cj j) 1 ⊆ A j '' thinSlice C (ε j))
    (houter : ∀ j, A j '' thinSlice C (ε j) ⊆ closedBall 0 R) :
    (∀ s : Space k, (∀ i, 0 ≤ s i) → ∀ r : ℝ, 0 ≤ r → (s, (r, 0)) ∈ C₀) ∧
    (∀ p ∈ C₀, (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2.1) ∧
    (interior C₀).Nonempty ∧
    (∀ T : ℝ, 0 ≤ T → IsCompact (C₀ ∩ {p | (∑ i, p.1 i) + p.2.1 ≤ T})) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  have hz : ∀ j, (0 : Space k × (ℝ × Space d)) ∈ thinRescaling C (ε j) (A j) := by
    intro j
    simpa [thinRescaling, Prod.zero_eq_mk] using hC.zero_mem
  have hclj : ∀ j, IsClosed (thinRescaling C (ε j) (A j)) :=
    fun j => hC.rescaling_closed _ _
  have hnej : ∀ j, (thinRescaling C (ε j) (A j)).Nonempty := fun j => ⟨0, hz j⟩
  have hposorth : ∀ s : Space k, (∀ i, 0 < s i) → ∀ r : ℝ, 0 ≤ r → (s, (r, 0)) ∈ C₀ := by
    intro s hs r hr
    apply h.mem_of_eventually_mem hclosed hne
    have ht : Tendsto (fun j => ε j * r) atTop (𝓝 0) := by simpa using hεt.mul_const r
    have hsmall : ∀ i : Fin k, ∀ᶠ j in atTop, ε j * r ≤ s i :=
      fun i => ht.eventually_le_const (hs i)
    filter_upwards [Filter.eventually_all.mpr hsmall, ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with j hj hj1
    have hp := hC.convex.smul_mem_of_zero_mem hC.zero_mem hC.one_mem
      (show ε j * r ∈ Icc (0 : ℝ) 1 from ⟨mul_nonneg (hε j).le hr, hj1⟩)
    have hp' : ((ε j * r) • e, (ε j * r, (0 : Space d))) ∈ C := by
      simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using hp
    simpa [thinRescaling] using hC.base_mono (by intro i; simpa [e] using hj i) hp'
  have horth : ∀ s : Space k, (∀ i, 0 ≤ s i) → ∀ r : ℝ, 0 ≤ r → (s, (r, 0)) ∈ C₀ := by
    intro s hs r hr
    have hm : ∀ t : ℝ, 0 < t → (s + t • e, (r, (0 : Space d))) ∈ C₀ := by
      intro t ht
      apply hposorth _ _ r hr
      intro i
      simpa [e] using (add_pos_of_nonneg_of_pos (hs i) ht)
    have ht : Tendsto (fun t : ℝ => (s + t • e, (r, (0 : Space d)))) (𝓝[>] 0) (𝓝 (s, (r, 0))) := by
      have hcont : Continuous (fun t : ℝ => (s + t • e, (r, (0 : Space d)))) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply hclosed.mem_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hm t ht
  have hsupp : ∀ p ∈ C₀, (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2.1 := by
    intro p hp
    obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating hclj hnej hp
    constructor
    · intro i
      have ht : Tendsto (fun j => (pj j).1 i) atTop (𝓝 (p.1 i)) :=
        (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst).tendsto p).comp hpt
      exact ge_of_tendsto ht (Eventually.of_forall fun j => hC.base_support _ (hpj j) i)
    · have ht : Tendsto (fun j => (pj j).2.1) atTop (𝓝 (p.2.1)) :=
        (((continuous_fst.comp continuous_snd).tendsto p).comp hpt)
      apply ge_of_tendsto ht
      exact Eventually.of_forall fun j =>
        (mul_nonneg_iff_of_pos_left (hε j)).mp (hC.new_support _ (hpj j))
  refine ⟨horth, hsupp, ?_, ?_⟩
  · have hfiber : ∀ z ∈ closedBall c 1, (e, (1, z)) ∈ C₀ := by
      intro z hz'
      have hm : ∀ j, (e, (1, cj j + (z-c))) ∈ thinRescaling C (ε j) (A j) := by
        intro j
        have hh : cj j + (z-c) ∈ A j '' thinSlice C (ε j) := hinner j (by
          simpa [mem_closedBall, dist_eq_norm] using hz')
        rw [← hC.rescaling_one_slice] at hh
        exact hh
      apply h.mem_of_tendsto hclosed hne hm
      have ht := hc.add_const (z-c)
      simpa using tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds ht)
    have hball : ball (2 • e, ((2 : ℝ), c)) (1 / 2 : ℝ) ⊆ C₀ := by
      intro q hq
      have hd : dist q.1 (2 • e) < (1 / 2 : ℝ) ∧
          dist q.2.1 2 < (1 / 2 : ℝ) ∧ dist q.2.2 c < (1 / 2 : ℝ) := by
        simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
      have hbase : ∀ i, e i ≤ q.1 i := by
        intro i
        have hn := PiLp.norm_apply_le (q.1 - 2 • e) i
        have hi : |q.1 i - 2| < (1 / 2 : ℝ) := by
          have hn' : |q.1 i - 2| ≤ ‖q.1 - 2 • e‖ := by simpa [e] using hn
          exact hn'.trans_lt (by simpa [dist_eq_norm] using hd.1)
        simpa [e] using (by linarith [(abs_lt.mp hi).1] : (1 : ℝ) ≤ q.1 i)
      have hr : 1 ≤ q.2.1 := by
        have ht : |q.2.1 - 2| < (1 / 2 : ℝ) := by simpa [Real.dist_eq] using hd.2.1
        linarith [(abs_lt.mp ht).1]
      have hm := hfiber q.2.2 (hd.2.2.le.trans (by norm_num))
      have hh := closed_convex_add_of_ray hclosed hconvex hm
        (v := (q.1 - e, (q.2.1 - 1, (0 : Space d)))) (by
          intro t ht
          simpa only [Prod.smul_mk, smul_eq_mul, smul_zero] using
            horth (t • (q.1 - e)) (fun i => mul_nonneg ht (sub_nonneg.mpr (hbase i)))
              (t * (q.2.1 - 1)) (mul_nonneg ht (sub_nonneg.mpr hr)))
      simpa using hh
    exact ⟨(2 • e, (2, c)), mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1/2)) hball)⟩
  · intro T hT
    let B : Set (Space k) := (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm ''
      Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => T)
    have hB : IsCompact B := isCompact_Icc.image (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm.continuous
    have hcapclosed : IsClosed (C₀ ∩ {p | (∑ i, p.1 i) + p.2.1 ≤ T}) :=
      hclosed.inter (isClosed_le (by fun_prop) continuous_const)
    apply (hB.prod (isCompact_Icc.prod (isCompact_closedBall (0 : Space d) (2 * (T+1) * R)))).of_isClosed_subset hcapclosed
    rintro p ⟨hp, hpT⟩
    change (∑ i, p.1 i) + p.2.1 ≤ T at hpT
    have hsT : ∀ i, p.1 i ≤ T := by
      intro i
      have hi := Finset.single_le_sum (fun a _ => (hsupp p hp).1 a) (Finset.mem_univ i)
      linarith [(hsupp p hp).2]
    have hrT : p.2.1 ≤ T := by linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => (hsupp p hp).1 i)]
    refine ⟨⟨fun i => p.1 i, ⟨(hsupp p hp).1, hsT⟩, rfl⟩, ⟨(hsupp p hp).2, hrT⟩, ?_⟩
    obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating hclj hnej hp
    have hcoord : ∀ i : Fin k, ∀ᶠ j in atTop, (pj j).1 i ≤ T+1 := by
      intro i
      have ht : Tendsto (fun j => (pj j).1 i) atTop (𝓝 (p.1 i)) :=
        (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst).tendsto p).comp hpt
      exact ht.eventually_le_const (by linarith [hsT i])
    have hrcoord : ∀ᶠ j in atTop, (pj j).2.1 ≤ T+1 :=
      (((continuous_fst.comp continuous_snd).tendsto p).comp hpt).eventually_le_const (by change p.2.1 < T+1; linarith)
    have hb : ∀ᶠ j in atTop, ‖(pj j).2.2‖ ≤ 2 * (T+1) * R := by
      filter_upwards [Filter.eventually_all.mpr hcoord, hrcoord] with j hj hjr
      exact hC.rescaling_cap_bound (hε j) (hε2 j) (A j) (by linarith) (houter j) (hpj j) hj hjr
    simpa only [mem_closedBall, dist_zero_right, Function.comp_apply] using
      le_of_tendsto (((continuous_snd.comp continuous_snd).tendsto p).comp hpt).norm hb

end AffineBernstein
end

end OAI
