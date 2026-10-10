import Mathlib
import OAI.Geometry.HyperbolicGroups.TangentRay

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal
variable {X : Type*} [MetricSpace X]

namespace TangentCone
variable (h : CATZero X) (o : X)

def vertex : TangentCone h o := (TangentRay.vertex h o : TangentRay h o)
def log (x : X) : TangentCone h o := (TangentRay.log h o x : TangentRay h o)
def scaleN (r : ℝ≥0) : TangentCone h o → TangentCone h o :=
  Completion.map (TangentRay.scale h o r)

theorem scaleN_coe (r : ℝ≥0) (p : TangentRay h o) :
    scaleN h o r p = (TangentRay.scale h o r p : TangentRay h o) :=
  Completion.map_coe (TangentRay.scale_lipschitz h o r).uniformContinuous p

@[fun_prop] theorem continuous_scaleN (r : ℝ≥0) : Continuous (scaleN h o r) := Completion.continuous_map

theorem scaleN_zero (x : TangentCone h o) : scaleN h o 0 x = vertex h o := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_scaleN h o 0) continuous_const
  | ih p =>
    rw [scaleN_coe]
    apply dist_eq_zero.mp
    rw [vertex, Completion.dist_eq, dist_comm, TangentRay.dist_vertex]
    simp [TangentRay.scale]

theorem scaleN_one (x : TangentCone h o) : scaleN h o 1 x = x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_scaleN h o 1) continuous_id
  | ih p =>
    rw [scaleN_coe]
    congr 1
    cases p
    simp [TangentRay.scale]

theorem radial_metric (r s : ℝ≥0) (x y : TangentCone h o) :
    dist (scaleN h o r x) (scaleN h o s y) ^ 2 =
      ((r : ℝ) ^ 2 - (r : ℝ) * (s : ℝ)) * dist (vertex h o) x ^ 2 +
      ((s : ℝ) ^ 2 - (r : ℝ) * (s : ℝ)) * dist (vertex h o) y ^ 2 +
      (r : ℝ) * (s : ℝ) * dist x y ^ 2 := by
  induction x, y using Completion.induction_on₂ with
  | hp =>
    apply isClosed_eq <;> fun_prop
  | ih p q =>
    rw [scaleN_coe, scaleN_coe]
    simpa only [vertex, Completion.dist_eq] using TangentRay.radial_metric h o r s p q

/-- The required radial metric law, with no asserted CAT(0) axiom.
The CAT(0) property is a separate construction below. -/
def coneData : ConeData (TangentCone h o) where
  vertex := vertex h o
  scale r := scaleN h o r.toNNReal
  scale_zero := by simpa only [Real.toNNReal_zero] using scaleN_zero h o
  scale_one := by simpa only [Real.toNNReal_one] using scaleN_one h o
  radial_metric r s hr hs := by
    simpa only [Real.toNNReal_of_nonneg hr, Real.toNNReal_of_nonneg hs, NNReal.coe_mk]
      using radial_metric h o r.toNNReal s.toNNReal

theorem dist_log_le (x y : X) : dist (log h o x) (log h o y) ≤ dist x y := by
  rw [log, log, Completion.dist_eq]
  change CATZero.tangentDist h o x y 1 1 ≤ dist x y
  simpa only [one_mul] using CATZero.tangentDist_le h o x y (r := 1) (by norm_num)

theorem log_lipschitz : LipschitzWith 1 (log h o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul] using dist_log_le h o x y

theorem dist_vertex_log (x : X) : dist (vertex h o) (log h o x) = dist o x := by
  rw [vertex, log, Completion.dist_eq, TangentRay.dist_vertex]
  simp only [TangentRay.log, NNReal.coe_one, one_mul]

theorem normSq_log (x : X) : (coneData h o).normSq (log h o x) = dist o x ^ 2 := by
  change dist (vertex h o) (log h o x) ^ 2 = _
  rw [dist_vertex_log]

theorem pairing_log (x y : X) :
    (coneData h o).pairing (log h o x) (log h o y) = CATZero.tangentPairing h o x y := by
  unfold ConeData.pairing
  rw [normSq_log, normSq_log, log, log, Completion.dist_eq, TangentRay.dist_sq]
  dsimp only [TangentRay.log, NNReal.coe_one]
  ring

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal

/-- Quadrilateral comparison and approximate midpoints give a convergent
midpoint sequence in a complete metric space. -/
theorem midpoint_limit {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    (quad : ∀ a b c d : Y, dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2)
    (x y : Y) (u : ℕ → Y) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 (dist x y)))
    (hu : ∀ᶠ n in atTop, dist x (u n) ≤ b n / 2 ∧ dist y (u n) ≤ b n / 2) :
    ∃ m, Tendsto u atTop (𝓝 m) ∧ dist x m = dist x y / 2 ∧
      dist y m = dist x y / 2 := by
  have hc : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hev : ∀ᶠ n in atTop, b n ^ 2 < dist x y ^ 2 + ε ^ 2 :=
      (hb.pow 2).eventually (gt_mem_nhds (by nlinarith [sq_pos_of_pos hε]))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.and hev)
    refine ⟨N, ?_⟩
    intro i hi j hj
    obtain ⟨⟨hix, hiy⟩, hbi⟩ := hN i hi
    obtain ⟨⟨hjx, hjy⟩, hbj⟩ := hN j hj
    have hq := quad x (u i) y (u j)
    rw [dist_comm (u i) y, dist_comm (u j) x] at hq
    have hix' := sq_le_sq₀ (dist_nonneg (x := x) (y := u i))
      (le_trans dist_nonneg hix) |>.mpr hix
    have hiy' := sq_le_sq₀ (dist_nonneg (x := y) (y := u i))
      (le_trans dist_nonneg hiy) |>.mpr hiy
    have hjx' := sq_le_sq₀ (dist_nonneg (x := x) (y := u j))
      (le_trans dist_nonneg hjx) |>.mpr hjx
    have hjy' := sq_le_sq₀ (dist_nonneg (x := y) (y := u j))
      (le_trans dist_nonneg hjy) |>.mpr hjy
    nlinarith [dist_nonneg (x := u i) (y := u j)]
  obtain ⟨m, hm⟩ := cauchySeq_tendsto_of_complete hc
  have hx : dist x m ≤ dist x y / 2 :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hm) (hb.div_const 2)
      (hu.mono fun _ hh => hh.1)
  have hy : dist y m ≤ dist x y / 2 :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hm) (hb.div_const 2)
      (hu.mono fun _ hh => hh.2)
  have ht := dist_triangle x m y
  rw [dist_comm m y] at ht
  exact ⟨m, hm, by linarith, by linarith⟩

namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)

def atScale (k : ℝ) (p : TangentRay h o) : X :=
  CATZero.segment h o p.point (k * (p.weight : ℝ))

def rescale (k : ℝ) (x : X) : TangentCone h o :=
  (⟨Real.toNNReal k⁻¹, x⟩ : TangentRay h o)

theorem rescale_atScale {k : ℝ} (hk : 0 < k) (p : TangentRay h o)
    (hp : k * (p.weight : ℝ) ≤ 1) : rescale h o k (atScale h o k p) = p := by
  apply dist_eq_zero.mp
  rw [rescale, Completion.dist_eq, TangentRay.dist_def]
  dsimp only [atScale]
  rw [Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr hk)),
    CATZero.tangentDist_radial_left h o p.point p.point
      ⟨mul_nonneg hk.le p.weight.coe_nonneg, hp⟩ (inv_nonneg.mpr hk.le)
      p.weight.coe_nonneg]
  rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul, CATZero.tangentDist_same]
  simp

theorem dist_rescale_le {k : ℝ} (hk : 0 < k) (x y : X) :
    dist (rescale h o k x) (rescale h o k y) ≤ dist x y / k := by
  rw [rescale, rescale, Completion.dist_eq, TangentRay.dist_def]
  dsimp only
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hk.le)]
  simpa only [div_eq_mul_inv, mul_comm] using
    CATZero.tangentDist_le h o x y (inv_nonneg.mpr hk.le)

def shrink (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem shrink_pos (n : ℕ) : 0 < shrink n := by
  unfold shrink
  positivity

theorem shrink_tendsto : Tendsto shrink atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Filter.Eventually.of_forall shrink_pos⟩

theorem shrink_weight (p : TangentRay h o) :
    ∀ᶠ n in atTop, shrink n * (p.weight : ℝ) ≤ 1 := by
  have ht : Tendsto (fun n => shrink n * (p.weight : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_nhds_of_tendsto_nhdsWithin shrink_tendsto).mul_const
      (p.weight : ℝ)
  exact ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))

def approxMid (p q : TangentRay h o) (n : ℕ) : TangentCone h o :=
  rescale h o (shrink n) (CATZero.mid h (atScale h o (shrink n) p)
    (atScale h o (shrink n) q))

def approxDist (p q : TangentRay h o) (n : ℕ) : ℝ :=
  dist (atScale h o (shrink n) p) (atScale h o (shrink n) q) / shrink n

theorem approxDist_tendsto (p q : TangentRay h o) :
    Tendsto (approxDist h o p q) atTop (𝓝 (dist p q)) :=
  (CATZero.tangentDist_tendsto h o p.point q.point
    p.weight.coe_nonneg q.weight.coe_nonneg).comp shrink_tendsto

theorem approxMid_bound (p q : TangentRay h o) :
    ∀ᶠ n in atTop, dist (p : TangentCone h o) (approxMid h o p q n) ≤
        approxDist h o p q n / 2 ∧
      dist (q : TangentCone h o) (approxMid h o p q n) ≤ approxDist h o p q n / 2 := by
  filter_upwards [shrink_weight h o p, shrink_weight h o q] with n hp hq
  constructor
  · rw [← rescale_atScale h o (shrink_pos n) p hp]
    have hh := dist_rescale_le h o (shrink_pos n) (atScale h o (shrink n) p)
      (CATZero.mid h (atScale h o (shrink n) p) (atScale h o (shrink n) q))
    rw [CATZero.dist_left_mid] at hh
    exact hh.trans_eq (by unfold approxDist; ring)
  · rw [← rescale_atScale h o (shrink_pos n) q hq]
    have hh := dist_rescale_le h o (shrink_pos n) (atScale h o (shrink n) q)
      (CATZero.mid h (atScale h o (shrink n) p) (atScale h o (shrink n) q))
    rw [dist_comm (atScale h o (shrink n) q), CATZero.dist_mid_right] at hh
    exact hh.trans_eq (by unfold approxDist; ring)

theorem quadrilateral (a b c d : TangentCone h o) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  induction a using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih a =>
    induction b, c, d using Completion.induction_on₃ with
    | hp => apply isClosed_le <;> fun_prop
    | ih b c d =>
      simpa only [Completion.dist_eq] using TangentRay.quadrilateral h o a b c d

theorem represented_midpoint_limit (p q : TangentRay h o) :
    ∃ m : TangentCone h o, Tendsto (approxMid h o p q) atTop (𝓝 m) ∧
      dist (p : TangentCone h o) m = dist p q / 2 ∧
      dist (q : TangentCone h o) m = dist p q / 2 := by
  simpa only [Completion.dist_eq] using midpoint_limit (quadrilateral h o)
    (p : TangentCone h o) (q : TangentCone h o) (approxMid h o p q) (approxDist h o p q)
    (by simpa only [Completion.dist_eq] using approxDist_tendsto h o p q)
    (approxMid_bound h o p q)


theorem approxMid_cn (p q z : TangentRay h o) :
    ∀ᶠ n in atTop, dist (z : TangentCone h o) (approxMid h o p q n) ^ 2 ≤
      (approxDist h o z p n ^ 2 + approxDist h o z q n ^ 2) / 2 -
        approxDist h o p q n ^ 2 / 4 := by
  filter_upwards [shrink_weight h o z] with n hz
  rw [← rescale_atScale h o (shrink_pos n) z hz]
  apply (sq_le_sq₀ dist_nonneg (div_nonneg dist_nonneg (shrink_pos n).le) |>.mpr
    (dist_rescale_le h o (shrink_pos n) (atScale h o (shrink n) z)
      (CATZero.mid h (atScale h o (shrink n) p) (atScale h o (shrink n) q)))).trans
  have hc := div_le_div_of_nonneg_right
    (CATZero.mid_cn h (atScale h o (shrink n) p) (atScale h o (shrink n) q)
      (atScale h o (shrink n) z)) (sq_nonneg (shrink n))
  convert hc using 1
  · simp only [div_pow]
  · simp only [approxDist, div_pow]
    ring

theorem exists_represented_mid (p q : TangentRay h o) :
    ∃ m : TangentCone h o,
      dist (p : TangentCone h o) m = dist p q / 2 ∧
      dist (q : TangentCone h o) m = dist p q / 2 ∧
      ∀ z : TangentCone h o, dist z m ^ 2 ≤
        (dist z p ^ 2 + dist z q ^ 2) / 2 - dist p q ^ 2 / 4 := by
  obtain ⟨m, hm, hmp, hmq⟩ := represented_midpoint_limit h o p q
  refine ⟨m, hmp, hmq, ?_⟩
  intro z
  induction z using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih z =>
    have ht := (((approxDist_tendsto h o z p).pow 2).add
      ((approxDist_tendsto h o z q).pow 2)).div_const 2
    have ht' := ((approxDist_tendsto h o p q).pow 2).div_const 4
    have hl := le_of_tendsto_of_tendsto ((tendsto_const_nhds.dist hm).pow 2)
      (ht.sub ht') (approxMid_cn h o p q z)
    simpa only [Completion.dist_eq] using hl

def representedMid (p q : TangentRay h o) : TangentCone h o :=
  (exists_represented_mid h o p q).choose

theorem representedMid_left (p q : TangentRay h o) :
    dist (p : TangentCone h o) (representedMid h o p q) = dist p q / 2 :=
  (exists_represented_mid h o p q).choose_spec.1

theorem representedMid_right (p q : TangentRay h o) :
    dist (q : TangentCone h o) (representedMid h o p q) = dist p q / 2 :=
  (exists_represented_mid h o p q).choose_spec.2.1

theorem representedMid_cn (p q : TangentRay h o) (z : TangentCone h o) :
    dist z (representedMid h o p q) ^ 2 ≤ (dist z p ^ 2 + dist z q ^ 2) / 2 -
      dist p q ^ 2 / 4 := (exists_represented_mid h o p q).choose_spec.2.2 z

theorem representedMid_swap (p q : TangentRay h o) :
    representedMid h o p q = representedMid h o q p := by
  have hc := representedMid_cn h o q p (representedMid h o p q)
  rw [dist_comm (representedMid h o p q) q, representedMid_right,
    dist_comm (representedMid h o p q) p, representedMid_left, dist_comm q p] at hc
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := representedMid h o p q) (y := representedMid h o q p)]

theorem representedMid_contraction (p q r : TangentRay h o) :
    dist (representedMid h o p q) (representedMid h o p r) ≤ dist q r / 2 := by
  have hc := representedMid_cn h o p r (representedMid h o p q)
  have hc' := representedMid_cn h o p q (r : TangentCone h o)
  rw [dist_comm (representedMid h o p q) p, representedMid_left,
    dist_comm (representedMid h o p q) r] at hc
  simp only [Completion.dist_eq] at hc'
  rw [dist_comm r p, dist_comm r q] at hc'
  have hn := dist_nonneg (x := q) (y := r)
  nlinarith [dist_nonneg (x := representedMid h o p q) (y := representedMid h o p r)]

theorem representedMid_lipschitz :
    LipschitzWith 1 (fun p : TangentRay h o × TangentRay h o => representedMid h o p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h1 := representedMid_contraction h o p.2 p.1 q.1
  rw [representedMid_swap h o p.2 p.1, representedMid_swap h o p.2 q.1] at h1
  have h2 := representedMid_contraction h o q.1 p.2 q.2
  have ht := dist_triangle (representedMid h o p.1 p.2) (representedMid h o q.1 p.2)
    (representedMid h o q.1 q.2)
  rw [NNReal.coe_one, one_mul, Prod.dist_eq]
  have ha := le_max_left (dist p.1 q.1) (dist p.2 q.2)
  have hb := le_max_right (dist p.1 q.1) (dist p.2 q.2)
  linarith

def coneMid : TangentCone h o → TangentCone h o → TangentCone h o :=
  Completion.extension₂ (representedMid h o)

@[fun_prop] theorem continuous_coneMid :
    Continuous (fun p : TangentCone h o × TangentCone h o => coneMid h o p.1 p.2) :=
  (Completion.uniformContinuous_extension₂ (representedMid h o)).uniformContinuous.continuous

theorem coneMid_coe (p q : TangentRay h o) : coneMid h o p q = representedMid h o p q :=
  Completion.extension₂_coe_coe (f := representedMid h o)
    (representedMid_lipschitz h o).uniformContinuous p q

theorem coneMid_left (x y : TangentCone h o) :
    dist x (coneMid h o x y) = dist x y / 2 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih p q => rw [coneMid_coe, representedMid_left, Completion.dist_eq]

theorem coneMid_right (x y : TangentCone h o) :
    dist y (coneMid h o x y) = dist x y / 2 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih p q => rw [coneMid_coe, representedMid_right, Completion.dist_eq]

theorem coneMid_cn (x y z : TangentCone h o) :
    dist z (coneMid h o x y) ^ 2 ≤ (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_le <;> fun_prop
  | ih p q =>
    rw [coneMid_coe, Completion.dist_eq]
    exact representedMid_cn h o p q z

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology

/-- The complete-space direct method for a squared-distance strongly convex
functional. No local compactness is used. -/
theorem strongly_convex_minimum {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [Nonempty Y]
    (M : Y → Y → Y) (f : Y → ℝ) (hf : Continuous f)
    (hb : BddBelow (Set.range f))
    (hc : ∀ x y, f (M x y) ≤ (f x + f y) / 2 - dist x y ^ 2 / 4) :
    ∃ p, ∀ z, f p ≤ f z := by
  obtain ⟨v, _, hv, hvr⟩ := exists_seq_tendsto_sInf (Set.range_nonempty f) hb
  choose u hu using hvr
  have hlow (z : Y) : sInf (Set.range f) ≤ f z := csInf_le hb (Set.mem_range_self z)
  have hC : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have he := hv.eventually (gt_mem_nhds
      (show sInf (Set.range f) < sInf (Set.range f) + ε ^ 2 / 4 by
        nlinarith [sq_pos_of_pos hε]))
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    refine ⟨N, ?_⟩
    intro i hi j hj
    have hi' := hN i hi
    have hj' := hN j hj
    have hl := hlow (M (u i) (u j))
    have hc' := hc (u i) (u j)
    rw [hu i, hu j] at hc'
    nlinarith [dist_nonneg (x := u i) (y := u j)]
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hC
  have he : f p = sInf (Set.range f) := tendsto_nhds_unique
    ((hf.tendsto p).comp hp) (hv.congr' (Filter.Eventually.of_forall fun n => (hu n).symm))
  exact ⟨p, fun z => he ▸ hlow z⟩

/-- Iterating midpoints toward a minimizer sharpens the one-step midpoint
inequality to the exact variance inequality. -/
theorem strongly_convex_variance {Y : Type*} [MetricSpace Y]
    (M : Y → Y → Y) (hM : ∀ x y, dist x (M x y) = dist x y / 2)
    (f : Y → ℝ)
    (hc : ∀ x y, f (M x y) ≤ (f x + f y) / 2 - dist x y ^ 2 / 4)
    (p : Y) (hp : ∀ z, f p ≤ f z) (z : Y) : f p + dist p z ^ 2 ≤ f z := by
  let u : ℕ → Y := fun n => (M p)^[n] z
  have hd (n : ℕ) : dist p (u n) = (1 / 2 : ℝ) ^ n * dist p z := by
    induction n with
    | zero => simp [u]
    | succ n hn =>
      change dist p ((M p)^[n + 1] z) = _
      rw [Function.iterate_succ_apply', hM]
      change dist p (u n) / 2 = _
      rw [hn, pow_succ]
      ring
  have hf (n : ℕ) : f (u n) ≤ (1 - (1 / 2 : ℝ) ^ n) * f p +
      (1 / 2 : ℝ) ^ n * f z -
        (1 / 2 : ℝ) ^ n * (1 - (1 / 2 : ℝ) ^ n) * dist p z ^ 2 := by
    induction n with
    | zero => simp [u]
    | succ n hn =>
      have hh := hc p (u n)
      rw [hd n] at hh
      change f ((M p)^[n + 1] z) ≤ _
      rw [Function.iterate_succ_apply']
      change f (M p (u n)) ≤ _
      rw [pow_succ]
      nlinarith
  have hh (n : ℕ) : (1 - (1 / 2 : ℝ) ^ n) * dist p z ^ 2 ≤ f z - f p := by
    apply (mul_le_mul_iff_of_pos_left (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)).mp
    nlinarith [hp (u n), hf n]
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (1 - (1 / 2 : ℝ) ^ n) * dist p z ^ 2)
      atTop (𝓝 (dist p z ^ 2)) := by
    simpa only [sub_zero, one_mul] using ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).mul_const (dist p z ^ 2)
  have hh' := le_of_tendsto hlim (Filter.Eventually.of_forall hh)
  linarith

/-- Full CAT(0) comparison from complete CN midpoints. The division point
is constructed by minimizing a weighted squared-distance functional. -/
theorem catZero_of_midpoints {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    (M : Y → Y → Y)
    (hM : ∀ x y, dist x (M x y) = dist x y / 2)
    (hCN : ∀ x y z, dist z (M x y) ^ 2 ≤
      (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4) : CATZero Y := by
  intro x y
  let : Nonempty Y := ⟨x⟩
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ∃ p : Y, dist x p = t * dist x y ∧ dist p y = (1 - t) * dist x y ∧
        ∀ z, dist z p ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
          t * (1 - t) * dist x y ^ 2 := by
    let f : Y → ℝ := fun z => (1 - t) * dist z x ^ 2 + t * dist z y ^ 2
    have hf : Continuous f := by dsimp only [f]; fun_prop
    have hb : BddBelow (Set.range f) := ⟨0, by
      rintro _ ⟨z, rfl⟩
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg _))
        (mul_nonneg ht.1 (sq_nonneg _))⟩
    have hc (a b : Y) : f (M a b) ≤ (f a + f b) / 2 - dist a b ^ 2 / 4 := by
      have h1 := mul_le_mul_of_nonneg_left (hCN a b x) (sub_nonneg.mpr ht.2)
      have h2 := mul_le_mul_of_nonneg_left (hCN a b y) ht.1
      simp only [dist_comm x, dist_comm y] at h1 h2
      dsimp only [f]
      nlinarith
    obtain ⟨p, hp⟩ := strongly_convex_minimum M f hf hb hc
    have hv := strongly_convex_variance M hM f hc p hp
    have hx := hv x
    have hy := hv y
    have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2)
    have hy' := mul_le_mul_of_nonneg_left hy ht.1
    simp only [f, dist_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
      zero_add, add_zero, dist_comm y x] at hx hy hx' hy'
    have hupper : f p ≤ t * (1 - t) * dist x y ^ 2 := by
      dsimp only [f]
      nlinarith
    have htri := dist_triangle x p y
    rw [dist_comm x p] at htri
    have hs : dist x y ^ 2 ≤ (dist p x + dist p y) ^ 2 :=
      (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr htri
    have hs' := mul_le_mul_of_nonneg_left hs (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    have hlower : t * (1 - t) * dist x y ^ 2 ≤ f p := by
      dsimp only [f]
      nlinarith [sq_nonneg ((1 - t) * dist p x - t * dist p y)]
    have hfx : f p = t * (1 - t) * dist x y ^ 2 := le_antisymm hupper hlower
    have hpx : dist p x ≤ t * dist x y := by
      have hl := hlower
      dsimp only [f] at hl
      nlinarith [dist_nonneg (x := p) (y := x),
        mul_nonneg ht.1 (dist_nonneg (x := x) (y := y))]
    have hpy : dist p y ≤ (1 - t) * dist x y := by
      have hl := hlower
      dsimp only [f] at hl
      nlinarith [dist_nonneg (x := p) (y := y),
        mul_nonneg (sub_nonneg.mpr ht.2) (dist_nonneg (x := x) (y := y))]
    refine ⟨p, ?_, by linarith, ?_⟩
    · rw [dist_comm]
      linarith
    · intro z
      have hz := hv z
      rw [hfx, dist_comm p z] at hz
      exact (le_sub_iff_add_le.mpr (by simpa only [f, add_comm] using hz))
  choose point hleft hright hcomp using hpoint
  let γ : ℝ → Y := fun t => if ht : t ∈ Set.Icc (0 : ℝ) 1 then point t ht else x
  have hγ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : γ t = point t ht := dite_eq_left ht
  have hL (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : dist x (γ t) = t * dist x y := by
    rw [hγ t ht]; exact hleft t ht
  have hR (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : dist (γ t) y = (1 - t) * dist x y := by
    rw [hγ t ht]; exact hright t ht
  have hC (z : Y) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      dist z (γ t) ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
        t * (1 - t) * dist x y ^ 2 := by rw [hγ t ht]; exact hcomp t ht z
  refine ⟨γ, ⟨?_, ?_, ?_⟩, hC⟩
  · apply (dist_eq_zero.mp ?_).symm
    simpa only [zero_mul] using hL 0 (by norm_num)
  · apply dist_eq_zero.mp
    simpa only [sub_self, zero_mul] using hR 1 (by norm_num)
  · intro s hs t ht
    have hCN' := hC (γ s) t ht
    rw [dist_comm (γ s) x, hL s hs, hR s hs] at hCN'
    have ha : dist (γ s) (γ t) ≤ |s - t| * dist x y := by
      nlinarith [sq_abs (s - t), mul_nonneg (abs_nonneg (s - t)) (dist_nonneg (x := x) (y := y)),
        dist_nonneg (x := γ s) (y := γ t)]
    have hb1 := dist_triangle x (γ t) (γ s)
    have hb2 := dist_triangle x (γ s) (γ t)
    rw [hL s hs, hL t ht, dist_comm (γ t) (γ s)] at hb1
    rw [hL s hs, hL t ht] at hb2
    rcases le_total t s with hts | hst
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)] at ha ⊢
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hst)] at ha ⊢
      linarith


end HyperbolicObstruction
end
end
end
end
end
end
end
end
end

end OAI
