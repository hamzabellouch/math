import Mathlib
import OAI.Analysis.BiholderTransport.Model

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

variable {M : Type*} [MetricSpace M]

def cTransform (v : M → ℝ) (x : M) : ℝ :=
  sSup (Set.range (fun y => -cost x y - v y))

def IsCostDualPair (u v : M → ℝ) : Prop :=
  u = cTransform v ∧ v = cTransform u

def contactGap (u v : M → ℝ) (x y : M) : ℝ :=
  u x + cost x y + v y

def gapSection (u v : M → ℝ) (x : M) (r : ℝ) : Set M :=
  {y | contactGap u v x y ≤ r}

lemma continuous_cost_left (y : M) : Continuous (fun x => cost x y) := by
  exact ((continuous_id.dist continuous_const).pow 2).div_const 2

lemma continuous_cost_right (x : M) : Continuous (cost x) := by
  exact ((continuous_const.dist continuous_id).pow 2).div_const 2

lemma cost_symm (x y : M) : cost x y = cost y x := by
  simp only [cost, dist_comm]

lemma cost_nonneg (x y : M) : 0 ≤ cost x y := by
  exact div_nonneg (sq_nonneg _) (by norm_num)

lemma cost_lipschitz_of_distance_bound {D : ℝ}
    (hD : ∀ x y : M, dist x y ≤ D) (x x' y : M) :
    |cost x y - cost x' y| ≤ D * dist x x' := by
  have htri := abs_dist_sub_le x x' y
  have hsum : 0 ≤ dist x y + dist x' y := by positivity
  have hprod := mul_le_mul htri (show dist x y + dist x' y ≤ 2 * D by
      linarith [hD x y, hD x' y]) hsum (dist_nonneg : 0 ≤ dist x x')
  rw [cost, cost]
  have heq : dist x y ^ 2 / 2 - dist x' y ^ 2 / 2 =
      (dist x y - dist x' y) * (dist x y + dist x' y) / 2 := by ring
  rw [heq, abs_div, abs_mul, abs_of_nonneg hsum]
  norm_num
  linarith

variable [CompactSpace M] [Nonempty M]

lemma exists_cTransform_contact {v : M → ℝ} (hv : Continuous v) (x : M) :
    ∃ y, cTransform v x = -cost x y - v y ∧
      ∀ z, -cost x z - v z ≤ cTransform v x := by
  obtain ⟨y, _, hy⟩ := isCompact_univ.exists_isMaxOn
    Set.univ_nonempty (((continuous_cost_right x).neg.sub hv).continuousOn)
  have hg : IsGreatest (Set.range (fun y => -cost x y - v y)) (-cost x y - v y) := by
    refine ⟨Set.mem_range_self y, ?_⟩
    rintro a ⟨z, rfl⟩
    exact hy (Set.mem_univ z)
  refine ⟨y, hg.csSup_eq, ?_⟩
  intro z
  rw [cTransform, hg.csSup_eq]
  exact hy (Set.mem_univ z)

lemma cTransform_gap_nonneg {v : M → ℝ} (hv : Continuous v) (x y : M) :
    0 ≤ contactGap (cTransform v) v x y := by
  obtain ⟨_, _, hmax⟩ := exists_cTransform_contact hv x
  dsimp [contactGap]
  linarith [hmax y]

lemma cTransform_gap_zero {v : M → ℝ} (hv : Continuous v) (x : M) :
    ∃ y, contactGap (cTransform v) v x y = 0 := by
  obtain ⟨y, heq, _⟩ := exists_cTransform_contact hv x
  refine ⟨y, ?_⟩
  dsimp [contactGap]
  rw [heq]
  ring

lemma cTransform_lipschitz {v : M → ℝ} (hv : Continuous v) {D : ℝ≥0}
    (hD : ∀ x y : M, dist x y ≤ D) : LipschitzWith D (cTransform v) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x x'
  rw [Real.dist_eq, abs_le]
  obtain ⟨y, hy, hmax⟩ := exists_cTransform_contact hv x
  obtain ⟨y', hy', hmax'⟩ := exists_cTransform_contact hv x'
  have hcost := cost_lipschitz_of_distance_bound hD x x' y
  have hcost' := cost_lipschitz_of_distance_bound hD x x' y'
  constructor
  · have hh := hmax y'
    rw [hy']
    linarith [(abs_le.mp hcost').2]
  · have hh := hmax' y
    rw [hy]
    linarith [(abs_le.mp hcost).1]

lemma continuous_cTransform {v : M → ℝ} (hv : Continuous v) :
    Continuous (cTransform v) := by
  apply (cTransform_lipschitz hv (D := ⟨Metric.diam (univ : Set M),
    Metric.diam_nonneg⟩) _).continuous
  intro x y
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)

lemma dualPair_gap_nonneg {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x y : M) : 0 ≤ contactGap u v x y := by
  rw [huv.1]
  exact cTransform_gap_nonneg hv x y

lemma dualPair_contact_left {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) : ∃ y, contactGap u v x y = 0 := by
  rw [huv.1]
  exact cTransform_gap_zero hv x

omit [CompactSpace M] [Nonempty M] in
lemma contactGap_symm (u v : M → ℝ) (x y : M) :
    contactGap u v x y = contactGap v u y x := by
  dsimp [contactGap]
  rw [cost_symm x y]
  ring

lemma dualPair_contact_right {u v : M → ℝ} (hu : Continuous u)
    (huv : IsCostDualPair u v) (y : M) : ∃ x, contactGap u v x y = 0 := by
  obtain ⟨x, hx⟩ := dualPair_contact_left hu ⟨huv.2, huv.1⟩ y
  exact ⟨x, (contactGap_symm u v x y).trans hx⟩

lemma homeomorph_of_contact_bounds {u v : M → ℝ} (hu : Continuous u)
    (hv : Continuous v) (huv : IsCostDualPair u v) {alpha C : ℝ}
    (ha : 0 < alpha) (hC : 0 ≤ C)
    (hf : ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist y y' ≤ C * dist x x' ^ alpha)
    (hr : ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist x x' ≤ C * dist y y' ^ alpha) :
    ∃ T : M ≃ₜ M, (∀ x, contactGap u v x (T x) = 0) ∧
      (∀ x x', dist (T x) (T x') ≤ C * dist x x' ^ alpha) ∧
      (∀ y y', dist (T.symm y) (T.symm y') ≤ C * dist y y' ^ alpha) := by
  classical
  choose T hT using dualPair_contact_left hv huv
  choose S hS using dualPair_contact_right hu huv
  have hST : Function.LeftInverse S T := by
    intro x
    apply dist_eq_zero.mp
    have hh := hr (S (T x)) x (T x) (T x) (hS (T x)) (hT x)
    exact le_antisymm (by simpa only [dist_self, Real.zero_rpow ha.ne', mul_zero] using hh)
      dist_nonneg
  have hTS : Function.RightInverse S T := by
    intro y
    apply dist_eq_zero.mp
    have hh := hf (S y) (S y) (T (S y)) y (hT (S y)) (hS y)
    exact le_antisymm (by simpa only [dist_self, Real.zero_rpow ha.ne', mul_zero] using hh)
      dist_nonneg
  have hf' (x x') : dist (T x) (T x') ≤ C * dist x x' ^ alpha :=
    hf x x' (T x) (T x') (hT x) (hT x')
  have hr' (y y') : dist (S y) (S y') ≤ C * dist y y' ^ alpha :=
    hr (S y) (S y') y y' (hS y) (hS y')
  have cont_of_bound (f : M → M)
      (h : ∀ x x', dist (f x) (f x') ≤ C * dist x x' ^ alpha) : Continuous f := by
    have holder : HolderWith ⟨C, hC⟩ ⟨alpha, ha.le⟩ f := by
      intro x x'
      simp only [edist_dist]
      have hh := ENNReal.ofReal_le_ofReal (h x x')
      rw [ENNReal.ofReal_mul hC, ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg ha.le] at hh
      rw [show ENNReal.ofReal C = ENNReal.ofNNReal (NNReal.mk C hC) from
        ENNReal.ofReal_coe_nnreal (p := NNReal.mk C hC)] at hh
      exact hh
    exact holder.continuous ha
  exact ⟨⟨⟨T, S, hST, hTS⟩, cont_of_bound T hf', cont_of_bound S hr'⟩,
    hT, hf', hr'⟩

omit [CompactSpace M] [Nonempty M] in

lemma contactGap_le_of_contact {u v : M → ℝ} {D : ℝ≥0}
    (hu : LipschitzWith D u) (hD : ∀ x y : M, dist x y ≤ D)
    {x x' y : M} (hcontact : contactGap u v x' y = 0) :
    contactGap u v x y ≤ (2 * D) * dist x x' := by
  have hdu := hu.dist_le_mul x x'
  rw [Real.dist_eq, abs_le] at hdu
  have hdc := (abs_le.mp (cost_lipschitz_of_distance_bound hD x x' y)).2
  dsimp [contactGap] at hcontact ⊢
  linarith

omit [CompactSpace M] [Nonempty M] in

lemma contact_section_zero_diameter {u v : M → ℝ} {x y y' : M} {K alpha r0 : ℝ}
    (ha : 0 < alpha) (hr0 : 0 < r0)
    (hsection : ∀ r, 0 < r → r < r0 →
      ∀ z ∈ gapSection u v x r, ∀ z' ∈ gapSection u v x r,
        dist z z' ≤ K * r ^ alpha)
    (hy : contactGap u v x y = 0) (hy' : contactGap u v x y' = 0) :
    dist y y' = 0 := by
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 r0) := by
    rw [closure_Ioo hr0.ne]
    exact ⟨le_rfl, hr0.le⟩
  have hc : Continuous (fun r : ℝ => K * r ^ alpha) :=
    continuous_const.mul (Real.continuous_rpow_const ha.le)
  have hh := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := dist y y')) hc.continuousWithinAt
    (fun r hr => hsection r hr.1 hr.2 y (by simpa [gapSection, hy] using hr.1.le)
      y' (by simpa [gapSection, hy'] using hr.1.le))
  apply le_antisymm _ dist_nonneg
  simpa only [Real.zero_rpow ha.ne', mul_zero] using hh

omit [CompactSpace M] [Nonempty M] in

lemma global_contact_bound_of_local {u v : M → ℝ} {D K alpha delta : ℝ}
    (hD : ∀ y y' : M, dist y y' ≤ D) (hK : 0 ≤ K) (ha : 0 < alpha)
    (hdelta : 0 < delta)
    (hlocal : ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist x x' < delta → dist y y' ≤ K * dist x x' ^ alpha) :
    ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist y y' ≤ (K + max D 0 / delta ^ alpha) * dist x x' ^ alpha := by
  intro x x' y y' hy hy'
  have hrpow : 0 ≤ dist x x' ^ alpha := Real.rpow_nonneg dist_nonneg _
  have hdap : 0 < delta ^ alpha := Real.rpow_pos_of_pos hdelta _
  by_cases hd : dist x x' < delta
  · exact (hlocal x x' y y' hy hy' hd).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right
        (div_nonneg (le_max_right D 0) hdap.le)) hrpow)
  · have hmono : delta ^ alpha ≤ dist x x' ^ alpha :=
      Real.rpow_le_rpow hdelta.le (le_of_not_gt hd) ha.le
    calc
      dist y y' ≤ max D 0 := (hD y y').trans (le_max_left D 0)
      _ = (max D 0 / delta ^ alpha) * delta ^ alpha := by
        rw [div_mul_cancel₀ _ hdap.ne']
      _ ≤ (max D 0 / delta ^ alpha) * dist x x' ^ alpha :=
        mul_le_mul_of_nonneg_left hmono (div_nonneg (le_max_right D 0) hdap.le)
      _ ≤ (K + max D 0 / delta ^ alpha) * dist x x' ^ alpha :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hrpow

omit [CompactSpace M] [Nonempty M] in

lemma contact_bound_of_section_bound {u v : M → ℝ} {D : ℝ≥0}
    (hu : LipschitzWith D u) (hD : ∀ x y : M, dist x y ≤ D)
    {K alpha r0 : ℝ} (hK : 0 ≤ K) (ha : 0 < alpha) (hr0 : 0 < r0)
    (hsection : ∀ x r, 0 < r → r < r0 →
      ∀ y ∈ gapSection u v x r, ∀ y' ∈ gapSection u v x r,
        dist y y' ≤ K * r ^ alpha) :
    ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist y y' ≤
        (K * (2 * D + 1) ^ alpha + D / (r0 / (2 * D + 1)) ^ alpha) *
          dist x x' ^ alpha := by
  let L : ℝ := 2 * D + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hlocal : ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist x x' < r0 / L → dist y y' ≤ (K * L ^ alpha) * dist x x' ^ alpha := by
    intro x x' y y' hy hy' hd
    by_cases heq : x = x'
    · subst x'
      rw [contact_section_zero_diameter ha hr0 (hsection x) hy hy', dist_self,
        Real.zero_rpow ha.ne', mul_zero]
    · have hdist : 0 < dist x x' := dist_pos.mpr heq
      have hr : 0 < L * dist x x' := mul_pos hL hdist
      have hr' : L * dist x x' < r0 := by
        have hm := (lt_div_iff₀ hL).mp hd
        nlinarith
      have hgap : contactGap u v x y' ≤ L * dist x x' :=
        (contactGap_le_of_contact hu hD hy').trans
          (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hdist.le)
      have hh := hsection x (L * dist x x') hr hr' y
        (by simpa [gapSection, hy] using hr.le) y' hgap
      rw [Real.mul_rpow hL.le hdist.le, ← mul_assoc] at hh
      exact hh
  have hh := global_contact_bound_of_local hD
    (mul_nonneg hK (Real.rpow_nonneg hL.le _)) ha (div_pos hr0 hL) hlocal
  simpa only [L, max_eq_left D.coe_nonneg] using hh

end WeakMTWTransport
end

end OAI
