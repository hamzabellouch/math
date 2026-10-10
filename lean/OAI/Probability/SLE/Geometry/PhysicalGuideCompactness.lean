import OAI.Probability.SLE.Geometry.GuideLimitIdentification
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

namespace OAI

/-!
Uniform subsequence compactness for the physical guide curves. A common speed
bound and bounded starting points put the entire family in one compact disk;
Arzelà–Ascoli then gives a uniformly convergent subsequence on the fixed interval.
-/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal BoundedContinuousFunction

namespace SLEExactGauge.PhysicalGuideCompactness

/-- A common Lipschitz bound and bounded tips suffice for uniform subsequence
compactness of the physical guides. The limit retains the same speed bound. -/
theorem exists_uniform_subsequence
    (αₙ : ℕ → ℝ → ℂ) {T R : ℝ} (hT : 0 ≤ T) (C : ℝ≥0)
    (hL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 T))
    (htip : ∀ n, ‖αₙ n 0‖ ≤ R) :
    ∃ α : ℝ → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop (Icc 0 T) ∧
      LipschitzOnWith C α (Icc 0 T) ∧ ContinuousOn α (Icc 0 T) ∧ ‖α 0‖ ≤ R := by
  classical
  let I := Icc (0 : ℝ) T
  have : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : ℕ → I →ᵇ ℂ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨I.domRestrict (αₙ n), (hL n).continuousOn.domRestrict⟩
  have hfL : ∀ n, LipschitzWith C (f n) := fun n => (hL n).to_restrict
  have hbound n (t : I) : ‖f n t‖ ≤ R + C * T := by
    have hd := (hL n).dist_le_mul t t.property 0 (show 0 ∈ I from ⟨le_rfl, hT⟩)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1] at hd
    have hh := norm_le_norm_add_const_of_dist_le hd
    exact hh.trans (add_le_add (htip n) (mul_le_mul_of_nonneg_left t.property.2 C.coe_nonneg))
  have heq : Equicontinuous ((↑) : Set.range f → I → ℂ) := by
    apply (LipschitzWith.uniformEquicontinuous _ C ?_).equicontinuous
    rintro ⟨g, n, rfl⟩
    exact hfL n
  have hcompact : IsCompact (closure (Set.range f)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) (R + C * T))
      (isCompact_closedBall _ _) (Set.range f)
      (by rintro g t ⟨n, rfl⟩; simpa only [mem_closedBall, dist_zero_right] using hbound n t)
      heq
  obtain ⟨b, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hb : TendstoUniformly (fun n => f (φ n)) b atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  let α : ℝ → ℂ := fun t => if ht : t ∈ I then b ⟨t, ht⟩ else 0
  have hu : TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop I := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hb ε hε] with n hn
    intro t ht
    simpa [α, f, ht] using hn ⟨t, ht⟩
  have hαL : LipschitzOnWith C α I := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro s hs t ht
    exact le_of_tendsto ((hu.tendsto_at hs).dist (hu.tendsto_at ht))
      (Eventually.of_forall fun n => (hL (φ n)).dist_le_mul s hs t ht)
  have hα0 : ‖α 0‖ ≤ R := le_of_tendsto
    (hu.tendsto_at (show 0 ∈ I from ⟨le_rfl, hT⟩)).norm
    (Eventually.of_forall fun n => htip (φ n))
  exact ⟨α, φ, hφ, hu, hαL, hαL.continuousOn, hα0⟩

/-- The fixed lower chord bound of a guide patch passes to its uniform limit. -/
theorem lower_chord_bound_of_uniform_limit
    {αₙ : ℕ → ℝ → ℂ} {α : ℝ → ℂ} {I : Set ℝ} {c : ℝ}
    (hu : TendstoUniformlyOn αₙ α atTop I)
    (hchord : ∀ n s, s ∈ I → ∀ t, t ∈ I →
      c * |s - t| ≤ dist (αₙ n s) (αₙ n t)) :
    ∀ s ∈ I, ∀ t ∈ I, c * |s - t| ≤ dist (α s) (α t) := by
  intro s hs t ht
  exact ge_of_tendsto ((hu.tendsto_at hs).dist (hu.tendsto_at ht))
    (Eventually.of_forall fun n => hchord n s hs t ht)

/-- Positive lower chord bounds force a guide to be simple. -/
theorem injective_of_lower_chord_bound
    {α : ℝ → ℂ} {I : Set ℝ} {c : ℝ} (hc : 0 < c)
    (hchord : ∀ s ∈ I, ∀ t ∈ I, c * |s - t| ≤ dist (α s) (α t)) :
    InjOn α I := by
  intro s hs t ht he
  have hh := hchord s hs t ht
  rw [he, dist_self] at hh
  have ha : |s - t| = 0 := by nlinarith [abs_nonneg (s - t)]
  exact sub_eq_zero.mp (abs_eq_zero.mp ha)

/-- Bi-Lipschitz physical guide patches have simple, uniformly convergent
subsequential limits with the same two chord constants. -/
theorem exists_simple_uniform_subsequence
    (αₙ : ℕ → ℝ → ℂ) {T R c : ℝ} (hT : 0 ≤ T) (C : ℝ≥0) (hc : 0 < c)
    (hL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 T))
    (htip : ∀ n, ‖αₙ n 0‖ ≤ R)
    (hchord : ∀ n s, s ∈ Icc 0 T → ∀ t, t ∈ Icc 0 T →
      c * |s - t| ≤ dist (αₙ n s) (αₙ n t)) :
    ∃ α : ℝ → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop (Icc 0 T) ∧
      LipschitzOnWith C α (Icc 0 T) ∧ ContinuousOn α (Icc 0 T) ∧ ‖α 0‖ ≤ R ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, c * |s - t| ≤ dist (α s) (α t)) ∧
      InjOn α (Icc 0 T) := by
  obtain ⟨α, φ, hφ, hu, hLα, hcont, htipα⟩ :=
    exists_uniform_subsequence αₙ hT C hL htip
  have hchordα := lower_chord_bound_of_uniform_limit hu (fun n => hchord (φ n))
  exact ⟨α, φ, hφ, hu, hLα, hcont, htipα, hchordα,
    injective_of_lower_chord_bound hc hchordα⟩

end SLEExactGauge.PhysicalGuideCompactness

end

end OAI
