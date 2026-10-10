import Mathlib
import OAI.Analysis.SymmetricDomains.OffsetLimitClosedCone
import OAI.Analysis.SymmetricDomains.FiniteCommonRamification

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric MeasureTheory Topology

theorem finite_semialgebraic_ramification {n : ℕ} {J : Type*} [Fintype J]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : J → (Fin (n+1) → ℝ) → ℝ)
    (hgraph : ∀ j, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b j (fun i => x (some i))})
    (M : J → ℝ) (hbound : ∀ j (x : Fin (n+1) → ℝ),
      Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b j x‖ ≤ M j) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ L : ℕ, 0 < L ∧ ∃ η > 0,
        ∃ F : J → (Fin n → ℝ) × ℝ → ℝ,
          ball s r ⊆ B ∧
          (∀ j, AnalyticOnNhd ℝ (F j) (ball s r ×ˢ ball 0 η)) ∧
          ∀ j, ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η,
            F j (x,t) = b j (Fin.cons (t^L) x) := by
  choose E hEB hE hg using fun j =>
    semialgebraic_ramification_with_parameters hB hε (b j) (hgraph j) (hbound j)
  refine ⟨⋃ j, E j,iUnion_subset hEB,measure_iUnion_null hE,?_⟩
  intro s hs hsE
  have hg' : ∀ j, ∃ r > 0, ∃ l : ℕ, 0 < l ∧ ∃ η > 0,
      ∃ F : (Fin n → ℝ) × ℝ → ℝ,
        AnalyticOnNhd ℝ F (ball s r ×ˢ ball 0 η) ∧
        ∀ x ∈ ball s r, ∀ u ∈ Ioo (0 : ℝ) η,
          F (x,u) = b j (Fin.cons (u^l) x) := by
    intro j
    obtain ⟨r,hr,l,hl,η,hη,F,_,hFa,hF⟩ :=
      hg j s hs (fun h => hsE (mem_iUnion.mpr ⟨j,h⟩))
    exact ⟨r,hr,l,hl,η,hη,F,hFa,hF⟩
  obtain ⟨r,hr,L,hL,η,hη,F,hFa,hF⟩ :=
    finite_common_ramification (fun j p => b j (Fin.cons p.2 p.1)) s hg'
  obtain ⟨r₀,hr₀,hrB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hs)
  refine ⟨min r r₀,lt_min hr hr₀,L,hL,η,hη,F,?_,?_,?_⟩
  · exact (ball_subset_ball (min_le_right _ _)).trans hrB
  · intro j
    exact (hFa j).mono (Set.prod_mono (ball_subset_ball (min_le_left _ _)) Subset.rfl)
  · intro j x hx t ht
    exact hF j x (ball_subset_ball (min_le_left _ _) hx) t ht

lemma tendsto_positive_vertical {E : Type*} [TopologicalSpace E] (s : E) :
    Tendsto (fun t : ℝ => (s,t)) (𝓝[>] (0 : ℝ))
      (𝓝[{p : E × ℝ | 0 < p.2}] (s,0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_const_nhds.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds),self_mem_nhdsWithin⟩

theorem semialgebraic_lipschitz_boundary_limits {n : ℕ} {Y : Type*}
    [PseudoMetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin (n+1) → ℝ) → Y → ℝ)
    (hgraph : ∀ y, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b (fun i => x (some i)) y})
    (M : Y → ℝ) (hbound : ∀ y (x : Fin (n+1) → ℝ),
      Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b x y‖ ≤ M y)
    (hLip : ∀ x, LipschitzWith 1 (b x)) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ f : Y → ℝ, LipschitzWith 1 f ∧
        (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => b (Fin.cons p.2 p.1) y)
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
        ∀ K : Set Y, IsCompact K →
          TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => b (Fin.cons p.2 p.1)) f
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K := by
  obtain ⟨D,hD,hDense⟩ := TopologicalSpace.exists_countable_dense Y
  let : Countable D := hD.to_subtype
  obtain ⟨E,hEB,hE,hg⟩ := countable_semialgebraic_joint_boundary_limits hB hε
    (fun y : D => fun x => b x y.val) (fun y => hgraph y.val)
    (fun y => M y.val) (fun y => hbound y.val)
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  have : NeBot (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) :=
    (tendsto_positive_vertical s).neBot
  exact dense_lipschitz_test_limits _ (fun p => hLip (Fin.cons p.2 p.1)) hDense
    (fun y hy => hg s hs hsE ⟨y,hy⟩)

theorem semialgebraic_offset_joint_limits {n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace.SeparableSpace Y]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (A : (Fin n → ℝ) → Set Y)
    (hgraph : ∀ y, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = offsetDistance A (fun i => x (some i.succ)) (x (some 0)) y}) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ f : Y → ℝ, LipschitzWith 1 f ∧
        (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
        ∀ K : Set Y, IsCompact K →
          TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2) f
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K := by
  have hg : ∀ y, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = (fun a : Fin (n+1) → ℝ => offsetDistance A (Fin.tail a) (a 0) y)
            (fun i => x (some i))} := hgraph
  have H := semialgebraic_lipschitz_boundary_limits hB hε
    (fun a : Fin (n+1) → ℝ => offsetDistance A (Fin.tail a) (a 0)) hg
    (fun _ => (1 : ℝ)) (fun y x _ _ => by
      rw [Real.norm_of_nonneg (offsetDistance_nonneg A _ _ _)]
      exact offsetDistance_le_one A _ _ _) (fun x => offsetDistance_lipschitz A _ _)
  simpa only [Fin.tail_cons,Fin.cons_zero] using H

theorem semialgebraic_offset_limits {n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace.SeparableSpace Y]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (A : (Fin n → ℝ) → Set Y) (h0 : ∀ s ∈ B, (0 : Y) ∉ A s)
    (hgraph : ∀ y, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = offsetDistance A (fun i => x (some i.succ)) (x (some 0)) y}) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ f : Y → ℝ, LipschitzWith 1 f ∧
        (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
        (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
        (∀ K : Set Y, IsCompact K →
          TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2) f
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K) ∧
        IsClosed {y | f y = 0} ∧ (0 : Y) ∈ {y | f y = 0} ∧
        ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 := by
  obtain ⟨E,hEB,hE,H⟩ := semialgebraic_offset_joint_limits hB hε A hgraph
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  obtain ⟨f,hf,hpt,hunif⟩ := H s hs hsE
  have : NeBot (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) :=
    (tendsto_positive_vertical s).neBot
  have hvertical (y : Y) : Tendsto (fun t : ℝ => offsetDistance A s t y)
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
    have H := (hpt y).comp (tendsto_positive_vertical s)
    exact H
  have hcone : IsClosed {y | f y = 0} ∧ (0 : Y) ∈ {y | f y = 0} ∧
      ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 :=
    offset_limit_closed_cone A s (h0 s hs) hf hvertical
  refine ⟨f,hf,?_,hpt,hunif,hcone⟩
  intro y
  exact ⟨ge_of_tendsto (hpt y) (Eventually.of_forall fun p => offsetDistance_nonneg A p.1 p.2 y),
    le_of_tendsto (hpt y) (Eventually.of_forall fun p => offsetDistance_le_one A p.1 p.2 y)⟩

end Release061

end

end OAI
