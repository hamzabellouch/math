import Mathlib
import OAI.Analysis.SymmetricDomains.JointLimitRamification

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

section
open Set Filter Metric MeasureTheory Topology

theorem semialgebraic_joint_boundary_limit {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin (n+1) → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b (fun i => x (some i))})
    {M : ℝ} (hbound : ∀ x : Fin (n+1) → ℝ, Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b x‖ ≤ M) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ L : ℝ,
        Tendsto (fun p : (Fin n → ℝ) × ℝ => b (Fin.cons p.2 p.1))
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 L) := by
  obtain ⟨E,hEB,hE,hg⟩ := semialgebraic_ramification_with_parameters hB hε b hgraph hbound
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  obtain ⟨r,hr,l,hl,η,hη,F,_,hFa,hF⟩ := hg s hs hsE
  exact ⟨F (s,0),joint_limit_of_ramification _ F s hr hη hl
    (hFa (s,0) ⟨mem_ball_self hr,mem_ball_self hη⟩).continuousAt hF⟩

theorem countable_semialgebraic_joint_boundary_limits {n : ℕ} {J : Type*} [Countable J]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : J → (Fin (n+1) → ℝ) → ℝ)
    (hgraph : ∀ j, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b j (fun i => x (some i))})
    (M : J → ℝ) (hbound : ∀ j (x : Fin (n+1) → ℝ),
      Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b j x‖ ≤ M j) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∀ j, ∃ L : ℝ,
        Tendsto (fun p : (Fin n → ℝ) × ℝ => b j (Fin.cons p.2 p.1))
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 L) := by
  choose E hEB hE hg using fun j =>
    semialgebraic_joint_boundary_limit hB hε (b j) (hgraph j) (hbound j)
  refine ⟨⋃ j, E j,iUnion_subset hEB,measure_iUnion_null hE,?_⟩
  intro s hs hsE j
  exact hg j s hs (fun h => hsE (mem_iUnion.mpr ⟨j,h⟩))

end

open Set Filter Metric Topology

theorem finite_common_ramification {E J : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype J] (b : J → E × ℝ → ℝ) (s : E)
    (h : ∀ j, ∃ r > 0, ∃ l : ℕ, 0 < l ∧ ∃ η > 0, ∃ F : E × ℝ → ℝ,
      AnalyticOnNhd ℝ F (ball s r ×ˢ ball 0 η) ∧
      ∀ x ∈ ball s r, ∀ u ∈ Ioo (0 : ℝ) η, F (x,u) = b j (x,u^l)) :
    ∃ r > 0, ∃ L : ℕ, 0 < L ∧ ∃ η > 0, ∃ F : J → E × ℝ → ℝ,
      (∀ j, AnalyticOnNhd ℝ (F j) (ball s r ×ˢ ball 0 η)) ∧
      ∀ j, ∀ x ∈ ball s r, ∀ u ∈ Ioo (0 : ℝ) η, F j (x,u) = b j (x,u^L) := by
  classical
  choose r hr l hl η hη F hFa hF using h
  let L := ∏ j, l j
  let q : J → ℕ := fun j => ∏ k ∈ Finset.univ.erase j, l k
  have hL : 0 < L := Finset.prod_pos (fun j _ => hl j)
  have hq : ∀ j, 0 < q j := fun j => Finset.prod_pos (fun k _ => hl k)
  have hqL : ∀ j, q j * l j = L := fun j => Finset.prod_erase_mul _ _ (Finset.mem_univ j)
  let e : J → E × ℝ → E × ℝ := fun j p => (p.1,p.2 ^ q j)
  have he : ∀ j, Continuous (e j) := fun j => continuous_fst.prodMk (continuous_snd.pow _)
  have he₀ : ∀ j, e j (s,0) = (s,0) := by
    intro j
    simp only [e,zero_pow (hq j).ne']
  have hN : ∀ᶠ p in 𝓝 ((s,0) : E × ℝ), ∀ j,
      e j p ∈ ball s (r j) ×ˢ ball 0 (η j) := by
    apply eventually_all.mpr
    intro j
    have hT : Tendsto (e j) (𝓝 ((s,0) : E × ℝ)) (𝓝 ((s,0) : E × ℝ)) := by
      simpa only [he₀ j] using (he j).continuousAt.tendsto (x := (s,0))
    exact hT ((isOpen_ball.prod isOpen_ball).mem_nhds
      ⟨mem_ball_self (hr j),mem_ball_self (hη j)⟩)
  obtain ⟨δ,hδ,hδN⟩ := Metric.mem_nhds_iff.mp hN
  have hrect : ∀ p ∈ ball s δ ×ˢ ball (0 : ℝ) δ, ∀ j,
      e j p ∈ ball s (r j) ×ˢ ball 0 (η j) := by
    intro p hp
    apply hδN
    simpa only [mem_prod,mem_ball,Prod.dist_eq,max_lt_iff] using hp
  refine ⟨δ,hδ,L,hL,δ,hδ,(fun j => F j ∘ e j),?_,?_⟩
  · intro j p hp
    apply (hFa j _ (hrect p hp j)).comp
    exact (ContinuousLinearMap.fst ℝ E ℝ).analyticAt p |>.prod
      (((ContinuousLinearMap.snd ℝ E ℝ).analyticAt p).pow (q j))
  · intro j x hx u hu
    have hp : (x,u) ∈ ball s δ ×ˢ ball (0 : ℝ) δ := by
      refine ⟨hx,?_⟩
      simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hu.1] using hu.2
    have hp' := hrect (x,u) hp j
    have hpos : 0 < u ^ q j := pow_pos hu.1 _
    have hlt : u ^ q j < η j := by
      simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hpos,e]
        using hp'.2
    change F j (x,u ^ q j) = b j (x,u^L)
    rw [hF j x hp'.1 (u ^ q j) ⟨hpos,hlt⟩,← pow_mul,hqL j]

end Release061

end

end OAI
