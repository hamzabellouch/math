import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicOffsetLimitsFamily
import OAI.Analysis.SymmetricDomains.NormalOffsetFamilyJoint

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
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

lemma offset_joint_moving_limit {S E I : Type*} [TopologicalSpace S]
    [MetricSpace E] [SMul ℝ E] (A : S → Set E) {s₀ : S} {f : E → ℝ}
    (h : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y)))
    {l : Filter I} {s : I → S} {t : I → ℝ} {v : I → E} {w : E}
    (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < t i) (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => offsetDistance A (s i) (t i) (v i)) l (𝓝 (f w)) := by
  have hp₀ : Tendsto (fun i : I => (s i,t i)) l (𝓝 (s₀,(0 : ℝ))) := hs.prodMk_nhds ht
  have hmem : ∀ᶠ i : I in l, (s i,t i) ∈ {p : S × ℝ | 0 < p.2} := hpos
  have hp : Tendsto (fun i : I => (s i,t i)) l (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp₀,hmem⟩
  have hh := (h w).comp hp
  exact moving_offsetDistance_limit A s t hh hv

lemma offset_joint_excluded_limit {S E I : Type*} [TopologicalSpace S]
    [MetricSpace E] [SMul ℝ E] (A : S → Set E) {s₀ : S} {f : E → ℝ}
    (h : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y)))
    {l : Filter I} {s : I → S} {t : I → ℝ} {v : I → E} {w : E}
    (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < t i) (hv : Tendsto v l (𝓝 w)) (hw : f w = 0) :
    Tendsto (fun i => infDist (v i) (offsetScaled A (s i) (t i))ᶜ) l (𝓝 0) := by
  apply tendsto_of_truncated_zero
  simpa only [offsetDistance, hw] using offset_joint_moving_limit A h hs ht hpos hv

lemma offset_joint_interior_ball {S E I : Type*} [TopologicalSpace S]
    [MetricSpace E] [SMul ℝ E] (A : S → Set E) {s₀ : S} {f : E → ℝ}
    (h : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y)))
    {l : Filter I} {s : I → S} {t : I → ℝ} {w : E}
    (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < t i) (hw : 0 < f w) :
    ∀ᶠ i in l, ball w (f w/2) ⊆ offsetScaled A (s i) (t i) := by
  have hp₀ : Tendsto (fun i : I => (s i,t i)) l (𝓝 (s₀,(0 : ℝ))) := hs.prodMk_nhds ht
  have hmem : ∀ᶠ i : I in l, (s i,t i) ∈ {p : S × ℝ | 0 < p.2} := hpos
  have hp : Tendsto (fun i : I => (s i,t i)) l (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp₀,hmem⟩
  have hh := (h w).comp hp
  exact eventual_offset_ball A s t hw hh

theorem semialgebraic_joint_boundary_data_from_family {n k : ℕ}
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A z.1})
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (hb : ∀ s ∈ B, (s,(0 : Fin k → ℝ)) ∈
      closure {p : (Fin n → ℝ) × (Fin k → ℝ) | p.2 ∈ A p.1})
    (h0 : ∀ s ∈ B, (0 : Fin k → ℝ) ∉ A s) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E →
        (∃ r > 0, ∃ η > 0, ∃ ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ),
          ball s r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 η) ∧
          (∀ x ∈ ball s r, ψ (x,0) = 0) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η, ψ (x,t) ∈ A x) ∧
        ∃ f : (Fin k → ℝ) → ℝ, LipschitzWith 1 f ∧
          (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
          (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
          (∀ K : Set (Fin k → ℝ), IsCompact K →
            TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2) f
              (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K) ∧
          IsClosed {y | f y = 0} ∧ (0 : Fin k → ℝ) ∈ {y | f y = 0} ∧
          ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 := by
  obtain ⟨E₁,hE₁B,hE₁,H₁⟩ := semialgebraic_inward_analytic_from_family A hA B hB hBs hb
  obtain ⟨E₂,hE₂B,hE₂,H₂⟩ := semialgebraic_offset_limits_from_family A hA B hB hBs h0
  refine ⟨E₁ ∪ E₂,union_subset hE₁B hE₂B,measure_union_null hE₁ hE₂,?_⟩
  intro s hs hsE
  exact ⟨H₁ s hs (fun h => hsE (Or.inl h)),H₂ s hs (fun h => hsE (Or.inr h))⟩

theorem semialgebraic_chart_boundary_data {n k : ℕ}
    (U : Set ((Fin n → ℝ) × (Fin k → ℝ)))
    (hU : PolynomialSignSet (fun z => Sum.elim z.1 z.2) U)
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (φ : (Fin n → ℝ) → (Fin k → ℝ)) (hφc : ContinuousOn φ B)
    (hφs : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.1 ∈ B ∧ z.2 = φ z.1}) (ρ : ℝ) (hρ : 0 < ρ)
    (hb : ∀ s ∈ B, (s,φ s) ∈ closure U ∧ (s,φ s) ∉ U) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E →
        (∃ r > 0, ∃ η > 0, ∃ ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ),
          ball s r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 η) ∧
          (∀ x ∈ ball s r, ψ (x,0) = 0) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η,
            ψ (x,t) ∈ normalOffsetFamily U B φ ρ x) ∧
        ∃ f : (Fin k → ℝ) → ℝ, LipschitzWith 1 f ∧
          (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
          (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ =>
            offsetDistance (normalOffsetFamily U B φ ρ) p.1 p.2 y)
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
          (∀ K : Set (Fin k → ℝ), IsCompact K →
            TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ =>
              offsetDistance (normalOffsetFamily U B φ ρ) p.1 p.2) f
              (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K) ∧
          IsClosed {y | f y = 0} ∧ (0 : Fin k → ℝ) ∈ {y | f y = 0} ∧
          ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 := by
  apply semialgebraic_joint_boundary_data_from_family (normalOffsetFamily U B φ ρ)
    (normalOffsetFamily_polynomialSignSet ρ hU hφs) B hB hBs
  · intro s hs
    exact normalOffsetFamily_joint_closure (hB.mem_nhds hs)
      ((hφc s hs).continuousAt (hB.mem_nhds hs)) hρ (hb s hs).1
  · intro s hs
    exact normalOffsetFamily_zero_not_mem (hb s hs).2

end Release061

end

end OAI
