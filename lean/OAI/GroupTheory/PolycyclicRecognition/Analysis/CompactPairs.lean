import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Algebra.Group.Basic

namespace OAI

/-! # Compact sections of Lipschitz quasi-inverse pairs

The space consists of actual continuous maps, with the compact-open topology.
Uniform Lipschitz bounds and a bound at one point give compactness in a proper
target. The quasi-inverse conditions are closed, including their compositions.
-/

noncomputable section

open Set Metric
open scoped NNReal

namespace PolycyclicRecognition

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [ProperSpace Y]

/-- The compact family of maps with a common Lipschitz constant and a common
bound at one point. -/
theorem isCompact_lipschitz_family (K : ℝ≥0) (a : X) (b : Y) (R : ℝ) :
    IsCompact {f : C(X, Y) | LipschitzWith K f ∧ dist (f a) b ≤ R} := by
  let S : Set C(X, Y) := {f | LipschitzWith K f ∧ dist (f a) b ≤ R}
  let T : Set (X → Y) := {f | LipschitzWith K f ∧ dist (f a) b ≤ R}
  have hT : IsClosed T :=
    (isClosed_setOfPred_lipschitzWith K).inter
      (isClosed_le ((continuous_apply a).dist continuous_const) continuous_const)
  have heq : ContinuousMap.toFun '' S = T := by
    ext f
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · rintro ⟨hf, hb⟩
      exact ⟨⟨f, hf.continuous⟩, ⟨hf, hb⟩, rfl⟩
  have hcompact : IsCompact T := by
    apply (isCompact_pi_infinite (fun x : X =>
      isCompact_closedBall b ((K : ℝ) * dist x a + R))).of_isClosed_subset hT
    intro f hf x
    change dist (f x) b ≤ (K : ℝ) * dist x a + R
    exact (dist_triangle (f x) (f a) b).trans
      (add_le_add (hf.1.dist_le_mul x a) hf.2)
  apply ArzelaAscoli.isCompact_of_equicontinuous S
  · rwa [heq]
  · exact (LipschitzWith.uniformEquicontinuous
      (fun f : S => (f : C(X, Y))) K (fun f => f.property.1)).equicontinuous

variable (G : Type*) [Group G] [MetricSpace G] [ProperSpace G]

/-- Uniform Lipschitz, lower-distance, and two-sided quasi-inverse bounds.
The source manuscript uses the same constant in these four bounds. -/
def LipschitzPairBounds (Λ : ℝ≥0) (p : C(G, G) × C(G, G)) : Prop :=
  LipschitzWith Λ p.1 ∧ LipschitzWith Λ p.2 ∧
    (∀ x y, (Λ : ℝ)⁻¹ * dist x y - Λ ≤ dist (p.1 x) (p.1 y)) ∧
    (∀ x y, (Λ : ℝ)⁻¹ * dist x y - Λ ≤ dist (p.2 x) (p.2 y)) ∧
    (∀ x, dist (p.2 (p.1 x)) x ≤ Λ) ∧
    (∀ x, dist (p.1 (p.2 x)) x ≤ Λ)

/-- The first normalized section: the forward map sends the identity to itself. -/
def normalizedPairs (Λ : ℝ≥0) : Set (C(G, G) × C(G, G)) :=
  {p | LipschitzPairBounds G Λ p ∧ p.1 1 = 1}

omit [Group G] in
theorem isClosed_lipschitzPairBounds (Λ : ℝ≥0) :
    IsClosed {p | LipschitzPairBounds G Λ p} := by
  have hcoe : Continuous (fun f : C(G, G) => (f : G → G)) :=
    continuous_pi fun x => continuous_eval_const x
  have hl : IsClosed {f : C(G, G) | LipschitzWith Λ f} :=
    (isClosed_setOfPred_lipschitzWith Λ).preimage hcoe
  have hf (x : G) : Continuous (fun p : C(G, G) × C(G, G) => p.1 x) :=
    (continuous_eval_const x).comp continuous_fst
  have hr (x : G) : Continuous (fun p : C(G, G) × C(G, G) => p.2 x) :=
    (continuous_eval_const x).comp continuous_snd
  have hfr (x : G) : Continuous (fun p : C(G, G) × C(G, G) => p.2 (p.1 x)) :=
    continuous_eval.comp (continuous_snd.prodMk (hf x))
  have hrf (x : G) : Continuous (fun p : C(G, G) × C(G, G) => p.1 (p.2 x)) :=
    continuous_eval.comp (continuous_fst.prodMk (hr x))
  simp only [LipschitzPairBounds, Set.ofPred_and, Set.ofPred_forall]
  exact (hl.preimage continuous_fst).inter ((hl.preimage continuous_snd).inter
    ((isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const ((hf x).dist (hf y))).inter
    ((isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const ((hr x).dist (hr y))).inter
    ((isClosed_iInter fun x => isClosed_le ((hfr x).dist continuous_const) continuous_const).inter
      (isClosed_iInter fun x => isClosed_le ((hrf x).dist continuous_const) continuous_const)))))

theorem isClosed_normalizedPairs (Λ : ℝ≥0) : IsClosed (normalizedPairs G Λ) :=
  (isClosed_lipschitzPairBounds G Λ).inter
    (isClosed_eq ((continuous_eval_const 1).comp continuous_fst) continuous_const)

/-- Both maps are anchored on the normalized section: the inverse anchor
bound follows from its quasi-inverse bound and the forward normalization. -/
theorem isCompact_normalizedPairs (Λ : ℝ≥0) : IsCompact (normalizedPairs G Λ) := by
  apply ((isCompact_lipschitz_family Λ (1 : G) 1 Λ).prod
    (isCompact_lipschitz_family Λ (1 : G) 1 Λ)).of_isClosed_subset
      (isClosed_normalizedPairs G Λ)
  intro p hp
  refine ⟨⟨hp.1.1, ?_⟩, ⟨hp.1.2.1, ?_⟩⟩
  · simp [hp.2]
  · simpa only [hp.2] using hp.1.2.2.2.2.1 1

/-- Actual normalized pairs, carrying their compact-open topology. -/
abbrev NormalizedPair (Λ : ℝ≥0) := normalizedPairs G Λ

instance (Λ : ℝ≥0) : CompactSpace (NormalizedPair G Λ) :=
  isCompact_iff_compactSpace.mp (isCompact_normalizedPairs G Λ)

end PolycyclicRecognition

end

end OAI
