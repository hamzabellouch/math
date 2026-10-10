import OAI.GroupTheory.PolycyclicRecognition.Analysis.DiagonalCellProfilePairs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AffineProfileBoundary

namespace OAI

/-! # Affine limits and retained cell mass on one diagonal -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- An exhausting family of interior affine identities, convergent offsets,
and supported joint laws produce the actual common good sets needed by the
reflection-volume argument, including points over the boundary. -/
theorem exists_diagonal_affine_cell_profiles
    {V W N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace N]
    (q : V →ₗ[ℝ] W) (hq : Continuous q) (hqsurj : Function.Surjective q)
    (cell : Set W) (hconv : Convex ℝ cell) (hclosed : IsClosed cell)
    (hint : (interior cell).Nonempty)
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S]
    [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (K : ℕ → Set V) (hK : ∀ j, IsCompact (K j))
    (hcover : ∀ C : Set V, IsCompact C → ∀ᶠ j in atTop, C ⊆ K j)
    (scale : ℕ → ℕ → ℝ) (hs : ∀ j, Tendsto (scale j) atTop atTop)
    (μ : Measure N) (Q : ℕ → ℕ → Set N)
    (hQ : ∀ j n, MeasurableSet (Q j n))
    (hQ0 : ∀ j n, μ (Q j n) ≠ 0) (hQfin : ∀ j n, μ (Q j n) ≠ ∞)
    (profile : ℕ → ℕ → N → S × S) (hp : ∀ j n, Measurable (profile j n))
    (ν : ℕ → ProbabilityMeasure (S × S))
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure μ (Q j n) (hQ0 j n) (hQfin j n)) (profile j n)) atTop (𝓝 (ν j)))
    (f : ℕ → S × S) (g : S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support)
    (hfg : Tendsto f atTop (𝓝 g))
    (A₁ A₂ : W →L[ℝ] W) (b₁ b₂ : ℕ → W)
    (haff₁ : ∀ z, q z ∈ interior cell → ∀ᶠ j in atTop, (f j).1.val z = A₁ (q z) + b₁ j)
    (haff₂ : ∀ z, q z ∈ interior cell → ∀ᶠ j in atTop, (f j).2.val z = A₂ (q z) + b₂ j)
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ (c₁ c₂ : W) (u n : ℕ → ℕ) (Good : ℕ → Set N),
      Tendsto u atTop atTop ∧ (∀ j, P (u j) (n j)) ∧
      Tendsto (fun j => scale (u j) (n j)) atTop atTop ∧
      (∀ j, MeasurableSet (Good j)) ∧ (∀ j, Good j ⊆ Q (u j) (n j)) ∧
      (∀ j, 0 < (μ (Good j)).toReal) ∧
      HasSubexponentialLowerBoundSeq (fun j => scale (u j) (n j))
        (fun j => (μ (Good j)).toReal / (μ (Q (u j) (n j))).toReal) ∧
      ∀ C : Set V, IsCompact C → ∀ᶠ j in atTop, ∀ x ∈ Good j, ∀ z ∈ C,
        q z ∈ cell →
        ‖(profile (u j) (n j) x).1.val z - (A₁ (q z) + c₁)‖ ≤ 2 / ((j : ℝ) + 1) ∧
        ‖(profile (u j) (n j) x).2.val z - (A₂ (q z) + c₂)‖ ≤ 2 / ((j : ℝ) + 1) := by
  have hlim₁ : Tendsto (fun j => (f j).1.val) atTop (𝓝 g.1.val) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto g).comp hfg
  have hlim₂ : Tendsto (fun j => (f j).2.val) atTop (𝓝 g.2.val) :=
    ((continuous_subtype_val.comp continuous_snd).tendsto g).comp hfg
  obtain ⟨w₀, hw₀⟩ := hint
  obtain ⟨z₀, hz₀⟩ := hqsurj w₀
  let c₁ := g.1.val z₀ - A₁ (q z₀)
  let c₂ := g.2.val z₀ - A₂ (q z₀)
  have hb₁ : Tendsto b₁ atTop (𝓝 c₁) :=
    affine_offset_tendsto _ _ hlim₁ z₀ (A₁ (q z₀)) b₁ (haff₁ z₀ (hz₀ ▸ hw₀))
  have hb₂ : Tendsto b₂ atTop (𝓝 c₂) :=
    affine_offset_tendsto _ _ hlim₂ z₀ (A₂ (q z₀)) b₂ (haff₂ z₀ (hz₀ ▸ hw₀))
  have hg₁ := affine_profile_limit_on_closed_cell q hq hqsurj cell hconv hclosed ⟨w₀, hw₀⟩
    (fun j => (f j).1.val) g.1.val hlim₁ A₁ b₁ c₁ hb₁ haff₁
  have hg₂ := affine_profile_limit_on_closed_cell q hq hqsurj cell hconv hclosed ⟨w₀, hw₀⟩
    (fun j => (f j).2.val) g.2.val hlim₂ A₂ b₂ c₂ hb₂ haff₂
  obtain ⟨u, n, Good, hu, hn, hr, hGood, hGoodQ, hGoodpos, hmass, happ⟩ :=
    exists_diagonal_good_cell_profile_pairs S K hK hcover scale hs μ Q hQ hQ0 hQfin
      profile hp ν hν f g hf hfg P hP
  refine ⟨c₁, c₂, u, n, Good, hu, hn, hr, hGood, hGoodQ, hGoodpos, hmass, ?_⟩
  intro C hC
  filter_upwards [happ C hC] with j hj
  intro x hx z hz hcell
  simpa only [hg₁ z hcell, hg₂ z hcell] using
    And.intro (hj x hx z hz).1.le (hj x hx z hz).2.le

end PolycyclicRecognition

end

end OAI
