import OAI.Geometry.RCD.Harmonic.FiniteHarmonicSubsequence
import OAI.Geometry.RCD.Harmonic.BoundedHarmonicCompactness

namespace OAI

/-! # A common smooth harmonic limit for a prescribed finite family -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem finite_subsequence_value_choice {ι D : Type*} [Fintype ι] [Inhabited D]
    (P : ι → (ℕ → ℕ) → D → Prop)
    (hsub : ∀ i α g β, P i α g → StrictMono β → P i (α∘β) g)
    (hex : ∀ α : ℕ → ℕ, StrictMono α → ∀ i, ∃ β : ℕ → ℕ, StrictMono β ∧ ∃ g, P i (α∘β) g) :
    ∃ α, StrictMono α ∧ ∃ g : ι → D, ∀ i, P i α (g i) := by
  classical
  have hfinite (s : Finset ι) : ∃ α, StrictMono α ∧ ∃ g : ι → D, ∀ i ∈ s, P i α (g i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id,strictMono_id,fun _ => default,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨α,hα,g,hg⟩ := ih
      obtain ⟨β,hβ,v,hv⟩ := hex α hα i
      refine ⟨α∘β,hα.comp hβ,Function.update g i v,?_⟩
      intro j hj
      by_cases hji : j=i
      · subst j
        simpa only [Function.update_self] using hv
      · rw [Function.update_of_ne hji]
        exact hsub j α (g j) β (hg j ((Finset.mem_insert.mp hj).resolve_left hji)) hβ
  obtain ⟨α,hα,g,hg⟩ := hfinite Finset.univ
  exact ⟨α,hα,g,fun i => hg i (Finset.mem_univ i)⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.finite_bounded_harmonic_limits {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {S M : ℝ} (hS : 0 < S) (hM : 0 < M)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*r k^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    {ι : Type*} [Fintype ι] (w : ι → ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ i k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w i k))
    (hnorm : ∀ i k, harmonicTargetNorm hX (p k) (S*r k) (w i k) ≤ M) :
    ∃ α : ℕ → ℕ, StrictMono α ∧ ∃ g : ι → Euclidean n → ℝ,
      (∀ i, InnerProductSpace.HarmonicOnNhd (g i) (ball 0 S)) ∧
      (∀ i, ContDiffOn ℝ ∞ (g i) (ball 0 S)) ∧
      (∀ i W, W < S → ∃ L : ℝ≥0, LipschitzOnWith L (g i) (closedBall 0 W)) ∧
      ∀ i W, 0 < W → W < S → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (α k)) (W*r (α k))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i (α k)) x-g i (V (α k) x)| ≤ δ := by
  let P := fun (i : ι) (α : ℕ → ℕ) (g : Euclidean n → ℝ) =>
    InnerProductSpace.HarmonicOnNhd g (ball 0 S) ∧ ContDiffOn ℝ ∞ g (ball 0 S) ∧
    (∀ W < S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W)) ∧
    ∀ W : ℝ, 0 < W → W < S → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (α k)) (W*r (α k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i (α k)) x-g (V (α k) x)| ≤ δ
  have hsub : ∀ i α g β, P i α g → StrictMono β → P i (α∘β) g := by
    rintro i α g β ⟨hh,hg,hL,hconv⟩ hβ
    exact ⟨hh,hg,hL,fun W hW hWS δ hδ => hβ.tendsto_atTop.eventually (hconv W hW hWS δ hδ)⟩
  have hex : ∀ α : ℕ → ℕ, StrictMono α → ∀ i, ∃ β : ℕ → ℕ, StrictMono β ∧ ∃ g, P i (α∘β) g := by
    intro α hα i
    obtain ⟨β,hβ,g,_,hgc,hgw,hgs,hgL,hconv⟩ := hX.bounded_harmonic_compactness hn hS hM
      (p∘α) (r∘α) (ε∘α) (V∘α) (fun k => hr (α k)) (fun k => hcurv (α k))
      (fun k => hε (α k)) (fun k => hε1 (α k)) (hεlim.comp hα.tendsto_atTop)
      (fun k => hV (α k)) (w i∘α) (fun k => hw i (α k)) (fun k => hnorm i (α k))
    exact ⟨β,hβ,g,continuous_weak_harmonic hgc hgw,hgs,hgL,hconv⟩
  obtain ⟨α,hα,g,hg⟩ := finite_subsequence_value_choice P hsub hex
  exact ⟨α,hα,g,fun i => (hg i).1,fun i => (hg i).2.1,
    fun i => (hg i).2.2.1,fun i => (hg i).2.2.2⟩

end RegularPointCoordinates

end

end OAI
