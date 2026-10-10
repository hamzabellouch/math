import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedChainProbeSelection
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! # Pointwise affine bounds on every retained probe prefix -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The supported compact-map comparison yields the actual pointwise
bounds used on all the Cartan legs, with one tolerance for every probe. -/
theorem exists_supported_affine_probe_sequence
    {X Z W V C : Type*} [Nonempty X] [MeasurableSpace X]
    [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [AddCommGroup V] [Module ℝ V] [Fintype C]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))]
    [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    {Y : ℕ → Type*} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    (carrying : Set X) (hcarrying : MeasurableSet carrying)
    (hfull : (μ : Measure X) carryingᶜ = 0)
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → C(Z, W) × C(Z, W)) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (profile n)) atTop (𝓝 limitLaw))
    {f : C(Z, W) × C(Z, W)} (hf : f ∈ (limitLaw : Measure (C(Z, W) × C(Z, W))).support)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : Bool → W)
    (haffine : ∀ s z, (if s then f.2 else f.1) z = A (q z) + b s)
    (chain : ∀ n, X × Y n → C → C(Z, W)) (sheet : C → Bool)
    (hm : ∀ n i, Measurable (fun p : X × Y n =>
      dist (chain n p i) (if sheet i then (profile n p.1).2 else (profile n p.1).1)))
    (hdet : ∀ i (ε : ℝ), 0 < ε → ∀ y : ∀ n, Y n,
      Tendsto (fun n => (μ : Measure X)
        {x | ε ≤ dist (chain n (x, y n) i)
          (if sheet i then (profile n x).2 else (profile n x).1)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop, x n ∈ carrying ∧
        (∀ s z, ‖(if s then (profile n (x n)).2 else (profile n (x n)).1) z -
          (A (q z) + b s)‖ < ε n) ∧
        ∀ y ∈ K n, ∀ i z,
          ‖chain n (x n, y) i z - (A (q z) + b (sheet i))‖ < 2 * ε n := by
  obtain ⟨ε, x, K, hεpos, hε, hK, he⟩ := exists_supported_chain_probe_sequence
    μ ν carrying hcarrying hfull profile hp limitLaw hlim hf chain sheet hm hdet
  refine ⟨ε, x, K, hεpos, hε, hK, he.mono ?_⟩
  intro n hn
  refine ⟨hn.1, ?_, ?_⟩
  · intro s z
    rw [← haffine s z, ← dist_eq_norm]
    apply (ContinuousMap.dist_apply_le_dist z).trans_lt
    have hdist : dist (if s then (profile n (x n)).2 else (profile n (x n)).1)
        (if s then f.2 else f.1) ≤ dist (profile n (x n)) f := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.dist_eq]
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact hdist.trans_lt hn.2.1
  · intro y hy i z
    rw [← haffine (sheet i) z, ← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist z).trans_lt (hn.2.2 y hy i)

end PolycyclicRecognition

end

end OAI
