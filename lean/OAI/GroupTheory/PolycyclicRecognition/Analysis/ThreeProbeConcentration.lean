import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedAffineProbeSelection

namespace OAI

/-! # Joint concentration of the three actual probe chains -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Concentration is transitive through the measured anchor profile. -/
theorem bad_distance_triangle_tendsto_zero
    {X S : Type*} [MeasurableSpace X] [PseudoMetricSpace S]
    (μ : ℕ → Measure X) (f g h : ℕ → X → S)
    (hfg : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    (hgh : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {x | ε ≤ dist (g n x) (h n x)}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => μ n {x | ε ≤ dist (f n x) (h n x)}) atTop (𝓝 0) := by
  have hb (n : ℕ) : μ n {x | ε ≤ dist (f n x) (h n x)} ≤
      μ n {x | ε / 2 ≤ dist (f n x) (g n x)} +
        μ n {x | ε / 2 ≤ dist (g n x) (h n x)} := by
    apply (measure_mono (fun x hx => ?_)).trans (measure_union_le _ _)
    by_cases hf : ε / 2 ≤ dist (f n x) (g n x)
    · exact Or.inl hf
    · right
      have hh := dist_triangle (f n x) (g n x) (h n x)
      have hx' : ε ≤ dist (f n x) (h n x) := hx
      change ε / 2 ≤ dist (g n x) (h n x)
      linarith [lt_of_not_ge hf]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds _ (fun _ => zero_le) hb
  simpa only [zero_add] using (hfg (ε / 2) (half_pos hε)).add (hgh (ε / 2) (half_pos hε))

/-- The first chain is based at the original sheet, the second at its
neighbor, and the third at the selected endpoint of the second. One compact
set of probes and one original sample work for every prefix of all three. -/
theorem exists_supported_three_affine_probe_sequence
    {X Z W V : Type*} [Nonempty X] [MeasurableSpace X]
    [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [AddCommGroup V] [Module ℝ V]
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
    {N₀ N₁ N₂ : ℕ}
    (chain₀ : ∀ n, X × Y n → Fin (N₀ + 1) → C(Z, W))
    (chain₁ : ∀ n, X × Y n → Fin (N₁ + 1) → C(Z, W))
    (chain₂ : ∀ n, X × Y n → Fin (N₂ + 1) → C(Z, W))
    (hm₀ : ∀ n j, Measurable (fun p => chain₀ n p j))
    (hm₁ : ∀ n j, Measurable (fun p => chain₁ n p j))
    (hm₂ : ∀ n j, Measurable (fun p => chain₂ n p j))
    (hstart : ∀ n p, chain₂ n p 0 = chain₁ n p (Fin.last N₁))
    (hc₀ : ∀ j ε, 0 < ε → ∀ y : ∀ n, Y n,
      Tendsto (fun n => (μ : Measure X)
        {x | ε ≤ dist (chain₀ n (x, y n) j) (profile n x).1}) atTop (𝓝 0))
    (hc₁ : ∀ j ε, 0 < ε → ∀ y : ∀ n, Y n,
      Tendsto (fun n => (μ : Measure X)
        {x | ε ≤ dist (chain₁ n (x, y n) j) (profile n x).2}) atTop (𝓝 0))
    (hc₂ : ∀ j ε, 0 < ε → ∀ y : ∀ n, Y n,
      Tendsto (fun n => (μ : Measure X)
        {x | ε ≤ dist (chain₂ n (x, y n) j) (chain₂ n (x, y n) 0)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop, x n ∈ carrying ∧
        (∀ s z, ‖(if s then (profile n (x n)).2 else (profile n (x n)).1) z -
          (A (q z) + b s)‖ < ε n) ∧
        (∀ y ∈ K n, ∀ j z, ‖chain₀ n (x n, y) j z - (A (q z) + b false)‖ < 2 * ε n) ∧
        (∀ y ∈ K n, ∀ j z, ‖chain₁ n (x n, y) j z - (A (q z) + b true)‖ < 2 * ε n) ∧
        ∀ y ∈ K n, ∀ j z, ‖chain₂ n (x n, y) j z - (A (q z) + b true)‖ < 2 * ε n := by
  let C := Fin (N₀ + 1) ⊕ (Fin (N₁ + 1) ⊕ Fin (N₂ + 1))
  let chain : ∀ n, X × Y n → C → C(Z, W) := fun n p =>
    Sum.elim (chain₀ n p) (Sum.elim (chain₁ n p) (chain₂ n p))
  let sheet : C → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have hm (n : ℕ) (j : C) : Measurable (fun p => dist (chain n p j)
      (if sheet j then (profile n p.1).2 else (profile n p.1).1)) := by
    rcases j with j | j | j
    · exact continuous_dist.measurable.comp
        ((hm₀ n j).prodMk (((hp n).fst).comp measurable_fst))
    · exact continuous_dist.measurable.comp
        ((hm₁ n j).prodMk (((hp n).snd).comp measurable_fst))
    · exact continuous_dist.measurable.comp
        ((hm₂ n j).prodMk (((hp n).snd).comp measurable_fst))
  have hc (j : C) (ε : ℝ) (hε : 0 < ε) (y : ∀ n, Y n) :
      Tendsto (fun n => (μ : Measure X) {x | ε ≤ dist (chain n (x, y n) j)
        (if sheet j then (profile n x).2 else (profile n x).1)}) atTop (𝓝 0) := by
    rcases j with j | j | j
    · exact hc₀ j ε hε y
    · exact hc₁ j ε hε y
    · apply bad_distance_triangle_tendsto_zero (fun _ => (μ : Measure X))
        (fun n x => chain₂ n (x, y n) j)
        (fun n x => chain₁ n (x, y n) (Fin.last N₁))
        (fun n x => (profile n x).2) _ (fun ε hε => hc₁ _ ε hε y) ε hε
      intro δ hδ
      simpa only [hstart] using hc₂ j δ hδ y
  obtain ⟨ε, x, K, hεpos, hε, hK, he⟩ := exists_supported_affine_probe_sequence
    μ ν carrying hcarrying hfull profile hp limitLaw hlim hf q A b haffine chain sheet hm hc
  refine ⟨ε, x, K, hεpos, hε, hK, he.mono ?_⟩
  intro n hn
  exact ⟨hn.1, hn.2.1,
    fun y hy j z => hn.2.2 y hy (Sum.inl j) z,
    fun y hy j z => hn.2.2 y hy (Sum.inr (Sum.inl j)) z,
    fun y hy j z => hn.2.2 y hy (Sum.inr (Sum.inr j)) z⟩

end PolycyclicRecognition

end

end OAI
