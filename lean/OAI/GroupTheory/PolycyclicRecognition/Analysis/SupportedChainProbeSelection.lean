import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbeSequence
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # A single supported base sample with all prefix comparisons -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

/-- Finitely many measurable prefix comparisons can be selected together
with a supported pair of profiles. The retained compact probe set has
quarter mass, independent of the probability of the support neighborhood. -/
theorem exists_supported_chain_probe_sequence
    {X S C : Type*} [Nonempty X] [MeasurableSpace X]
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    [HasOuterApproxClosed (S × S)] [Fintype C]
    {Y : ℕ → Type*} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    (carrying : Set X) (hcarrying : MeasurableSet carrying)
    (hfull : (μ : Measure X) carryingᶜ = 0)
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → S × S) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure (S × S))
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (profile n)) atTop (𝓝 limitLaw))
    {f : S × S} (hf : f ∈ (limitLaw : Measure (S × S)).support)
    (chain : ∀ n, X × Y n → C → S) (sheet : C → Bool)
    (hm : ∀ n i, Measurable (fun q : X × Y n =>
      dist (chain n q i) (if sheet i then (profile n q.1).2 else (profile n q.1).1)))
    (hdet : ∀ i (ε : ℝ), 0 < ε → ∀ y : ∀ n, Y n,
      Tendsto (fun n => (μ : Measure X)
        {x | ε ≤ dist (chain n (x, y n) i)
          (if sheet i then (profile n x).2 else (profile n x).1)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop,
        x n ∈ carrying ∧ dist (profile n (x n)) f < ε n ∧
        ∀ y ∈ K n, ∀ i, dist (chain n (x n, y) i)
          (if sheet i then f.2 else f.1) < 2 * ε n := by
  classical
  let tol := fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)
  have htol (j : ℕ) : 0 < tol j := by dsimp [tol]; positivity
  let comparisons := fun n j => ⋃ i : C, {q : X × Y n | tol j ≤
    dist (chain n q i) (if sheet i then (profile n q.1).2 else (profile n q.1).1)}
  let bad := fun n j => Prod.fst ⁻¹' carryingᶜ ∪ comparisons n j
  have hcomparisons (n j) : MeasurableSet (comparisons n j) :=
    MeasurableSet.iUnion (fun i => (isClosed_le continuous_const continuous_id).measurableSet.preimage
      (hm n i))
  have hbad (n j) : MeasurableSet (bad n j) :=
    (measurable_fst hcarrying.compl).union (hcomparisons n j)
  have hdet' (j : ℕ) (y : ∀ n, Y n) :
      Tendsto (fun n => (μ : Measure X) ((fun x => (x, y n)) ⁻¹' bad n j))
        atTop (𝓝 0) := by
    have hh := finite_bad_union_tendsto_zero (fun _ => (μ : Measure X))
      (fun n i => {x | tol j ≤ dist (chain n (x, y n) i)
        (if sheet i then (profile n x).2 else (profile n x).1)})
      (fun i => hdet i (tol j) (htol j) y)
    have hzero : ∀ n, (μ : Measure X) ((fun x => (x, y n)) ⁻¹' bad n j) =
        (μ : Measure X) (⋃ i : C, {x | tol j ≤ dist (chain n (x, y n) i)
          (if sheet i then (profile n x).2 else (profile n x).1)}) := by
      intro n
      simp only [bad, comparisons, preimage_union, preimage_iUnion, preimage_ofPred_eq]
      change (μ : Measure X) (carryingᶜ ∪ _) = _
      apply le_antisymm
      · exact (measure_union_le _ _).trans (by rw [hfull, zero_add])
      · exact measure_mono subset_union_right
    simpa only [hzero] using hh
  obtain ⟨k, hk, hselect⟩ := exists_compact_probes_from_supported_profiles
    μ ν profile hp limitLaw hlim hf (fun j => ball f (tol j))
    (fun _ => isOpen_ball) (fun j => mem_ball_self (htol j)) bad hbad hdet'
  let ε := fun n => tol (k n)
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  obtain ⟨x, K, hK, hgood⟩ := choose_compact_good_probe_sequence ν
    (fun n x K => dist (profile n x) f < ε n ∧ K ⊆ {y | (x, y) ∉ bad n (k n)})
    (hselect.mono (by
      intro n hn
      obtain ⟨x, hx, K, hc, hs, hm⟩ := hn
      exact ⟨x, K, hc, ⟨hx, hs⟩, hm⟩))
  refine ⟨ε, x, K, fun n => htol (k n), hε, hK, ?_⟩
  filter_upwards [hgood] with n hn
  have hnonempty : (K n).Nonempty := nonempty_of_measure_ne_zero
    (ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1 / 4).trans (hK n).2.2))
  have hcar : x n ∈ carrying := by
    obtain ⟨y, hy⟩ := hnonempty
    by_contra hx
    exact hn.2 hy (Or.inl hx)
  refine ⟨hcar, hn.1, ?_⟩
  intro y hy i
  have hb : dist (chain n (x n, y) i)
      (if sheet i then (profile n (x n)).2 else (profile n (x n)).1) < ε n := by
    apply lt_of_not_ge
    intro hge
    exact hn.2 hy (Or.inr (mem_iUnion.mpr ⟨i, hge⟩))
  have hp' : dist (if sheet i then (profile n (x n)).2 else (profile n (x n)).1)
      (if sheet i then f.2 else f.1) < ε n := by
    split_ifs
    · exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hn.1
    · exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hn.1
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end PolycyclicRecognition

end

end OAI
