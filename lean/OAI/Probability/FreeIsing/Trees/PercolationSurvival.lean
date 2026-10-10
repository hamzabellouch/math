import OAI.Probability.FreeIsing.Trees.SubcriticalClusters

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Problem367
namespace SubcriticalClusters

lemma takeVertex_takeVertex {d : ℕ} (v : TreeVertex d) {i j : ℕ}
    (hij : i ≤ j) :
    ConnectedHull.takeVertex (ConnectedHull.takeVertex v j) i =
      ConnectedHull.takeVertex v i := by
  apply Subtype.ext
  simp only [ConnectedHull.takeVertex, List.take_take, Nat.min_eq_left hij]

lemma DownwardOpen.take {d : ℕ} {p : ℝ} {U : TreeVertex d → ℝ}
    {r v : TreeVertex d} (h : DownwardOpen p U r v)
    {n : ℕ} (hrn : r.1.length ≤ n) (hnv : n ≤ v.1.length) :
    DownwardOpen p U r (ConnectedHull.takeVertex v n) := by
  refine ⟨?_, ?_⟩
  · change r.1 <+: v.1.take n
    exact List.prefix_take_iff.mpr ⟨h.1, hrn⟩
  · intro k hrk hkn
    have hkn' : k ≤ n := by
      simpa only [ConnectedHull.prefix_length_eq v hnv] using hkn
    rw [takeVertex_takeVertex v hkn']
    exact h.2 k hrk (hkn'.trans hnv)

def survivalEvent {d : ℕ} {Ω : Type*} (U : Ω → TreeVertex d → ℝ)
    (p : ℝ) (r : TreeVertex d) (n : ℕ) : Set Ω :=
  {ω | ∃ v : TreeVertex d, v.1.length = r.1.length + n ∧ DownwardOpen p (U ω) r v}

lemma survivalEvent_antitone {d : ℕ} {Ω : Type*}
    (U : Ω → TreeVertex d → ℝ) (p : ℝ) (r : TreeVertex d) :
    Antitone (survivalEvent U p r) := by
  intro i j hij ω hω
  obtain ⟨v, hv, hopen⟩ := hω
  have hle : r.1.length + i ≤ v.1.length := by omega
  refine ⟨ConnectedHull.takeVertex v (r.1.length + i),
    ConnectedHull.prefix_length_eq v hle, ?_⟩
  exact hopen.take (by omega) hle

lemma measurableSet_survivalEvent {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → TreeVertex d → ℝ} (hU : ∀ v, Measurable (fun ω => U ω v))
    (p : ℝ) (r : TreeVertex d) (n : ℕ) :
    MeasurableSet (survivalEvent U p r n) := by
  simp only [survivalEvent, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro v
  by_cases hv : v.1.length = r.1.length + n
  · simpa only [hv, true_and] using measurableSet_downwardOpen hU p r v
  · simp only [hv, false_and, Set.ofPred_false, MeasurableSet.empty]

lemma finite_downwardOpen_iff {d : ℕ} (p : ℝ) (U : TreeVertex d → ℝ)
    (r : TreeVertex d) :
    {v | DownwardOpen p U r v}.Finite ↔
      ∃ n : ℕ, ¬ ∃ v : TreeVertex d,
        v.1.length = r.1.length + n ∧ DownwardOpen p U r v := by
  classical
  constructor
  · intro hfin
    obtain ⟨M, hM⟩ := (hfin.image (fun v : TreeVertex d => v.1.length)).bddAbove
    refine ⟨M + 1, ?_⟩
    rintro ⟨v, hv, hopen⟩
    have hle : v.1.length ≤ M := hM (Set.mem_image_of_mem _ hopen)
    omega
  · rintro ⟨n, hn⟩
    apply (finite_treeBall d (r.1.length + n)).subset
    intro v hv
    show v.1.length ≤ r.1.length + n
    by_contra hlen
    have hle : r.1.length + n ≤ v.1.length := by omega
    apply hn
    exact ⟨ConnectedHull.takeVertex v (r.1.length + n),
      ConnectedHull.prefix_length_eq v hle, hv.take (by omega) hle⟩

lemma infinite_downwardOpen_iff_survives {d : ℕ} {Ω : Type*}
    (U : Ω → TreeVertex d → ℝ) (p : ℝ) (r : TreeVertex d) (ω : Ω) :
    {v | DownwardOpen p (U ω) r v}.Infinite ↔
      ∀ n : ℕ, ω ∈ survivalEvent U p r n := by
  rw [Set.Infinite, finite_downwardOpen_iff]
  simp only [not_exists, not_forall, not_not, survivalEvent, Set.mem_ofPred_eq]

theorem ae_finite_downwardOpen_of_survival_tendsto_zero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → TreeVertex d → ℝ) (p : ℝ) (r : TreeVertex d)
    (hlim : Tendsto (fun n => μ (survivalEvent U p r n)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, {v | DownwardOpen p (U ω) r v}.Finite := by
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply ge_of_tendsto' hlim
  intro n
  apply measure_mono
  intro ω hω
  exact (infinite_downwardOpen_iff_survives U p r ω).1 hω n

theorem ae_finite_downwardOpen_of_survival_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → TreeVertex d → ℝ) (p : ℝ) (r : TreeVertex d)
    (q : ℕ → ℝ≥0∞) (hbound : ∀ n, μ (survivalEvent U p r n) ≤ q n)
    (hlim : Tendsto q atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, {v | DownwardOpen p (U ω) r v}.Finite := by
  apply ae_finite_downwardOpen_of_survival_tendsto_zero μ U p r
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

end SubcriticalClusters
end Problem367

end

end OAI
