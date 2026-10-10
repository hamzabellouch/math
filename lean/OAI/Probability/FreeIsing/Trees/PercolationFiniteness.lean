import OAI.Probability.FreeIsing.Trees.OpenClusterGeometry
import OAI.Probability.FreeIsing.Trees.PercolationSurvival

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Problem367
namespace SubcriticalClusters

def openCluster {d : ℕ} (p : ℝ) (U : TreeVertex d → ℝ)
    (o : TreeVertex d) : Set (TreeVertex d) :=
  {v | Relation.ReflTransGen (OpenCluster.openAdj (fun w => U w ≤ p)) o v}

lemma reachable_iff_common_downwardOpen {d : ℕ} (P : TreeVertex d → Prop)
    (u v : TreeVertex d) :
    Relation.ReflTransGen (OpenCluster.openAdj P) u v ↔
      ∃ r, OpenCluster.downwardOpen P r u ∧ OpenCluster.downwardOpen P r v := by
  constructor
  · intro huv
    obtain ⟨r, _, hsub⟩ := OpenCluster.reachable_subset_downwardOpen P u
    exact ⟨r, hsub Relation.ReflTransGen.refl, hsub huv⟩
  · rintro ⟨r, hru, hrv⟩
    exact (OpenCluster.reachable_symm (OpenCluster.reachable_of_downwardOpen hru)).trans
      (OpenCluster.reachable_of_downwardOpen hrv)

lemma measurableSet_mem_openCluster {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → TreeVertex d → ℝ} (hU : ∀ v, Measurable (fun ω => U ω v))
    (p : ℝ) (o v : TreeVertex d) :
    MeasurableSet {ω | v ∈ openCluster p (U ω) o} := by
  have heq : {ω | v ∈ openCluster p (U ω) o} =
      ⋃ r : TreeVertex d,
        {ω | DownwardOpen p (U ω) r o} ∩ {ω | DownwardOpen p (U ω) r v} := by
    ext ω
    simp only [openCluster, Set.mem_ofPred_eq, reachable_iff_common_downwardOpen,
      Set.mem_iUnion, Set.mem_inter_iff, DownwardOpen, OpenCluster.downwardOpen]
  rw [heq]
  exact MeasurableSet.iUnion fun r => (measurableSet_downwardOpen hU p r o).inter
    (measurableSet_downwardOpen hU p r v)

theorem ae_all_finite_openClusters {d : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : (d - 1 : ℕ) * p < 1) :
    ∀ᵐ U ∂labelMeasure d, ∀ o : TreeVertex d, (openCluster p U o).Finite := by
  filter_upwards [ae_all_finite_downwardOpen hp0 hp1 hp] with U hU
  intro o
  exact OpenCluster.finite_reachable_of_finite_downwardOpen (fun w => U w ≤ p) hU o

theorem ae_all_finite_openClusters_of_cylinder_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → TreeVertex d → ℝ) {p : ℝ}
    (hp : (d - 1 : ℕ) * p < 1) (hp0 : 0 ≤ p)
    (hCylinder : ∀ S : Finset (TreeVertex d), (∀ v ∈ S, v.1 ≠ []) →
      μ {ω | ∀ v ∈ S, U ω v ≤ p} ≤ (ENNReal.ofReal p) ^ S.card) :
    ∀ᵐ ω ∂μ, ∀ o : TreeVertex d, (openCluster p (U ω) o).Finite := by
  filter_upwards [ae_all_finite_downwardOpen_of_cylinder_bound μ U hp hp0 hCylinder]
    with ω hω
  intro o
  exact OpenCluster.finite_reachable_of_finite_downwardOpen
    (fun w => U ω w ≤ p) hω o

theorem ae_all_finite_openClusters_of_survival_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → TreeVertex d → ℝ) (p : ℝ)
    (q : TreeVertex d → ℕ → ℝ≥0∞)
    (hbound : ∀ r n, μ (survivalEvent U p r n) ≤ q r n)
    (hlim : ∀ r, Tendsto (q r) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ o : TreeVertex d, (openCluster p (U ω) o).Finite := by
  have hfinite : ∀ᵐ ω ∂μ, ∀ r : TreeVertex d,
      {v | DownwardOpen p (U ω) r v}.Finite :=
    ae_all_iff.2 (fun r =>
      ae_finite_downwardOpen_of_survival_bound μ U p r (q r) (hbound r) (hlim r))
  filter_upwards [hfinite] with ω hω
  intro o
  exact OpenCluster.finite_reachable_of_finite_downwardOpen
    (fun w => U ω w ≤ p) hω o

theorem ae_all_finite_reachable_of_incoming_cylinder_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R : Ω → TreeVertex d → TreeVertex d → Prop) (p : ℝ≥0∞)
    (hp : ((d - 1 : ℕ) : ℝ≥0∞) * p < 1) (hptop : p ≠ ∞)
    (hsub : ∀ᵐ ω ∂μ, ∀ u v, R ω u v → treeAdj u v)
    (hsymm : ∀ᵐ ω ∂μ, ∀ u v, R ω u v → R ω v u)
    (hCylinder : ∀ S : Finset (TreeVertex d), (∀ v ∈ S, v.1 ≠ []) →
      μ {ω | ∀ v ∈ S, R ω (parentVertex v) v} ≤ p ^ S.card) :
    ∀ᵐ ω ∂μ, ∀ o : TreeVertex d,
      {v | Relation.ReflTransGen (R ω) o v}.Finite := by
  have hfinite : ∀ᵐ ω ∂μ, ∀ r : TreeVertex d,
      {v | OpenCluster.downwardOpen (fun w => R ω (parentVertex w) w) r v}.Finite := by
    apply ae_all_iff.2
    intro r
    apply ae_finite_of_depth_bound μ
      (fun ω v => OpenCluster.downwardOpen (fun w => R ω (parentVertex w) w) r v)
      r.1.length p hp hptop (fun _ _ h => h.1.length_le)
    intro v
    calc
      μ {ω | OpenCluster.downwardOpen (fun w => R ω (parentVertex w) w) r v} ≤
          μ {ω | ∀ w ∈ pathCoordinates r.1.length v, R ω (parentVertex w) w} := by
        apply measure_mono
        intro ω hω w hw
        obtain ⟨k, hk, hkv, rfl⟩ := mem_pathCoordinates.mp hw
        exact hω.2 k hk hkv
      _ ≤ p ^ (pathCoordinates r.1.length v).card :=
        hCylinder _ (fun _ hw => pathCoordinates_ne_nil hw)
      _ = p ^ (v.1.length - r.1.length) := by rw [card_pathCoordinates]
  filter_upwards [hfinite, hsub, hsymm] with ω hω hsω hsymω
  exact OpenCluster.finite_reachable_of_finite_incoming (R ω) hsω hsymω hω

theorem finite_downwardOpen_of_nonroot {d : ℕ} (p : ℝ)
    (U : TreeVertex d → ℝ)
    (hfinite : ∀ r : TreeVertex d, r.1 ≠ [] → {v | DownwardOpen p U r v}.Finite)
    (r : TreeVertex d) : {v | DownwardOpen p U r v}.Finite := by
  classical
  by_cases hr : r.1 = []
  · have hUnion : (⋃ w ∈ {w : TreeVertex d | w.1.length = 1},
        {v | DownwardOpen p U w v}).Finite := by
      apply (finite_treeShell d 1).biUnion
      intro w hw
      apply hfinite w
      intro hnil
      change w.1.length = 1 at hw
      simp [hnil] at hw
    apply (hUnion.insert r).subset
    intro v hv
    by_cases hnil : v.1 = []
    · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext (hnil.trans hr.symm)))
    · have hlen : 1 ≤ v.1.length := List.length_pos_iff.mpr hnil
      let w := ConnectedHull.takeVertex v 1
      have hwlen : w.1.length = 1 := ConnectedHull.prefix_length_eq v hlen
      apply Set.mem_insert_of_mem
      apply Set.mem_iUnion.mpr ⟨w, ?_⟩
      apply Set.mem_iUnion.mpr ⟨hwlen, ?_⟩
      refine ⟨List.take_prefix _ _, ?_⟩
      intro k hwk hkv
      apply hv.2 k _ hkv
      simp only [hr, List.length_nil]
      omega
  · exact hfinite r hr

theorem ae_all_finite_openClusters_of_nonroot_survival_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → TreeVertex d → ℝ) (p : ℝ)
    (q : TreeVertex d → ℕ → ℝ≥0∞)
    (hbound : ∀ r : TreeVertex d, r.1 ≠ [] →
      ∀ n, μ (survivalEvent U p r n) ≤ q r n)
    (hlim : ∀ r : TreeVertex d, r.1 ≠ [] → Tendsto (q r) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ o : TreeVertex d, (openCluster p (U ω) o).Finite := by
  have hfinite : ∀ᵐ ω ∂μ, ∀ r : TreeVertex d, r.1 ≠ [] →
      {v | DownwardOpen p (U ω) r v}.Finite := by
    apply ae_all_iff.2
    intro r
    apply ae_all_iff.2
    intro hr
    exact ae_finite_downwardOpen_of_survival_bound μ U p r (q r)
      (hbound r hr) (hlim r hr)
  filter_upwards [hfinite] with ω hω
  intro o
  exact OpenCluster.finite_reachable_of_finite_downwardOpen (fun w => U ω w ≤ p)
    (finite_downwardOpen_of_nonroot p (U ω) hω) o

end SubcriticalClusters
end Problem367

end

end OAI
