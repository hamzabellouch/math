import OAI.Analysis.Mahler.RegularSublevel
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

/-- A bounded open portion of a genuine regular-level chart, inside U. -/
structure RegularBoundaryPatch (d : ℕ) (U : Set (Fin d → ℝ))
    (g : (Fin d → ℝ) → ℝ) where
  coordinate : Fin d
  chart : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)
  domain : Set (Fin d → ℝ)
  open_domain : IsOpen domain
  bounded_domain : Bornology.IsBounded domain
  domain_source : domain ⊆ chart.source
  domain_U : domain ⊆ U
  chart_eq : ∀ z, chart z = levelCoordinates g coordinate z
  smooth_chart : ContDiffOn ℝ 2 chart chart.source
  smooth_inverse : ContDiffOn ℝ 2 chart.symm chart.target

 theorem exists_regularBoundaryPatch {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hg : ContDiffAt ℝ 2 g x) (hreg : fderiv ℝ g x ≠ 0) :
    ∃ p : RegularBoundaryPatch d U g, x ∈ p.domain := by
  obtain ⟨k, e, he, heq, hs, hi⟩ := exists_regular_level_chart hg hreg
  refine ⟨⟨k, e, e.source ∩ U ∩ Metric.ball x 1,
    (e.open_source.inter hU).inter Metric.isOpen_ball,
    (Metric.isBounded_ball).subset inter_subset_right,
    fun z hz => hz.1.1, fun z hz => hz.1.2, heq, hs, hi⟩, ?_⟩
  exact ⟨⟨he, hx⟩, Metric.mem_ball_self (by norm_num)⟩

/-- A finite cover extracted from actual derivative-based charts. -/
structure RegularBoundaryAtlas (d : ℕ) (U : Set (Fin d → ℝ))
    (g : (Fin d → ℝ) → ℝ) (K : Set (Fin d → ℝ)) where
  Index : Type
  finite : Fintype Index
  patch : Index → RegularBoundaryPatch d U g
  covers : K ⊆ ⋃ i, (patch i).domain

attribute [instance] RegularBoundaryAtlas.finite

 theorem exists_regularBoundaryAtlas {d : ℕ} {U K : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ∀ x ∈ K, ContDiffAt ℝ 2 g x)
    (hreg : ∀ x ∈ K, fderiv ℝ g x ≠ 0) :
    Nonempty (RegularBoundaryAtlas d U g K) := by
  classical
  have hp (x : K) := exists_regularBoundaryPatch hU (hKU x.property)
    (hg x x.property) (hreg x x.property)
  choose p hp using hp
  have hcover : K ⊆ ⋃ x : K, (p x).domain := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hp ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => (p x).domain)
    (fun x => (p x).open_domain) hcover
  refine ⟨⟨t, inferInstance, fun i => p i.val, ?_⟩⟩
  intro x hx
  obtain ⟨i, hit, hi⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion.mpr ⟨⟨i, hit⟩, hi⟩

/-- The chart identifies the actual sublevel with the lower coordinate half-space. -/
theorem RegularBoundaryPatch.sublevel_iff {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} (p : RegularBoundaryPatch d U g) {R : ℝ}
    {x : Fin d → ℝ} (hx : x ∈ p.domain) :
    x ∈ regularSublevel U g R ↔ p.chart x p.coordinate < R := by
  rw [p.chart_eq]
  simp [levelCoordinates, regularSublevel, p.domain_U hx]

 theorem exists_sublevelBoundaryAtlas {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0) :
    Nonempty (RegularBoundaryAtlas d U g (frontier (regularSublevel U g R))) := by
  rw [frontier_regularSublevel hU hg.continuousOn hcl hreg]
  exact exists_regularBoundaryAtlas hU
    (isCompact_regularLevel hU hg.continuousOn hc hcl hreg) inter_subset_left
    (fun x hx => hg.contDiffAt (hU.mem_nhds hx.1)) (fun x hx => hreg x hx.1 hx.2)

end MahlerStokes

end

end OAI
