import OAI.Analysis.Mahler.RegularBoundaryAtlas
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace OAI

noncomputable section
open Set Filter
open scoped Topology Manifold
namespace MahlerStokes

/-- An actual smooth partition with compact supports in a given finite bounded
open cover, equal to one on a neighborhood of the compact set. -/
theorem exists_compact_smooth_partition {d : ℕ} {ι : Type} [Fintype ι]
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (V : ι → Set (Fin d → ℝ))
    (hVo : ∀ i, IsOpen (V i)) (hVb : ∀ i, Bornology.IsBounded (V i))
    (hcover : K ⊆ ⋃ i, V i) :
    ∃ (W : Set (Fin d → ℝ))
      (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) (closure W)),
      IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧
      ρ.IsSubordinate V ∧ (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) := by
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK (isOpen_iUnion hVo) hcover
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Fin d → ℝ) isClosed_closure V hVo hWV
  refine ⟨W, ρ, hWo, hKW, hWc, hρ, ?_, ?_⟩
  · intro i
    exact Metric.isCompact_of_isClosed_isBounded isClosed_closure ((hVb i).subset (hρ i))
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (subset_closure hx)

/-- The boundary atlas has an actual finite smooth subordinate partition,
with compact supports and sum one on a boundary neighborhood. -/
theorem RegularBoundaryAtlas.exists_partition {d : ℕ} {U K : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} (a : RegularBoundaryAtlas d U g K) (hK : IsCompact K) :
    ∃ (W : Set (Fin d → ℝ))
      (ρ : SmoothPartitionOfUnity a.Index 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) (closure W)),
      IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧
      (∀ i, tsupport (ρ i) ⊆ (a.patch i).domain) ∧
      (∀ i, HasCompactSupport (ρ i)) ∧ (∀ x ∈ W, ∑ i, ρ i x = 1) :=
  exists_compact_smooth_partition hK (fun i => (a.patch i).domain)
    (fun i => (a.patch i).open_domain) (fun i => (a.patch i).bounded_domain) a.covers

/-- Adjoin the actual sublevel as the interior patch. This finite cover covers
the whole closure, so derivative cancellation can be used throughout D_R. -/
def sublevelPatchDomain {d : ℕ} {U : Set (Fin d → ℝ)} {g : (Fin d → ℝ) → ℝ}
    {R : ℝ} (a : RegularBoundaryAtlas d U g (frontier (regularSublevel U g R))) :
    Option a.Index → Set (Fin d → ℝ)
  | none => regularSublevel U g R
  | some i => (a.patch i).domain

 theorem sublevelPatchDomain_covers {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (a : RegularBoundaryAtlas d U g (frontier (regularSublevel U g R))) :
    closure (regularSublevel U g R) ⊆ ⋃ i, sublevelPatchDomain a i := by
  intro x hx
  by_cases hi : x ∈ regularSublevel U g R
  · exact mem_iUnion.mpr ⟨none, hi⟩
  · have hf : x ∈ frontier (regularSublevel U g R) := by
      rw [(isOpen_regularSublevel hU hg).frontier_eq]
      exact ⟨hx, hi⟩
    obtain ⟨i, hix⟩ := mem_iUnion.mp (a.covers hf)
    exact mem_iUnion.mpr ⟨some i, hix⟩

 theorem exists_sublevel_partition {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (a : RegularBoundaryAtlas d U g (frontier (regularSublevel U g R))) :
    ∃ (W : Set (Fin d → ℝ))
      (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) (closure W)),
      IsOpen W ∧ closure (regularSublevel U g R) ⊆ W ∧ IsCompact (closure W) ∧
      ρ.IsSubordinate (sublevelPatchDomain a) ∧ (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) := by
  apply exists_compact_smooth_partition hc (sublevelPatchDomain a)
  · intro i
    cases i with
    | none => exact isOpen_regularSublevel hU hg
    | some i => exact (a.patch i).open_domain
  · intro i
    cases i with
    | none => exact hc.isBounded.subset subset_closure
    | some i => exact (a.patch i).bounded_domain
  · exact sublevelPatchDomain_covers hU hg a

end MahlerStokes

end

end OAI
