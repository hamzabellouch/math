import Mathlib

namespace OAI

noncomputable section
open Set Filter Function Metric MeasureTheory
open scoped Topology ENNReal
open Set Filter Function Metric Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem compact_disjoint_smooth_cutoffs (K V : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hd : Pairwise (Disjoint on K))
    (hV : ∀ i, IsOpen (V i)) (hKV : ∀ i, K i ⊆ V i) :
    ∃ χ : ι → E → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ V i ∧ (∀ᶠ x in 𝓝ˢ (K i), χ i x = 1) ∧
        ∀ x, χ i x ∈ Icc 0 1) ∧ Pairwise (Disjoint on fun i => tsupport (χ i)) := by
  have hN : Pairwise (Disjoint on fun i => 𝓝ˢ (K i)) := by
    intro i j hij
    change Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))
    rw [(hK i).disjoint_nhdsSet_left]
    intro x hx
    rw [(hK j).disjoint_nhdsSet_right]
    intro y hy
    exact disjoint_nhds_nhds.mpr (fun hxy => (hd hij).notMem_of_mem_left hx (hxy ▸ hy))
  obtain ⟨O,hO,hdO⟩ := hN.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (K i))
  have hex (i : ι) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ V i ∩ O i ∧ (∀ᶠ x in 𝓝ˢ (K i), χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
    obtain ⟨B,hB,hKB,hBc⟩ := exists_isOpen_superset_and_isCompact_closure (hK i)
    have hNV : V i ∩ O i ∩ B ∈ 𝓝ˢ (K i) :=
      ((hV i).inter (hO i).1 |>.inter hB).mem_nhdsSet.mpr
        (fun x hx => ⟨⟨hKV i hx,(hO i).2 hx⟩,hKB hx⟩)
    obtain ⟨W,hW,hKW,hWsub⟩ := (hK i).exists_isOpen_closure_subset hNV
    obtain ⟨f,hf1,hf0,hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ,E)) (n := ⊤) (hK i).isClosed (t := W) (by simpa only [hW.interior_eq] using hKW)
    have hfs : tsupport (f : E → ℝ) ⊆ closure W := by
      apply closure_mono
      intro x hx
      by_contra hh
      exact hx (hf0 x hh)
    refine ⟨f,contMDiff_iff_contDiff.mp f.contMDiff,?_,?_,hf1,hf⟩
    · exact hBc.of_isClosed_subset (isClosed_tsupport _)
        (hfs.trans (hWsub.trans (fun x hx => subset_closure hx.2)))
    · exact hfs.trans (hWsub.trans (fun x hx => hx.1))
  choose χ hχ using hex
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_left,
    (hχ i).2.2.2.1,(hχ i).2.2.2.2⟩,?_⟩
  intro i j hij
  exact (hdO hij).mono ((hχ i).2.2.1.trans inter_subset_right)
    ((hχ j).2.2.1.trans inter_subset_right)
end YauCounterexamples

end

end OAI
