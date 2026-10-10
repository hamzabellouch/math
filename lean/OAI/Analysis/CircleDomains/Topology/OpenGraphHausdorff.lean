import OAI.Analysis.CircleDomains.Uniformization.UniformGraphHausdorff
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Remove the fixed interior margin by a compact exhaustion of the open
energy neighborhood. The resulting estimate applies to the entire set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_graph_hausdorff_le_open {A O : Set GraphSpace} (hO : IsOpen O) (hAO : A ⊆ O)
    (μ : Measure GraphSpace) (K : ℝ≥0∞)
    (hlocal : ∀ s, 0 < s → ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s))) :
    (μH[2] : Measure GraphSpace) A ≤ 4096*K*μ O := by
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let B : ℕ → Set GraphSpace := fun n => Subtype.val '' compactCovering O n
  have hB (n : ℕ) : IsCompact (B n) :=
    (isCompact_compactCovering O n).image continuous_subtype_val
  have hBO (n : ℕ) : B n ⊆ O := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hmB : Monotone B := fun _ _ h => image_mono (compactCovering_subset O h)
  have hcap (n : ℕ) : (μH[2] : Measure GraphSpace) (A ∩ B n) ≤ 4096*K*μ O := by
    obtain ⟨ε,hε,hεO⟩ := (hB n).exists_cthickening_subset_open hO (hBO n)
    apply uniform_graph_hausdorff_le μ K (show 0 < ε/4 by positivity)
    · intro x hx
      have hh : closedBall x (4*(ε/4)) ⊆ cthickening ε (B n) := by
        simpa only [mul_div_cancel₀ _ (by norm_num : (4:ℝ) ≠ 0)] using
          (closedBall_subset_cthickening hx.2 ε)
      exact hh.trans hεO
    · intro s hs _ x hx
      obtain ⟨T,hT,hD,hC⟩ := hlocal s hs x hx.1
      exact ⟨T,(inter_subset_inter_left _ inter_subset_left).trans hT,hD,hC⟩
  have hcover : (⋃ n, A ∩ B n) = A := by
    apply Subset.antisymm (iUnion_subset fun _ => inter_subset_left)
    intro x hx
    obtain ⟨n,hn⟩ := exists_mem_compactCovering (⟨x,hAO hx⟩ : O)
    exact mem_iUnion.mpr ⟨n,hx,⟨⟨x,hAO hx⟩,hn,rfl⟩⟩
  have hm : Monotone (fun n => A ∩ B n) := fun _ _ h _ hx => ⟨hx.1,hmB h hx.2⟩
  rw [← hcover,hm.measure_iUnion]
  exact iSup_le hcap

end CircleDomainRigidity

end

end OAI
