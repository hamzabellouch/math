import OAI.Analysis.CircleDomains.Topology.OneDimensionalOpenImage
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.OpenPartialHomeomorph.Composition

namespace OAI

/-! Explicit local real charts of the circle and the open-image theorem
for circle embeddings into a real one-manifold. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_real_circle_chart (z : Circle) :
    ∃ c : OpenPartialHomeomorph ℝ Circle, z ∈ c.target := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hhalf : ((1/2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
    intro h
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show (1/2 : ℝ) ∈ Ico 0 (0+1) by norm_num)
      (show (0 : ℝ) ∈ Ico 0 (0+1) by norm_num)).mp h
    norm_num at hh
  obtain ⟨a, ha⟩ : ∃ a : ℝ, e.symm z ≠ (a : AddCircle (1 : ℝ)) := by
    by_cases hz : e.symm z = 0
    · exact ⟨1/2, by simpa only [hz] using hhalf.symm⟩
    · exact ⟨0, hz⟩
  refine ⟨(AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).trans e.toOpenPartialHomeomorph, ?_⟩
  rw [OpenPartialHomeomorph.trans_target]
  exact ⟨mem_univ _, ha⟩

lemma isOpenMap_circle_to_real_manifold {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    {f : Circle → M} (hf : Continuous f) (hi : Injective f) : IsOpenMap f := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨c, hc⟩ := exists_real_circle_chart z
  exact continuous_injective_local_real_image hf hi c (chartAt ℝ (f z))
    hc (mem_chart_source ℝ (f z)) hU hz

end CircleDomainRigidity

end

end OAI
