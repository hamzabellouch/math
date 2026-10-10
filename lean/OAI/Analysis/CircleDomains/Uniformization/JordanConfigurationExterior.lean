import OAI.Analysis.CircleDomains.Uniformization.JordanCircularizationSequence

namespace OAI

/-! The fixed finite source configuration has a common exterior disk and
a connected finite chart. These provide the domains for normal families. -/
open Set Function Metric Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity.FiniteJordanConfiguration
variable {I : Type*} [Finite I]

def planeRegion (C : FiniteJordanConfiguration I) : Set ℂ :=
  ((↑) : ℂ → Sphere) ⁻¹' C.region

omit [Finite I] in
lemma planeRegion_eq (C : FiniteJordanConfiguration I) :
    C.planeRegion=(⋃ i,closure (jordanInterior (C.hole i)))ᶜ := by
  ext z
  simp only [planeRegion,region,FiniteTransfer.openCompletedRegion,
    FiniteTransfer.closedTerminalCap,mem_preimage,mem_compl_iff,mem_iUnion,
    OnePoint.coe_injective.mem_set_image]

lemma planeRegion_open (C : FiniteJordanConfiguration I) : IsOpen C.planeRegion :=
  C.region_open.preimage OnePoint.continuous_coe

lemma exists_exterior_radius (C : FiniteJordanConfiguration I) :
    ∃ R : ℝ, 0<R ∧ ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ C.region := by
  obtain ⟨R,hR,hbound⟩ := (isCompact_iUnion (fun i =>
    isCompact_closure_jordanInterior (C.hole i))).isBounded.exists_pos_norm_lt
  refine ⟨R,hR,?_⟩
  intro p hp hpC
  obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hpC
  apply hp
  refine ⟨z,?_,rfl⟩
  simpa only [mem_ball,dist_zero_right] using hbound z (mem_iUnion.mpr ⟨i,hz⟩)

lemma planeRegion_connected (C : FiniteJordanConfiguration I) : IsConnected C.planeRegion := by
  obtain ⟨R,hR,hbound⟩ := C.exists_exterior_radius
  refine ⟨?_,?_⟩
  · refine ⟨(R : ℂ),hbound ?_⟩
    simp only [OnePoint.coe_injective.mem_set_image,mem_ball,dist_zero_right,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,mem_compl_iff,lt_self_iff_false,not_false_eq_true]
  · rw [C.planeRegion_eq]
    exact isPreconnected_exterior_finite_jordanInteriors C.hole C.disjoint

end CircleDomainRigidity.FiniteJordanConfiguration

end

end OAI
