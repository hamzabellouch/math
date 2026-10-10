import OAI.Probability.SLE.Geometry.FiniteTraceTopology

namespace OAI

/-! Every finite Loewner-domain boundary point is on the finite trace or
on the real axis. This identifies the possible inverse cluster points. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma frontier_survivingDomain_subset {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (T : ℝ≥0) :
    frontier (survivingDomain γ T) ⊆ (γ '' Icc 0 T) ∪ {z : ℂ | z.im=0} := by
  intro z hz
  by_cases htrace : z∈γ '' Icc 0 T
  · exact Or.inl htrace
  right
  have hclosed : IsClosed {z : ℂ | 0≤z.im} := isClosed_le continuous_const Complex.continuous_im
  have hsub : survivingDomain γ T ⊆ {w : ℂ | 0≤w.im} := by
    intro w hw
    change 0≤w.im
    exact hw.1.1.le
  have hznonneg : 0≤z.im := (closure_minimal hsub hclosed) hz.1
  by_contra hz0
  have hzH : z∈upperHalfPlane := lt_of_le_of_ne hznonneg (Ne.symm hz0)
  let S := upperHalfPlane \ (γ '' Icc 0 T)
  have hS : IsOpen S := isOpen_upperHalfPlane.sdiff (finiteTrace_isCompact hγ T).isClosed
  have hzS : z∈S := ⟨hzH,htrace⟩
  have hznot : z∉survivingDomain γ T := by
    simpa only [(isOpen_survivingDomain hγ T).interior_eq] using hz.2
  have hb : Bornology.IsBounded (connectedComponentIn S z) := by
    by_contra hn
    exact hznot ⟨hzS,hn⟩
  have hCn : connectedComponentIn S z∈𝓝 z :=
    (hS.connectedComponentIn).mem_nhds (mem_connectedComponentIn hzS)
  obtain ⟨w,hwC,hwD⟩ := mem_closure_iff_nhds.mp hz.1 _ hCn
  have hwBound : Bornology.IsBounded (connectedComponentIn S w) := by
    rwa [← connectedComponentIn_eq hwC]
  exact hwD.2 hwBound

end SLEExactGauge

end

end OAI
