import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! An embedded compact arc admits source neighborhoods which capture
only parameters in any prescribed open parameter neighborhood. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
namespace SmoothCompactArc

theorem local_neighborhood (P : SmoothCompactArc I N) {t : ℝ}
    (ht : t ∈ Icc P.start P.finish) {U : Set ℝ} (hU : IsOpen U) (htU : t ∈ U)
    {O : Set N} (hO : IsOpen O) (htO : P.curve t ∈ O) :
    ∃ V : Set N, IsOpen V ∧ P.curve t ∈ V ∧ V ⊆ O ∧
      ∀ s ∈ Icc P.start P.finish, P.curve s ∈ V → s ∈ U := by
  let A := Icc P.start P.finish \ U
  have hA : IsCompact A := isCompact_Icc.diff hU
  have hAD : A ⊆ P.domain := fun _ hx => P.interval_subset hx.1
  have hK : IsCompact (P.curve '' A) := hA.image_of_continuousOn (P.smooth.continuousOn.mono hAD)
  have htK : P.curve t ∉ P.curve '' A := by
    rintro ⟨s,hs,he⟩
    have hst := P.injective hs.1 ht he
    exact hs.2 (hst ▸ htU)
  refine ⟨O \ (P.curve '' A),hO.sdiff hK.isClosed,⟨htO,htK⟩,sdiff_subset,?_⟩
  intro s hs hsV
  by_contra hn
  exact hsV.2 ⟨s,⟨hs,hn⟩,rfl⟩

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
