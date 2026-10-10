import OAI.Geometry.NodalSets.Elliptic.OperatorLocality
import OAI.Geometry.NodalSets.Waves.FiniteWaveDerivativeBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussianWaveField_tsupport_subset (V : ι → Coord → ℂ) (a : ι × Fin 2 → ℝ)
    {C : Set Coord} (hC : IsClosed C) (hV : ∀ i, tsupport (V i) ⊆ C) :
    tsupport (gaussianWaveField V a) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  by_contra hxc
  apply hx
  have hz (i : ι) : V i x = 0 := image_eq_zero_of_notMem_tsupport (fun hi ↦ hxc (hV i hi))
  simp [gaussianWaveField,hz]

lemma complexified_tsupport_subset (u : Coord → ℝ) {C : Set Coord} (hC : IsClosed C)
    (hu : tsupport u ⊆ C) : tsupport (fun x ↦ (u x : ℂ)) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  apply hu
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

lemma source_residual_tsupport_subset
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (u : Coord → ℂ) (lam : ℂ) {C : Set Coord} (hC : IsClosed C) (hu : tsupport u ⊆ C) :
    tsupport (fun x ↦ sourceWeightedOperator g w u x + lam*u x) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  by_contra hxc
  have hz : x ∉ tsupport u := fun h ↦ hxc (hu h)
  have he : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hz
  have hop := (sourceOperator_eventuallyEq g w he).eq_of_nhds
  apply hx
  simp only [hop,sourceWeightedOperator_zero,Pi.zero_apply,he.eq_of_nhds,mul_zero,add_zero]

end
end Yau.Geometry

end OAI
