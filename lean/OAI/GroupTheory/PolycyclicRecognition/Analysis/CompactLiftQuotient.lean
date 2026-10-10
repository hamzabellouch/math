import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

namespace OAI

/-! # Compact lifts and the topology of the actual quotient orbit -/

noncomputable section
namespace PolycyclicRecognition

open Set TopologicalSpace Topology
open scoped Manifold

/-- A continuous surjection with compact lifts of compact sets is a
quotient map into a Hausdorff compactly generated space. -/
theorem isQuotientMap_of_compact_lifts
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [CompactlyGeneratedSpace Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hlift : ∀ K : Set Y, IsCompact K → ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C) :
    IsQuotientMap f := by
  refine isQuotientMap_iff_isClosed.mpr ⟨hsurj, fun S => ⟨fun h => h.preimage hf, ?_⟩⟩
  intro hS
  apply (CompactlyGeneratedSpace.isClosed_iff_of_t2 S).mpr
  intro K hK
  obtain ⟨C, hC, hcover⟩ := hlift K hK
  have hc : IsCompact ((C ∩ f ⁻¹' S) ∩ f ⁻¹' K) :=
    (hC.inter_right hS).inter_right (hK.isClosed.preimage hf)
  have he : f '' ((C ∩ f ⁻¹' S) ∩ f ⁻¹' K) = S ∩ K := by
    ext y
    constructor
    · rintro ⟨x, ⟨⟨_, hxS⟩, hxK⟩, rfl⟩
      exact ⟨hxS, hxK⟩
    · rintro ⟨hyS, hyK⟩
      obtain ⟨x, hxC, hxy⟩ := hcover hyK
      exact ⟨x, ⟨⟨hxC, by simpa only [mem_preimage, hxy] using hyS⟩,
        by simpa only [mem_preimage, hxy] using hyK⟩, hxy⟩
  rw [← he]
  exact (hc.image hf).isClosed

namespace CartanFactorModel

variable {EG G Q : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [TopologicalSpace Q] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The actual orbit map is a quotient map. Its topology follows from
compact Cartan lifts and a continuous section of the nilpotent projection. -/
theorem orbitMap_isQuotientMap
    (π : F.N.carrier →* Q) (hπ : Continuous π)
    (s : Q → F.N.carrier) (hs : Continuous s) (hsection : Function.RightInverse s π)
    (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q) :
    IsQuotientMap (fun g => act g 1) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let p : F.N.carrier × F.D.carrier → G := fun z => F.inclusionN z.1 * F.inclusionD z.2
  have hp : IsQuotientMap p := isQuotientMap_of_compact_lifts p
    ((F.closedN.continuous.comp continuous_fst).mul (F.closedD.continuous.comp continuous_snd))
    F.surjective F.compactLifts
  have hcont : Continuous (fun g => act g 1) := hp.continuous_iff.mpr (by
    have hh : (fun z : F.N.carrier × F.D.carrier => act (p z) 1) =
        fun z => π z.1 := by
      funext z
      simp only [p, hact, map_one, mul_one]
    change Continuous (fun z => act (p z) 1)
    rw [hh]
    exact hπ.comp continuous_fst)
  have hright : Function.LeftInverse (fun g => act g 1) (fun q => F.inclusionN (s q)) := by
    intro q
    have hh := hact (s q) 1 1
    simpa only [map_one, mul_one, hsection q] using hh
  exact IsQuotientMap.of_inverse (F.closedN.continuous.comp hs) hcont hright

end CartanFactorModel
end PolycyclicRecognition

end

end OAI
