import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

theorem LineBundle.finite_affine_frame_cover [CompactSpace X] (L : LineBundle X) :
    ∃ k : ℕ, ∃ U : Fin k → X.affineOpens,
      (⨆ i, (U i).1) = ⊤ ∧
      ∀ i, Nonempty (L.sheaf.restrict (U i).1.ι ≅ structureSheaf (U i).1.toScheme) := by
  classical
  have hex (x : X) := common_affine_frames L L x
  choose V hx he _ using hex
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((V x).1 : Set X)) (fun x => (V x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, fun i => V (e i).val, ?_, fun i => he (e i).val⟩
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (show x ∈ Set.univ from trivial))
  obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
  exact Opens.mem_iSup.mpr ⟨e.symm ⟨i, hi⟩, by simpa using hx⟩

end
end PiExponentSeshadri.Geometry

end OAI
