import OAI.Analysis.KadisonKastler.PointedMatrixProduct
import OAI.Analysis.KadisonKastler.SpatialAssociatorTransport

namespace OAI

/-! # Spatial transport of pointed matrix products

Conjugating all site operators by one Hilbert-space equivalence preserves
cyclicity, separation and every finite product-state moment.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem matrixUnit_algebra_map
    (E : Generator.MatrixUnitSystem (Fin 2) (H →L[ℂ] H))
    (f : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    E.algebra.map f = (E.map f).algebra := by
  apply le_antisymm
  · apply StarSubalgebra.map_le_iff_le_comap.mpr
    apply (E.algebra_le_iff _).mpr
    intro i j
    exact (E.map f).entry_mem i j
  · apply ((E.map f).algebra_le_iff _).mpr
    intro i j
    exact ⟨E.entry i j, E.entry_mem i j, rfl⟩

@[simp] theorem spatialTransportEquiv_vector (e : H ≃ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) (Ω : H) (a : Algebra M) :
    algebraVectorMap (spatialTransportAlgebra e M) (e Ω) (spatialTransportEquiv e M a) =
      e (algebraVectorMap M Ω a) := by
  change e.conjStarAlgEquiv a.val (e Ω) = e (a.val Ω)
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]

namespace PointedMatrixSites

variable {I : Type*} {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

/-- All concrete pointed-product data survive spatial transport. -/
def transport (S : PointedMatrixSites M Ω ν) (e : H ≃ₗᵢ[ℂ] K) :
    PointedMatrixSites (spatialTransportAlgebra e M) (e Ω) ν where
  valid := S.valid
  site i := (S.site i).map e.conjStarAlgEquiv.toStarAlgHom
  commuting i j hij a b c d :=
    (S.commuting i j hij a b c d).map e.conjStarAlgEquiv.toMonoidHom
  generates := by
    calc
      spatialTransportAlgebra e M = spatialTransportAlgebra e
          (generatedVonNeumannAlgebra (⨆ i, (S.site i).algebra)) :=
        congrArg (spatialTransportAlgebra e) S.generates
      _ = _ := by
        rw [spatialTransport_generated]
        congr 1
        rw [(StarSubalgebra.gc_map_comap e.conjStarAlgEquiv.toStarAlgHom).l_iSup]
        congr 1
        funext i
        exact matrixUnit_algebra_map (S.site i) _
  unit_vector := by rw [e.norm_map, S.unit_vector]
  cyclic := by
    apply Dense.mono _ (e.surjective.denseRange.comp S.cyclic e.continuous)
    rintro _ ⟨a,rfl⟩
    exact ⟨spatialTransportEquiv e M a, spatialTransportEquiv_vector e M Ω a⟩
  separating := by
    intro a b hab
    obtain ⟨a',rfl⟩ := (spatialTransportEquiv e M).surjective a
    obtain ⟨b',rfl⟩ := (spatialTransportEquiv e M).surjective b
    change algebraVectorMap _ _ (spatialTransportEquiv e M a') =
      algebraVectorMap _ _ (spatialTransportEquiv e M b') at hab
    rw [spatialTransportEquiv_vector, spatialTransportEquiv_vector] at hab
    exact congrArg (spatialTransportEquiv e M) (S.separating (e.injective hab))
  moments l hl r c := by
    have hp : (l.map fun i =>
        ((S.site i).map e.conjStarAlgEquiv.toStarAlgHom).entry (r i) (c i)).prod =
        e.conjStarAlgEquiv ((l.map fun i => (S.site i).entry (r i) (c i)).prod) := by
      simp only [map_list_prod, List.map_map]
      rfl
    rw [hp, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      e.symm_apply_apply, e.inner_map_map]
    exact S.moments l hl r c

end PointedMatrixSites

end

end KadisonKastler

end OAI
