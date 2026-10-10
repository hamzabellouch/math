import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.FiniteAtlas
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtalePointChart

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

lemma Surface.etale_line_frame_inside (S : Surface) (J : LineBundle S.scheme)
    (W : S.scheme.Opens) (x : S.scheme) (hx : x ∈ W) :
    ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ _ : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        ∃ t : Fin 2 → Γ(S.scheme,U.1),
          (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale := by
  classical
  obtain ⟨V,hV,⟨e⟩⟩ := J.locallyRankOne x
  obtain ⟨C,hxC,hC⟩ := @exists_etale_projective_neighborhood ℂ _ S.scheme
    (Fin (S.embeddingDimension + 1)) S.integral S.structureMap S.smooth
    S.embedding S.closedImmersion S.overComplex (V ⊓ W) x ⟨hV,hx⟩
  let := C.finite
  let := Fintype.ofFinite C.κ
  let eκ : Fin 2 ≃ C.κ := (Fintype.equivFinOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using C.card)).symm
  let := (openScalars S.structureMap C.U.1).toAlgebra
  let a : C.κ → Γ(S.scheme,C.U.1) := fun k => -C.φ (MaximalSeshadri.Projective.chartCoordinate C.coord (C.a k).1)
  refine ⟨C.U,hxC,hC.trans inf_le_right,frameOnSmaller e C.U.1 (hC.trans inf_le_left),a ∘ eκ,?_⟩
  exact etale_aeval_reindex a C.etale eκ

end
end MaximalSeshadri.Geometry

end

end OAI
