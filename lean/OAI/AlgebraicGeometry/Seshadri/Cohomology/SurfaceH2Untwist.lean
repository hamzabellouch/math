import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CurveH1Bound
import OAI.AlgebraicGeometry.Seshadri.Intersection.ExactDimensionBound

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

lemma cohomologyDimension_pushforward {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    cohomologyDimension p ((Scheme.Modules.pushforward i).obj M) n =
      cohomologyDimension (i ≫ p) M n := by
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward i).obj M) n) (baseScalars p)
  let := Module.compHom (cohomology M n) (baseScalars (i ≫ p))
  exact (ClosedPushforward.cohomologyEquiv i p M n).finrank_eq.symm

theorem generated_section_H2_untwist (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L M : LineBundle S.scheme)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ L.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
    (hdeg : let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
      0 ≤ curveDegree S (L.tensor M) C) :
    cohomologyDimension S.structureMap M.sheaf 2 ≤
      cohomologyDimension ((sectionIdeal k s hs v).subschemeι ≫ S.structureMap)
        (O (sectionIdeal k s hs v).subscheme) 1 +
      cohomologyDimension S.structureMap (L.tensor M).sheaf 2 := by
  let I := sectionIdeal k s hs v
  let C : IntegralCurve S := ⟨I.subscheme,I.subschemeι,inferInstance,inferInstance,hd⟩
  let N := (L.tensor M).pullback C.embedding
  let φ : M.sheaf ⟶ (L.tensor M).sheaf :=
    sectionMultiply L M (sectionCombination k s v)
  let : Mono φ := sectionMultiply_mono L M (sectionCombination k s v) hne
  obtain ⟨hz,hseq⟩ := CartierSequence.exact S.structureMap M (L.tensor M) φ I (by
    intro x
    obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
    refine ⟨U,hx,f,tensorFrame L M U.1 e f,?_⟩
    exact (sectionIdeal_on_any_frame k s hs v U e).trans
      (tensor_multiply_ideal L M (sectionCombination k s v) U e f).symm)
  have H := cohomologyDimension_untwist_bound S.structureMap hseq 1
    (S.cohomology_finite A hA M 2) (S.cohomology_finite A hA (L.tensor M) 2)
    (C.pushforward_cohomology_finite S A hA N 1)
  change cohomologyDimension S.structureMap M.sheaf 2 ≤
    cohomologyDimension S.structureMap ((Scheme.Modules.pushforward C.embedding).obj N.sheaf) 1 +
    cohomologyDimension S.structureMap (L.tensor M).sheaf 2 at H
  rw [cohomologyDimension_pushforward] at H
  exact H.trans (Nat.add_le_add_right (C.H1_le S A hA N hdeg) _)
end
end MaximalSeshadri.Geometry

end

end OAI
