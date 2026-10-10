import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.CartierSequence
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfaceEuler

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem cartier_euler_difference (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N : LineBundle S.scheme) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : S.scheme.IdealSheafData) [IsIntegral I.subscheme]
    (hd : topologicalKrullDim I.subscheme = 1)
    (heq : ∀ x : S.scheme, ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    eulerCharacteristic S.structureMap 2 N.sheaf - eulerCharacteristic S.structureMap 2 M.sheaf =
      eulerCharacteristic (I.subschemeι ≫ S.structureMap) 1
        ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) := by
  let C : IntegralCurve S := ⟨I.subscheme,I.subschemeι,inferInstance,inferInstance,hd⟩
  let P := N.pullback I.subschemeι
  let : Subsingleton (cohomology M.sheaf (2+1)) := ⟨fun x y =>
    (S.lineBundle_cohomology_zero_above_two A hA M 0 x).trans
      (S.lineBundle_cohomology_zero_above_two A hA M 0 y).symm⟩
  obtain ⟨hz,hseq⟩ := CartierSequence.exact S.structureMap M N φ I heq
  have he := eulerCharacteristic_add S.structureMap hseq 2
    (fun n _ => S.cohomology_finite A hA M n)
    (fun n _ => S.cohomology_finite A hA N n)
    (fun n _ => C.pushforward_cohomology_finite S A hA P n)
  change eulerCharacteristic S.structureMap 2 N.sheaf =
    eulerCharacteristic S.structureMap 2 M.sheaf +
      eulerCharacteristic S.structureMap 2 ((Scheme.Modules.pushforward C.embedding).obj P.sheaf) at he
  rw [C.euler_pushforward S A hA P] at he
  exact sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))

theorem generated_section_euler_difference (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L M : LineBundle S.scheme)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ L.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf -
        eulerCharacteristic S.structureMap 2 M.sheaf =
      eulerCharacteristic ((sectionIdeal k s hs v).subschemeι ≫ S.structureMap) 1
        ((Scheme.Modules.pullback (sectionIdeal k s hs v).subschemeι).obj (L.tensor M).sheaf) := by
  let : Mono (show M.sheaf ⟶ (L.tensor M).sheaf from
      sectionMultiply L M (sectionCombination k s v)) :=
    sectionMultiply_mono L M (sectionCombination k s v) hne
  apply cartier_euler_difference S A hA M (L.tensor M)
    (sectionMultiply L M (sectionCombination k s v)) (sectionIdeal k s hs v) hd
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U,hx,f,tensorFrame L M U.1 e f,?_⟩
  exact (sectionIdeal_on_any_frame k s hs v U e).trans
    (tensor_multiply_ideal L M (sectionCombination k s v) U e f).symm

end
end MaximalSeshadri.Geometry

end

end OAI
