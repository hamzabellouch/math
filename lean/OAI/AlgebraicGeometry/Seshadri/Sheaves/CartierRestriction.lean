import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.CurveCartierEuler
import OAI.AlgebraicGeometry.Seshadri.Intersection.IntersectionCurveIso

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X : Scheme.{0}}

lemma ideal_affine_ne_bot [IsIntegral X] (Q : X.IdealSheafData) (hQ : Q ≠ ⊥)
    (U : X.affineOpens) [Nonempty U.1] : Q.ideal U ≠ ⊥ := by
  intro hz
  have hs : (U.1 : Set X) ⊆ Q.support := by
    intro x hx
    exact (Q.mem_support_iff_of_mem hx).mpr (by simp [hz])
  have hd : Dense (U.1 : Set X) := U.1.isOpen.dense (by
    obtain ⟨u⟩ : Nonempty U.1 := inferInstance
    exact ⟨u.1,u.2⟩)
  have he : (Q.support : Set X) = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← hd.closure_eq]
    exact closure_minimal hs Q.support.isClosed
  exact hQ (Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective he))

lemma regular_restriction_of_not_le (I J : X.IdealSheafData)
    [IsIntegral I.subscheme] (hn : ¬ J ≤ I)
    (hJ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X,U.1),
      J.ideal U = Ideal.span {r}) :
    ∀ y : I.subscheme, ∃ U : I.subscheme.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(I.subscheme,U.1), IsRegular r ∧
        (J.comap I.subschemeι).ideal U = Ideal.span {r} := by
  have hQ : J.comap I.subschemeι ≠ ⊥ := by
    intro hz
    have hl := J.le_map_comap I.subschemeι
    rw [hz,Scheme.IdealSheafData.map_bot,Scheme.IdealSheafData.ker_subschemeι] at hl
    exact hn hl
  intro y
  obtain ⟨U,hy,r,he⟩ := hJ (I.subschemeι y)
  let V : I.subscheme.affineOpens := ⟨I.subschemeι ⁻¹ᵁ U.1,U.2.preimage I.subschemeι⟩
  let : Nonempty V.1 := ⟨⟨y,hy⟩⟩
  let r' := I.subschemeι.appLE U.1 V.1 le_rfl r
  have ht : (J.comap I.subschemeι).ideal V = Ideal.span {r'} := by
    rw [IdealPullback.comap_ideal J I.subschemeι V U le_rfl,he,
      Ideal.map_span,Set.image_singleton]
  refine ⟨V,hy,r',?_,ht⟩
  apply isRegular_iff_ne_zero.mpr
  intro hr
  apply ideal_affine_ne_bot _ hQ V
  simpa [hr] using ht

theorem projective_curve_intersection_ideal_euler {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (I J : X.IdealSheafData)
    [IsIntegral I.subscheme] [IsNoetherian I.subscheme]
    [IsProper (I.subschemeι ≫ p)]
    (hd : topologicalKrullDim I.subscheme = 1)
    {M : I.subscheme.Modules} (s : σ → (Frames.O I.subscheme ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (Projective.sectionsMorphism
      ((I.subschemeι ≫ p).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs)]
    (hn : ¬ J ≤ I)
    (hJ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X,U.1),
      J.ideal U = Ideal.span {r}) :
    eulerCharacteristic (I.subschemeι ≫ p) 1 (structureSheaf I.subscheme) -
      eulerCharacteristic (I.subschemeι ≫ p) 1
        (IdealModule.closedModule (J.comap I.subschemeι)) =
      letI : Algebra ℂ Γ((I ⊔ J).subscheme,⊤) :=
        (baseScalars ((I ⊔ J).subschemeι ≫ p)).toAlgebra;
      (Module.finrank ℂ Γ((I ⊔ J).subscheme,⊤) : ℤ) := by
  have h := projective_curve_cartier_euler_length (I.subschemeι ≫ p) hd s hs
    (J.comap I.subschemeι) (regular_restriction_of_not_le I J hn hJ)
  exact h.trans (congrArg (fun length : ℕ => (length : ℤ))
    (intrinsicIntersection_length p I J).symm)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
