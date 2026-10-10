import OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} {ι : Type}

def affinePart (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] : C.affineOpens :=
  ⟨i ⁻¹ᵁ j.opensRange, (isAffineOpen_opensRange j).preimage i⟩

def affinePresentation (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] :
    Spec Γ(C,(affinePart i j).1) ⟶ Spec (.of (MvPolynomial ι ℂ)) :=
  (affinePart i j).2.isoSpec.inv ≫ (i ∣_ j.opensRange) ≫ j.isoOpensRange.inv

instance affinePresentation_isClosedImmersion (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] :
    IsClosedImmersion (affinePresentation i j) := by
  unfold affinePresentation
  have hcomp : IsClosedImmersion ((i ∣_ j.opensRange) ≫ j.isoOpensRange.inv) :=
    IsClosedImmersion.comp _ _
  exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance hcomp

@[reassoc] theorem affinePresentation_comp (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] :
    affinePresentation i j ≫ j = (affinePart i j).2.fromSpec ≫ i := by
  unfold affinePresentation IsAffineOpen.fromSpec
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (affinePart i j).2.isoSpec.inv ≫ k)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (i ∣_ j.opensRange) ≫ k)
          (Scheme.Hom.isoOpensRange_inv_comp j)).trans
          (morphismRestrict_ι i j.opensRange)))).trans
      (Category.assoc _ _ _).symm)

theorem affinePresentation_over (p : X ⟶ Spec (.of ℂ))
    (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ))) :
    affinePresentation i j ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      (affinePart i j).2.fromSpec ≫ i ≫ p := by
  rw [← hj, ← Category.assoc, affinePresentation_comp, Category.assoc]

theorem affinePart_nonempty (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j]
    (h : ∃ c : C, i c ∈ j.opensRange) : Nonempty (affinePart i j).1 := by
  obtain ⟨c,hc⟩ := h
  exact ⟨⟨c,hc⟩⟩

end PiExponent.CurveImageAffineCoordinates

end

end OAI
