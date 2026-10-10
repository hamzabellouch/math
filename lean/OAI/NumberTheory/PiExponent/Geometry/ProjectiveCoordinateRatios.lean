import OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry Frames ModuleFlasque RestrictionCohomology
open PiExponentSeshadri.ProjectiveChartSections
variable {X : Scheme} {M : X.Modules}

def coordinateRatioOn (si sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) : Γ(X,W) :=
  X.presheaf.map (homOfLE hi).op
    ((SectionOpens.isoOpen si).topIso.hom
      (coefficient (sectionFrame si)
        (restrictSection (SectionOpens.isoOpen si).ι sk)))

lemma coordinateRatioOn_eq_coefficient (si sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) :
    coordinateRatioOn si sk hi = W.topIso.hom
      (coefficient (restrictOpenFrame hi (sectionFrame si)) (restrictSection W.ι sk)) := by
  rw [restrictOpenFrame_coefficient_global, topIso_hom_restrict]
  rfl

@[simp] lemma coordinateRatioOn_self (si : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) : coordinateRatioOn si si hi = 1 := by
  simp only [coordinateRatioOn, sectionFrame_normalized, map_one]

lemma coordinateRatioOn_change (si sj sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    coordinateRatioOn sj sk hj = coordinateRatioOn sj si hj * coordinateRatioOn si sk hi := by
  rw [coordinateRatioOn_eq_coefficient sj sk hj,
    coefficient_change (restrictOpenFrame hi (sectionFrame si)),
    frameChange_restrictOpenFrame hi hj _ _ si (sectionFrame_normalized si),
    map_mul, topIso_hom_restrict, ← coordinateRatioOn_eq_coefficient]
  rfl

lemma coordinateRatioOn_reciprocal (si sj : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    coordinateRatioOn sj si hj * coordinateRatioOn si sj hi = 1 := by
  rw [← coordinateRatioOn_change si sj sj hi hj, coordinateRatioOn_self]

lemma coordinateRatioOn_restrict (si sk : O X ⟶ M) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen si) (h : W ≤ U) :
    X.presheaf.map (homOfLE h).op (coordinateRatioOn si sk hi) =
      coordinateRatioOn si sk (h.trans hi) := by
  unfold coordinateRatioOn
  change (X.presheaf.map (homOfLE hi).op ≫ X.presheaf.map (homOfLE h).op) _ = _
  rw [← Functor.map_comp]
  rfl

lemma framedHomCoefficientsEquiv_change (W : X.Opens) (N : X.Modules)
    (e f : N.restrict W.ι ≅ structureSheaf W.toScheme)
    (b : freeOpen X.ringCatSheaf W ⟶ N) :
    framedHomCoefficientsEquiv W N f b =
      W.topIso.hom (frameChange e f : Γ(W.toScheme,⊤)) *
        framedHomCoefficientsEquiv W N e b := by
  let x := (restrictionSectionsIso W N).inv (freeOpenEquiv X.ringCatSheaf N W b)
  change W.topIso.hom (f.hom.app ⊤ x) =
    W.topIso.hom (frameChange e f : Γ(W.toScheme,⊤)) * W.topIso.hom (e.hom.app ⊤ x)
  erw [← map_mul]
  apply congrArg W.topIso.hom
  have hx : e.inv.app ⊤ (e.hom.app ⊤ x) = x :=
    congrArg (fun g => g.app ⊤ x) e.hom_inv_id
  have hc := end_apply (e.inv ≫ f.hom) ⊤ (e.hom.app ⊤ x)
  change f.hom.app ⊤ (e.inv.app ⊤ (e.hom.app ⊤ x)) =
    (show Γ(W.toScheme,⊤) from e.hom.app ⊤ x) *
      (frameChange e f : Γ(W.toScheme,⊤)) at hc
  rw [hx, mul_comm] at hc
  exact hc

lemma coordinatePowerFrame_hom_change (si sj : O X ⟶ M) (n : ℕ) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj)
    (b : freeOpen X.ringCatSheaf W ⟶ modulePow X M n) :
    framedHomCoefficientsEquiv W (modulePow X M n)
      (restrictOpenFrame hj (coordinatePowerFrame sj n)) b =
    coordinateRatioOn sj si hj ^ n *
      framedHomCoefficientsEquiv W (modulePow X M n)
        (restrictOpenFrame hi (coordinatePowerFrame si n)) b := by
  erw [framedHomCoefficientsEquiv_change W _
    (restrictOpenFrame hi (coordinatePowerFrame si n)),
    coordinatePowerFrame_frameChange, map_pow, topIso_hom_restrict]
  rfl

lemma framedHomCoefficientsEquiv_eq_of_normalized (W : X.Opens) (N : X.Modules)
    (e f : N.restrict W.ι ≅ structureSheaf W.toScheme)
    (t : O W.toScheme ⟶ N.restrict W.ι)
    (he : coefficient e t = 1) (hf : coefficient f t = 1)
    (b : freeOpen X.ringCatSheaf W ⟶ N) :
    framedHomCoefficientsEquiv W N f b = framedHomCoefficientsEquiv W N e b := by
  have hc := coefficient_change e f t
  rw [he, hf, mul_one] at hc
  rw [framedHomCoefficientsEquiv_change W N e f, ← hc, map_one, one_mul]

lemma coordinatePowerFrame_hom_restrict (si : O X ⟶ M) (n : ℕ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen si) (h : W ≤ U)
    (b : freeOpen X.ringCatSheaf U ⟶ modulePow X M n) :
    framedHomCoefficientsEquiv W (modulePow X M n)
      (restrictOpenFrame (h.trans hi) (coordinatePowerFrame si n))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
    X.presheaf.map (homOfLE h).op
      (framedHomCoefficientsEquiv U (modulePow X M n)
        (restrictOpenFrame hi (coordinatePowerFrame si n)) b) := by
  have he : coefficient
      (restrictOpenFrame h (restrictOpenFrame hi (coordinatePowerFrame si n)))
      (restrictSection W.ι (powerSection si n)) = 1 := by
    erw [restrictOpenFrame_coefficient_global, restrictOpenFrame_coefficient_global,
      coordinatePowerFrame_normalized, map_one, map_one]
  have hf : coefficient
      (restrictOpenFrame (h.trans hi) (coordinatePowerFrame si n))
      (restrictSection W.ι (powerSection si n)) = 1 := by
    erw [restrictOpenFrame_coefficient_global, coordinatePowerFrame_normalized, map_one]
  erw [framedHomCoefficientsEquiv_eq_of_normalized W (modulePow X M n)
    (restrictOpenFrame h (restrictOpenFrame hi (coordinatePowerFrame si n)))
    (restrictOpenFrame (h.trans hi) (coordinatePowerFrame si n))
    (restrictSection W.ι (powerSection si n)) he hf]
  exact framedHomCoefficientsEquiv_restrict (modulePow X M n) h _ b

lemma coordinatePowerFrame_hom_change_restrict (si sj : O X ⟶ M) (n : ℕ)
    {U W : X.Opens} (hi : U ≤ SectionOpens.isoOpen si)
    (hj : W ≤ SectionOpens.isoOpen sj) (h : W ≤ U)
    (b : freeOpen X.ringCatSheaf U ⟶ modulePow X M n) :
    framedHomCoefficientsEquiv W (modulePow X M n)
      (restrictOpenFrame hj (coordinatePowerFrame sj n))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
    coordinateRatioOn sj si hj ^ n * X.presheaf.map (homOfLE h).op
      (framedHomCoefficientsEquiv U (modulePow X M n)
        (restrictOpenFrame hi (coordinatePowerFrame si n)) b) := by
  erw [coordinatePowerFrame_hom_change si sj n (h.trans hi) hj,
    coordinatePowerFrame_hom_restrict]

end
end PiExponentSeshadri.Projective

end OAI
