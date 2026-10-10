import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

def affineCoefficient {M : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) : Γ(X,U.1) :=
  U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))

lemma affineCoefficient_change {M : X.Modules} (U : X.affineOpens)
    (e f : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) :
    Associated (affineCoefficient U e s) (affineCoefficient U f s) := by
  unfold affineCoefficient
  rw [coefficient_change e f, map_mul]
  exact associated_unit_mul_right _ _ ((frameChange e f).isUnit.map U.1.topIso.hom.hom)

lemma affineCoefficient_iso {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (g : M ≅ N) (s : O X ⟶ M) :
    Associated (affineCoefficient U e s) (affineCoefficient U f (s ≫ g.hom)) := by
  have h := affineCoefficient_change U e
    ((Scheme.Modules.restrictFunctor U.1.ι).mapIso g ≪≫ f) s
  let restriction := Scheme.Modules.restrictFunctor U.1.ι
  let unitIso := Scheme.Modules.restrictUnitIso U.1.ι
  have composition :
      (unitIso.inv ≫ restriction.map s) ≫ restriction.map g.hom ≫ f.hom =
        (unitIso.inv ≫ restriction.map (s ≫ g.hom)) ≫ f.hom := by
    calc
      _ = unitIso.inv ≫ (restriction.map s ≫ restriction.map g.hom) ≫ f.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun morphism => unitIso.inv ≫ morphism)
            (Category.assoc _ _ _).symm)
      _ = unitIso.inv ≫ restriction.map (s ≫ g.hom) ≫ f.hom :=
        congrArg (fun morphism => unitIso.inv ≫ morphism ≫ f.hom)
          (restriction.map_comp s g.hom).symm
      _ = _ := (Category.assoc _ _ _).symm
  have equality : affineCoefficient U (restriction.mapIso g ≪≫ f) s =
      affineCoefficient U f (s ≫ g.hom) :=
    congrArg (fun value => U.1.topIso.hom value) (congrArg endValue composition)
  exact equality ▸ h

lemma affineCoefficient_ne_zero [IsIntegral X] (L : LineBundle X)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : affineCoefficient U e s ≠ 0 := by
  exact (isRegular_iff_ne_zero.mp (L.section_coefficient_regular s hs U e))

lemma coefficient_postcompose {Y : Scheme.{0}} {M N : Y.Modules}
    (e : M ≅ O Y) (f : N ≅ O Y) (s : O Y ⟶ M) (a : M ⟶ N) :
    coefficient f (s ≫ a) = coefficient e s * endValue (e.inv ≫ a ≫ f.hom) := by
  unfold coefficient
  rw [← endValue_comp]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]

lemma associated_unit_middle {R : Type*} [CommMonoid R] (a b u : R) (hu : IsUnit u) :
    Associated (a*b) (b*(u*a)) := by
  rw [show b*(u*a) = u*(a*b) by ac_rfl]
  exact associated_unit_mul_right _ _ hu

lemma affineCoefficient_sectionMultiply (L M : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (g : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    Associated (affineCoefficient U e s * affineCoefficient U f t)
      (affineCoefficient U g (t ≫ sectionMultiply L M s)) := by
  apply Associated.trans _ (affineCoefficient_change U (tensorFrame L M U.1 e f) g _)
  let multiplication : M.sheaf ⟶ (L.tensor M).sheaf := sectionMultiply L M s
  let restriction := Scheme.Modules.restrictFunctor U.1.ι
  let unitIso := Scheme.Modules.restrictUnitIso U.1.ι
  let tensorTrivialization : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
    tensorFrame L M U.1 e f
  have restrictedComposition : restrictSection U.1.ι (t ≫ multiplication) =
      restrictSection U.1.ι t ≫ restriction.map multiplication :=
    (congrArg (fun morphism => unitIso.inv ≫ morphism)
      (restriction.map_comp t multiplication)).trans (Category.assoc _ _ _).symm
  have he : coefficient (tensorFrame L M U.1 e f)
      (restrictSection U.1.ι (t ≫ sectionMultiply L M s)) =
      coefficient f (restrictSection U.1.ι t) *
        (endValue (tensorUnitTwist M U.1 f).hom * coefficient e (restrictSection U.1.ι s)) := by
    calc
      _ = coefficient tensorTrivialization
          (restrictSection U.1.ι t ≫ restriction.map multiplication) :=
        congrArg (coefficient tensorTrivialization) restrictedComposition
      _ = coefficient f (restrictSection U.1.ι t) *
          endValue (f.inv ≫ restriction.map multiplication ≫ tensorTrivialization.hom) :=
        coefficient_postcompose f tensorTrivialization _ _
      _ = coefficient f (restrictSection U.1.ι t) *
          endValue ((tensorUnitTwist M U.1 f).hom ≫ (restrictSection U.1.ι s ≫ e.hom)) :=
        congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme =>
          coefficient f (restrictSection U.1.ι t) * endValue morphism)
          (tensor_multiply_framed L M s U.1 e f)
      _ = _ := congrArg (coefficient f (restrictSection U.1.ι t) * ·)
        (endValue_comp _ _)
  have equality : affineCoefficient U tensorTrivialization (t ≫ multiplication) =
      affineCoefficient U f t *
        (U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).hom) * affineCoefficient U e s) :=
    (congrArg (fun value => U.1.topIso.hom value) he).trans
      (by simp only [map_mul, affineCoefficient])
  exact equality.symm ▸ associated_unit_middle
    (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))
    (U.1.topIso.hom (coefficient f (restrictSection U.1.ι t)))
    (U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).hom))
    (((end_isIso_iff _).mp (tensorUnitTwist M U.1 f).isIso_hom).map
      U.1.topIso.hom.hom)

lemma affineCoefficient_power (L : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (s : O X ⟶ L.sheaf) (n : ℕ)
    (f : (L.pow n).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Associated ((affineCoefficient U e s)^n)
      (affineCoefficient U f (powerSection s n)) := by
  apply Associated.trans _ (affineCoefficient_change U (localPowerFrame U.1 e n) f _)
  have equality : affineCoefficient U (localPowerFrame U.1 e n) (powerSection s n) =
      U.1.topIso.hom (endValue (powerRestrictionUnit U.1 n).hom) *
        (affineCoefficient U e s) ^ n :=
    (congrArg (fun value => U.1.topIso.hom value)
      (local_powerSection_coefficient U.1 e s n)).trans
        (by simp only [map_mul, map_pow, affineCoefficient])
  exact equality.symm ▸ associated_unit_mul_right _ _
    ((local_powerSection_coefficient_unit U.1 n).map U.1.topIso.hom.hom)

lemma affineCoefficient_division (L : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (d n : ℕ)
    (s : O X ⟶ (L.pow d).sheaf) (t : O X ⟶ (L.pow n).sheaf) :
    Associated
      (affineCoefficient U (localPowerFrame U.1 e d) s *
       affineCoefficient U (localPowerFrame U.1 e n) t)
      (affineCoefficient U (localPowerFrame U.1 e (d+n))
        (t ≫ sectionMultiply (L.pow d) (L.pow n) s ≫ (linePowerAdd L d n).inv)) := by
  exact (affineCoefficient_sectionMultiply (L.pow d) (L.pow n) U _ _
    (tensorFrame (L.pow d) (L.pow n) U.1 (localPowerFrame U.1 e d)
      (localPowerFrame U.1 e n)) s t).trans
    (affineCoefficient_iso U _ _ (linePowerAdd L d n).symm _)

end
end MaximalSeshadri.Geometry

end

end OAI
