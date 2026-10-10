import OAI.NumberTheory.PiExponent.Ampleness.NakaiCartier
import OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers

namespace OAI

namespace PiExponent.CartierPowerFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def sectionMultiplyLeft (L M : X.Modules) (s : structureSheaf X ⟶ L) :
    M ⟶ moduleTensor X L M :=
  (moduleTensorUnit M).inv ≫ moduleTensorMap s (𝟙 M)

def tensorFrame (L M : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (moduleTensor X L M).restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L M ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

def tensorUnitTwist (M : X.Modules) (U : X.Opens)
    (f : M.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M).symm ≪≫
    moduleTensorRestrict U (O X) M ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

private lemma frame_section {C : Type*} [Category C] {A B D : C}
    (u : A ≅ B) (s : A ⟶ D) (e : D ≅ B) :
    s ≫ e.hom = u.hom ≫ ((u.inv ≫ s) ≫ e.hom) := by
  simp

private lemma framed_multiply {C : Type*} [Category C] {A B D P Q T O : C}
    (g : O ⟶ A) (k : A ⟶ B) (m : B ⟶ D) (r : B ⟶ P) (r' : D ⟶ Q)
    (e : P ⟶ T) (e' : Q ⟶ T) (u : T ⟶ O) (a : O ⟶ O)
    (p : P ⟶ Q) (b : T ⟶ T)
    (hn : m ≫ r' = r ≫ p) (ht : p ≫ e' = e ≫ b) (hs : b ≫ u = u ≫ a) :
    g ≫ (k ≫ m) ≫ (r' ≫ e' ≫ u) = (g ≫ k ≫ r ≫ e ≫ u) ≫ a := by
  simp only [Category.assoc]
  rw [← Category.assoc m r', hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e', ht]
  simp only [Category.assoc]
  rw [hs]

lemma tensor_multiply_framed (L M : X.Modules) (s : O X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    f.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiplyLeft L M s) ≫
      (tensorFrame L M U e f).hom = (tensorUnitTwist M U f).hom ≫
        (restrictSection U.ι s ≫ e.hom) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U (O X) M
  let R' := moduleTensorRestrict U L M
  let E := moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f
  let E' := moduleTensorIso e f
  let T := moduleTensorUnit (O U.toScheme)
  let a : O U.toScheme ⟶ O U.toScheme := restrictSection U.ι s ≫ e.hom
  let p := moduleTensorMap (F.map s) (𝟙 (M.restrict U.ι))
  have hn : F.map (moduleTensorMap s (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U s (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map s) q) (F.map_id M))
  have he : F.map s ≫ e.hom = (Scheme.Modules.restrictUnitIso U.ι).hom ≫ a := by
    simpa only [a, restrictSection] using!
      frame_section (Scheme.Modules.restrictUnitIso U.ι) (F.map s) e
  have h₁ := (moduleTensorMap_comp (F.map s) e.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map s ≫ e.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp (Scheme.Modules.restrictUnitIso U.ι).hom a
      f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap ((Scheme.Modules.restrictUnitIso U.ι).hom ≫ a))
      (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap a (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj (O X) ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap a (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ a :=
    (moduleTensorUnit_scalar (X := U.toScheme) a (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id a))
  have hfinal := framed_multiply f.inv (F.map (moduleTensorUnit M).inv)
    (F.map (moduleTensorMap s (𝟙 M))) R.hom R'.hom E.hom E'.hom T.hom a p _ hn ht hs
  simpa only [sectionMultiplyLeft, tensorFrame, tensorUnitTwist] using!
    (congrArg (fun q => f.inv ≫ q ≫ (tensorFrame L M U e f).hom)
      (F.map_comp (moduleTensorUnit M).inv (moduleTensorMap s (𝟙 M)))).trans hfinal

lemma tensor_multiply_ideal (L M : X.Modules) (s : O X ⟶ L)
    (U : X.affineOpens) (e : L.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue (f.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiplyLeft L M s) ≫
        (tensorFrame L M U.1 e f).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  rw [tensor_multiply_framed,endValue_comp,map_mul,← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).hom) :=
    (end_isIso_iff _).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.top_mul]
  rfl

theorem cartierPowerMultiply_ideal (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (n : ℕ) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((modulePowFrame U.1 e n).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map
        (PiExponent.NumericalAmpleness.cartierPowerMultiply L s n) ≫
      (modulePowFrame U.1 e (n+1)).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} :=
  tensor_multiply_ideal L.sheaf (modulePow X L.sheaf n) s U e (modulePowFrame U.1 e n)
end
end PiExponent.CartierPowerFrames

end OAI
