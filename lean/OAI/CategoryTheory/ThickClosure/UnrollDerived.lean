import OAI.CategoryTheory.ThickClosure.CyclicShift
import OAI.CategoryTheory.ThickClosure.DerivedHom

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.Unroll
section DerivedFunctor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
variable (R : Type u) [Ring R] (D : ℕ)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]

abbrev PD := HomologicalComplexUpToQuasiIso (ModuleCat.{u} R) (.down (ZMod D))
abbrev q : PC R D ⥤ PD R D := HomologicalComplexUpToQuasiIso.Q

omit [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}] in
lemma inverts_quasiIso :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).IsInvertedBy
      (functor R D ⋙ DerivedCategory.Q) := by
  intro P Q f hf
  have : QuasiIso f := (mem_quasiIso_iff f).mp hf
  have := map_quasiIso R D f
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((functor R D).map f)))

def derivedFunctor : PD R D ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (functor R D ⋙ DerivedCategory.Q) (inverts_quasiIso R D) (q R D)

def derivedFactors : q R D ⋙ derivedFunctor R D ≅ functor R D ⋙ DerivedCategory.Q :=
  Localization.fac (functor R D ⋙ DerivedCategory.Q) (inverts_quasiIso R D) (q R D)

def derivedHomologyIso (n : ℤ) :
    derivedFunctor R D ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ≅
      HomologicalComplexUpToQuasiIso.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D))
        (-(n : ZMod D)) := by
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))
  let F := derivedFunctor R D ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let G := HomologicalComplexUpToQuasiIso.homologyFunctor (ModuleCat.{u} R)
    (.down (ZMod D)) (-(n : ZMod D))
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
    (.down (ZMod D)) (-(n : ZMod D))
  let e : q R D ⋙ F ≅ H :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedFactors R D) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (functor R D)
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n) ≪≫
      homologyIso R D n
  letI : Localization.Lifting (q R D) W H F := ⟨e⟩
  letI : Localization.Lifting (q R D) W H G :=
    ⟨HomologicalComplexUpToQuasiIso.homologyFunctorFactors (ModuleCat.{u} R)
      (.down (ZMod D)) (-(n : ZMod D))⟩
  exact Localization.liftNatIso (q R D) W H H F G (Iso.refl _)

theorem derived_homology_iso (n : ℤ) : Nonempty
    (derivedFunctor R D ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ≅
      HomologicalComplexUpToQuasiIso.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D))
        (-(n : ZMod D))) :=
  ⟨derivedHomologyIso R D n⟩

instance : (derivedFunctor R D).CommShift ℤ := by
  letI : Localization.Lifting (q R D)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D)))
      (Unroll.functor R D ⋙ DerivedCategory.Q) (derivedFunctor R D) :=
    ⟨derivedFactors R D⟩
  exact Functor.commShiftOfLocalization (q R D)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))) ℤ
    (Unroll.functor R D ⋙ DerivedCategory.Q) (derivedFunctor R D)
end DerivedFunctor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [Ring R] (D : ℕ)

lemma down_rel (n : ℤ) : (ComplexShape.down (ZMod D)).Rel
    (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D)) := by
  simp [ComplexShape.down_Rel]

lemma up_rel (n : ℤ) : (ComplexShape.up ℤ).Rel n (n+1) := rfl

def coneXIso {P Q : PC R D} (f : P ⟶ Q) (n : ℤ) :
    (obj R D (homotopyCofiber f)).X n ≅
      (CochainComplex.mappingCone (map R D f)).X n :=
  homotopyCofiber.XIsoBiprod f (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D)) (down_rel D n) ≪≫
    (homotopyCofiber.XIsoBiprod (map R D f) n (n+1) (up_rel n)).symm

@[simp] lemma obj_d (P : PC R D) (n : ℤ) :
    (obj R D P).d n (n+1) = P.d (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D)) := by
  simp [obj, CochainComplex.of_d]

@[simp] lemma map_f {P Q : PC R D} (f : P ⟶ Q) (n : ℤ) :
    (map R D f).f n = f.f (-(n : ZMod D)) := rfl

lemma coneXIso_comm {P Q : PC R D} (f : P ⟶ Q) (n : ℤ) :
    (coneXIso R D f n).hom ≫ (CochainComplex.mappingCone (map R D f)).d n (n+1) =
      (obj R D (homotopyCofiber f)).d n (n+1) ≫ (coneXIso R D f (n+1)).hom := by
  simp only [coneXIso]
  erw [obj_d]
  change
    ((homotopyCofiber.XIsoBiprod f (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D))
      (down_rel D n)).hom ≫
      (homotopyCofiber.XIsoBiprod (map R D f) n (n+1) (up_rel n)).inv) ≫
        homotopyCofiber.d (map R D f) n (n+1) =
    homotopyCofiber.d f (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D)) ≫
      ((homotopyCofiber.XIsoBiprod f (-((n+1 : ℤ) : ZMod D))
        (-((n+1+1 : ℤ) : ZMod D)) (down_rel D (n+1))).hom ≫
        (homotopyCofiber.XIsoBiprod (map R D f) (n+1) (n+1+1) (up_rel (n+1))).inv)
  apply (cancel_epi (homotopyCofiber.XIsoBiprod f (-(n : ZMod D))
    (-((n+1 : ℤ) : ZMod D)) (down_rel D n)).inv).mp
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  apply biprod.hom_ext'
  all_goals
    apply homotopyCofiber.ext_to_X (map R D f) (n+1) (n+1+1) (up_rel (n+1))
  all_goals
    simp [homotopyCofiber.inlX_d_assoc f _ _ _ (down_rel D n) (down_rel D (n+1))]
    repeat erw [Category.assoc]
    try erw [homotopyCofiber.inlX_XIsoBiprod_hom_assoc f _ _ (down_rel D (n+1))]
    try erw [homotopyCofiber.inrX_XIsoBiprod_hom_assoc f _ _ (down_rel D (n+1))]
    try erw [homotopyCofiber.inl_XIsoBiprod_inv_assoc (map R D f) (n+1) n (up_rel n)]
    try erw [homotopyCofiber.inr_XIsoBiprod_inv_assoc (map R D f) (n+1) n (up_rel n)]
    try erw [homotopyCofiber.inl_XIsoBiprod_inv_assoc (map R D f) (n+1+1) (n+1) (up_rel (n+1))]
    try erw [homotopyCofiber.inr_XIsoBiprod_inv_assoc (map R D f) (n+1+1) (n+1) (up_rel (n+1))]
    simp [homotopyCofiber.inlX_d_assoc (map R D f) n (n+1) (n+1+1) (up_rel n) (up_rel (n+1))]
  all_goals simp [obj]
  all_goals
    erw [homotopyCofiber.inl_XIsoBiprod_inv_assoc (map R D f)
      (n+1+1) (n+1) (up_rel (n+1))]
  · erw [homotopyCofiber.inrX_fstX, homotopyCofiber.inlX_fstX]
    simp
    erw [Limits.comp_zero, add_zero]
  · erw [homotopyCofiber.inlX_sndX, homotopyCofiber.inrX_sndX]
    simp
    rfl

def coneIso {P Q : PC R D} (f : P ⟶ Q) :
    obj R D (homotopyCofiber f) ≅ CochainComplex.mappingCone (map R D f) :=
  Hom.isoOfComponents (coneXIso R D f) (by
    intro i j hij
    have hj : i+1 = j := hij
    subst j
    exact coneXIso_comm R D f i)

lemma coneIso_inr {P Q : PC R D} (f : P ⟶ Q) :
    map R D (homotopyCofiber.inr f) ≫ (coneIso R D f).hom =
      CochainComplex.mappingCone.inr (map R D f) := by
  apply Hom.ext
  funext n
  change homotopyCofiber.inrX f (-(n : ZMod D)) ≫ (coneXIso R D f n).hom =
    homotopyCofiber.inrX (map R D f) n
  change homotopyCofiber.inrX f (-(n : ZMod D)) ≫
    ((homotopyCofiber.XIsoBiprod f (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D)) (down_rel D n)).hom ≫
      (homotopyCofiber.XIsoBiprod (map R D f) n (n+1) (up_rel n)).inv) = _
  erw [← Category.assoc, homotopyCofiber.inrX_XIsoBiprod_hom]
  exact homotopyCofiber.inr_XIsoBiprod_inv (map R D f) (n+1) n (up_rel n)

theorem cone_iso {P Q : PC R D} (f : P ⟶ Q) :
    ∃ e : obj R D (homotopyCofiber f) ≅ CochainComplex.mappingCone (map R D f),
      map R D (homotopyCofiber.inr f) ≫ e.hom = CochainComplex.mappingCone.inr (map R D f) :=
  ⟨coneIso R D f, coneIso_inr R D f⟩

end HahnWilson.Unroll

end

end OAI
