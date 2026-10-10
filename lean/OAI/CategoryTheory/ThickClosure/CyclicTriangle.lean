import OAI.CategoryTheory.ThickClosure.UnrollDerived

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.CyclicTriangle
section ConeTriangles
open CategoryTheory CategoryTheory.Limits HomologicalComplex CategoryTheory.Pretriangulated
open HahnWilson.Unroll HahnWilson.CyclicShift
universe u
variable (R : Type u) [Ring R] (D : ℕ)

lemma next_rel (i : ZMod D) : (ComplexShape.down (ZMod D)).Rel i (i-1) := by
  simp [ComplexShape.down_Rel]

def delta {P Q : PC R D} (f : P ⟶ Q) :
    homotopyCofiber f ⟶ (cyclicShift R D 1).obj P where
  f i := -homotopyCofiber.fstX f i (i-(1 : ℤ)) (by simp [ComplexShape.down_Rel])
  comm' := by
    intro i j hij
    have hj : j = i - (1 : ℤ) := by
      change j+1=i at hij
      simpa only [Int.cast_one] using (eq_sub_iff_add_eq.mpr hij)
    subst j
    change (-homotopyCofiber.fstX f i (i-(1 : ℤ)) _) ≫
      ((1 : ℤ).negOnePow • P.d (i-(1 : ℤ)) (i-(1 : ℤ)-(1 : ℤ))) =
      homotopyCofiber.d f i (i-(1 : ℤ)) ≫
        (-homotopyCofiber.fstX f (i-(1 : ℤ)) (i-(1 : ℤ)-(1 : ℤ)) _)
    simp only [Int.negOnePow_one, Units.neg_smul, one_smul,
      Preadditive.comp_neg, Preadditive.neg_comp, neg_neg]
    rw [homotopyCofiber.d_fstX f _ _ _ (by simp [ComplexShape.down_Rel])
      (by simp [ComplexShape.down_Rel])]
    simp

def triangle {P Q : PC R D} (f : P ⟶ Q) : Triangle (PC R D) :=
  Triangle.mk f (homotopyCofiber.inr f) (delta R D f)

open CochainComplex.HomComplex

lemma fstX_transport {P Q : PC R D} (f : P ⟶ Q) (i j k : ZMod D)
    (h : j = k) (hij : (ComplexShape.down (ZMod D)).Rel i j)
    (hik : (ComplexShape.down (ZMod D)).Rel i k) :
    homotopyCofiber.fstX f i j hij ≫ (P.XIsoOfEq h).hom =
      homotopyCofiber.fstX f i k hik := by
  subst k
  simp

lemma ordinary_delta_f {A B : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : A ⟶ B) (n : ℤ) :
    (CochainComplex.mappingCone.triangle f).mor₃.f n =
      -homotopyCofiber.fstX f n (n+1) rfl := by
  apply homotopyCofiber.ext_from_X f (n+1) n rfl
  · erw [Preadditive.comp_neg, homotopyCofiber.inlX_fstX]
  · erw [Preadditive.comp_neg, homotopyCofiber.inrX_fstX, neg_zero]

lemma coneIso_delta {P Q : PC R D} (f : P ⟶ Q) :
    (Unroll.functor R D).map (delta R D f) ≫
      ((Unroll.functor R D).commShiftIso (1 : ℤ)).hom.app P =
        (coneIso R D f).hom ≫ (CochainComplex.mappingCone.triangle (Unroll.map R D f)).mor₃ := by
  apply Hom.ext
  funext n
  change (-homotopyCofiber.fstX f (-(n : ZMod D)) (-(n : ZMod D)-(1 : ℤ)) _) ≫
      (P.XIsoOfEq (by simp only [Int.cast_add, Int.cast_one]; abel)).hom =
    (coneXIso R D f n).hom ≫
      (CochainComplex.mappingCone.triangle (Unroll.map R D f)).mor₃.f n
  erw [Preadditive.neg_comp, fstX_transport R D, ordinary_delta_f R,
    Preadditive.comp_neg]
  congr 1
  change homotopyCofiber.fstX f (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D)) _ =
    ((homotopyCofiber.XIsoBiprod f (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D))
      (down_rel D n)).hom ≫
      (homotopyCofiber.XIsoBiprod (Unroll.map R D f) n (n+1) (up_rel n)).inv) ≫
        homotopyCofiber.fstX (Unroll.map R D f) n (n+1) rfl
  simp [homotopyCofiber.fstX]
  · erw [Category.assoc, Iso.inv_hom_id_assoc]
    rfl

def unrollTriangleIso {P Q : PC R D} (f : P ⟶ Q) :
    (Unroll.functor R D).mapTriangle.obj (triangle R D f) ≅
      CochainComplex.mappingCone.triangle (Unroll.map R D f) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (coneIso R D f)
    (by change Unroll.map R D f ≫ 𝟙 _ = 𝟙 _ ≫ Unroll.map R D f; simp)
    (by
      change Unroll.map R D (homotopyCofiber.inr f) ≫ (coneIso R D f).hom =
        𝟙 _ ≫ CochainComplex.mappingCone.inr (Unroll.map R D f)
      simpa only [Category.id_comp] using coneIso_inr R D f)
    (by
      change ((Unroll.functor R D).map (delta R D f) ≫
        ((Unroll.functor R D).commShiftIso (1 : ℤ)).hom.app P) ≫
        (CategoryTheory.shiftFunctor _ (1 : ℤ)).map (𝟙 ((Unroll.functor R D).obj P)) =
          (coneIso R D f).hom ≫ (CochainComplex.mappingCone.triangle (Unroll.map R D f)).mor₃
      exact (congrArg (fun a => ((Unroll.functor R D).map (delta R D f) ≫
          ((Unroll.functor R D).commShiftIso (1 : ℤ)).hom.app P) ≫ a)
          ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ)).map_id _)).trans
        ((Category.comp_id _).trans (coneIso_delta R D f)))

end ConeTriangles
open CategoryTheory CategoryTheory.Limits HomologicalComplex CategoryTheory.Pretriangulated
open HahnWilson.Unroll HahnWilson.CyclicShift
universe u v w
variable (R : Type u) [Ring R] (D : ℕ)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]

instance : NatTrans.CommShift (derivedFactors R D).hom ℤ := by
  let : Localization.Lifting (q R D)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D)))
      (Unroll.functor R D ⋙ DerivedCategory.Q) (derivedFunctor R D) :=
    ⟨derivedFactors R D⟩
  exact NatTrans.commShift_iso_hom_of_localization (q R D)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))) ℤ
    (Unroll.functor R D ⋙ DerivedCategory.Q) (derivedFunctor R D)

def distinguished : Set (Triangle (PD R D)) :=
  { T | ∃ (P Q : PC R D) (f : P ⟶ Q),
    Nonempty (T ≅ (q R D).mapTriangle.obj (triangle R D f)) }

lemma map_distinguished (T : Triangle (PD R D)) (hT : T ∈ distinguished R D) :
    (derivedFunctor R D).mapTriangle.obj T ∈ distTriang _ := by
  obtain ⟨P, Q, f, ⟨e⟩⟩ := hT
  apply isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished (Unroll.map R D f))
  exact ((derivedFunctor R D).mapTriangle.mapIso e) ≪≫
    ((Functor.mapTriangleCompIso (q R D) (derivedFunctor R D)).symm.app _) ≪≫
    ((Functor.mapTriangleIso (derivedFactors R D)).app _) ≪≫
    ((Functor.mapTriangleCompIso (Unroll.functor R D) DerivedCategory.Q).app _) ≪≫
    (DerivedCategory.Q.mapTriangle.mapIso (unrollTriangleIso R D f))
end HahnWilson.CyclicTriangle

end

end OAI
