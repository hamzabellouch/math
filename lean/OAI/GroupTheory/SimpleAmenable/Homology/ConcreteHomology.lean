import Mathlib

namespace OAI

section

section

open CategoryTheory Limits HomologicalComplex
namespace ConcreteHomology

universe u
variable {R : Type u} [CommRing R]
abbrev c := ComplexShape.down ℕ
abbrev CC := ChainComplex (ModuleCat.{u} R) ℕ
variable (K L : CC (R:=R)) (n : ℕ)
def S := K.sc' (n+1) n (n-1)
abbrev Cycles := LinearMap.ker ((K.d n (n-1)).hom)
abbrev boundary := (S K n).moduleCatToCycles
abbrev H := Cycles K n ⧸ LinearMap.range (boundary K n)
def π : Cycles K n →ₗ[R] H K n := (LinearMap.range (boundary K n)).mkQ

@[simp] lemma π_eq_zero (x : Cycles K n) : π K n x=0 ↔ ∃ y, boundary K n y=x :=
  Submodule.Quotient.mk_eq_zero _

lemma π_surjective : Function.Surjective (π K n) :=
  Submodule.mkQ_surjective (LinearMap.range (boundary K n))

noncomputable def sFunctor : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj T := T.moduleCatLeftHomologyData.H
  map f := ShortComplex.leftHomologyMap' f _ _
  map_id _ := ShortComplex.leftHomologyMap'_id _
  map_comp _ _ := ShortComplex.leftHomologyMap'_comp _ _ _ _ _

instance : (sFunctor (R:=R)).Additive where
  map_add {X Y} f g := by
    exact ShortComplex.leftHomologyMap'_add X.moduleCatLeftHomologyData Y.moduleCatLeftHomologyData

noncomputable def sIso : ShortComplex.homologyFunctor (ModuleCat.{u} R) ≅ sFunctor (R:=R) :=
  NatIso.ofComponents (fun T => T.moduleCatHomologyIso) (fun f =>
    (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality f _ _).symm)

noncomputable def functor (n : ℕ) : CC (R:=R) ⥤ ModuleCat.{u} R :=
  shortComplexFunctor' _ c (n+1) n (n-1) ⋙ sFunctor

instance : (functor (R:=R) n).Additive where
  map_add {X Y} f g := by
    change ShortComplex.leftHomologyMap' ((shortComplexFunctor' (ModuleCat.{u} R) c (n+1) n (n-1)).map (f+g)) (S X n).moduleCatLeftHomologyData (S Y n).moduleCatLeftHomologyData = _
    have h : (shortComplexFunctor' (ModuleCat.{u} R) c (n+1) n (n-1)).map (f+g) =
        (shortComplexFunctor' (ModuleCat.{u} R) c (n+1) n (n-1)).map f +
        (shortComplexFunctor' (ModuleCat.{u} R) c (n+1) n (n-1)).map g := by
      ext <;> rfl
    rw [h]
    exact ShortComplex.leftHomologyMap'_add (S X n).moduleCatLeftHomologyData
      (S Y n).moduleCatLeftHomologyData

lemma prev (n : ℕ) : c.prev n=n+1 := c.prev_eq' rfl
lemma next (n : ℕ) : c.next n=n-1 := by
  cases n with
  | zero => exact c.next_eq_self' 0 (by intro k; change ¬k+1=0; omega)
  | succ n => exact c.next_eq' rfl

noncomputable def naturalIso (n : ℕ) : homologyFunctor (ModuleCat.{u} R) c n ≅ functor n :=
  homologyFunctorIso' _ c (n+1) n (n-1) (prev n) (next n) ≪≫
    Functor.isoWhiskerLeft _ sIso

noncomputable def iso : K.homology n ≅ ModuleCat.of R (H K n) := (naturalIso n).app K

variable {K L}
noncomputable def cyclesMap (f : K ⟶ L) (n : ℕ) : Cycles K n →ₗ[R] Cycles L n :=
  (ShortComplex.cyclesMap' ((shortComplexFunctor' _ c (n+1) n (n-1)).map f)
    (S K n).moduleCatLeftHomologyData (S L n).moduleCatLeftHomologyData).hom

@[simp] lemma cyclesMap_val (f : K ⟶ L) (n : ℕ) (x : Cycles K n) :
    (cyclesMap f n x).val=(f.f n).hom x := by
  have h := ShortComplex.cyclesMap'_i ((shortComplexFunctor' _ c (n+1) n (n-1)).map f)
    (S K n).moduleCatLeftHomologyData (S L n).moduleCatLeftHomologyData
  exact congrArg (fun g : ModuleCat.of R (Cycles K n) ⟶ L.X n => g.hom x) h

@[simp] lemma map_π (f : K ⟶ L) (n : ℕ) (x : Cycles K n) :
    ((functor n).map f).hom (π K n x)=π L n (cyclesMap f n x) := by
  have h := ShortComplex.leftHomologyπ_naturality' ((shortComplexFunctor' _ c (n+1) n (n-1)).map f)
    (S K n).moduleCatLeftHomologyData (S L n).moduleCatLeftHomologyData
  exact congrArg (fun g : ModuleCat.of R (Cycles K n) ⟶ ModuleCat.of R (H L n) => g.hom x) h

end ConcreteHomology

end

section
open CategoryTheory Limits HomologicalComplex
namespace ConeCoordinates

universe u
variable {R : Type u} [CommRing R]
open ConcreteHomology
variable {F G : CC (R:=R)} (φ : F ⟶ G)
noncomputable abbrev C := homotopyCofiber φ
noncomputable abbrev left (n : ℕ) : F.X n ⟶ (C φ).X (n+1) := homotopyCofiber.inlX φ n (n+1) rfl
noncomputable abbrev right (n : ℕ) : G.X n ⟶ (C φ).X n := homotopyCofiber.inrX φ n
noncomputable abbrev fst (n : ℕ) : (C φ).X (n+1) ⟶ F.X n := homotopyCofiber.fstX φ (n+1) n rfl
noncomputable abbrev snd (n : ℕ) : (C φ).X n ⟶ G.X n := homotopyCofiber.sndX φ n
lemma zero_next : ¬ c.Rel 0 (c.next 0) := by change ¬ c.next 0+1=0; omega
@[simp] lemma fst_left (n : ℕ) (x : F.X n) : fst φ n (left φ n x)=x := by
  exact congrArg (fun f : F.X n ⟶ F.X n => f x) (homotopyCofiber.inlX_fstX φ n (n+1) rfl)
@[simp] lemma snd_right (n : ℕ) (x : G.X n) : snd φ n (right φ n x)=x := by
  exact congrArg (fun f : G.X n ⟶ G.X n => f x) (homotopyCofiber.inrX_sndX φ n)
@[simp] lemma fst_right (n : ℕ) (x : G.X (n+1)) : fst φ n (right φ (n+1) x)=0 := by
  exact congrArg (fun f : G.X (n+1) ⟶ F.X n => f x) (homotopyCofiber.inrX_fstX φ (n+1) n rfl)
@[simp] lemma snd_left (n : ℕ) (x : F.X n) : snd φ (n+1) (left φ n x)=0 := by
  exact congrArg (fun f : F.X n ⟶ G.X (n+1) => f x) (homotopyCofiber.inlX_sndX φ n (n+1) rfl)
lemma ext {n : ℕ} {x y : (C φ).X (n+1)} (hfst : fst φ n x=fst φ n y)
    (hsnd : snd φ (n+1) x=snd φ (n+1) y) : x=y := by
  have hrel : c.Rel (n+1) n := rfl
  apply (homotopyCofiber.XIsoBiprod φ (n+1) n hrel).toLinearEquiv.injective
  apply (ModuleCat.biprodIsoProd (F.X n) (G.X (n+1))).toLinearEquiv.injective
  apply Prod.ext
  · exact hfst
  · change (biprod.snd : F.X n ⊞ G.X (n+1) ⟶ G.X (n+1)) ((homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom x) =
      (biprod.snd : F.X n ⊞ G.X (n+1) ⟶ G.X (n+1)) ((homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom y)
    have he : (homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom ≫ biprod.snd = snd φ (n+1) := by
      apply homotopyCofiber.ext_from_X φ n (n+1) hrel
      · simp only [homotopyCofiber.inlX_XIsoBiprod_hom_assoc,biprod.inl_snd,
          homotopyCofiber.inlX_sndX]
      · simp only [homotopyCofiber.inrX_XIsoBiprod_hom_assoc,biprod.inr_snd,
          homotopyCofiber.inrX_sndX]
    change ((homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom ≫ biprod.snd) x =
      ((homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom ≫ biprod.snd) y
    rw [he]; exact hsnd
lemma ext_zero {x y : (C φ).X 0} (h : snd φ 0 x=snd φ 0 y) : x=y :=
  (homotopyCofiber.XIso φ 0 zero_next).toLinearEquiv.injective h
lemma decomp (n : ℕ) (x : (C φ).X (n+1)) :
    left φ n (fst φ n x)+right φ (n+1) (snd φ (n+1) x)=x := by
  apply ext φ
  · simp only [map_add,fst_left φ n _,fst_right φ n _,add_zero]
  · simp only [map_add,snd_left φ n _,snd_right φ (n+1) _,zero_add]
lemma decomp_zero (x : (C φ).X 0) : right φ 0 (snd φ 0 x)=x := by
  apply ext_zero φ; exact snd_right φ 0 _
lemma d_snd (n : ℕ) (x : (C φ).X (n+1)) :
    snd φ n ((C φ).d (n+1) n x)=φ.f n (fst φ n x)+G.d (n+1) n (snd φ (n+1) x) := by
  exact congrArg (fun f : (C φ).X (n+1) ⟶ G.X n => f x)
    (homotopyCofiber.d_sndX φ (n+1) n rfl)
lemma d_fst (n : ℕ) (x : (C φ).X (n+2)) :
    fst φ n ((C φ).d (n+2) (n+1) x) = -F.d (n+1) n (fst φ (n+1) x) := by
  exact congrArg (fun f : (C φ).X (n+2) ⟶ F.X n => f x)
    (homotopyCofiber.d_fstX φ (n+2) (n+1) n rfl rfl)
lemma d_right (n m : ℕ) (x : G.X n) :
    (C φ).d n m (right φ n x)=right φ m (G.d n m x) := by
  exact congrArg (fun f : G.X n ⟶ (C φ).X m => f x)
    (homotopyCofiber.inrX_d φ n m)
lemma d_left (n : ℕ) (x : F.X (n+1)) :
    (C φ).d (n+2) (n+1) (left φ (n+1) x) =
      -left φ n (F.d (n+1) n x)+right φ (n+1) (φ.f (n+1) x) := by
  apply ext φ
  · rw [d_fst φ n, fst_left φ (n+1)]
    simp only [map_add,map_neg,fst_left φ n _,fst_right φ n _,add_zero]
  · rw [d_snd φ (n+1),fst_left φ (n+1),snd_left φ (n+1)]
    simp only [map_add,map_neg,map_zero,snd_left φ n _,snd_right φ (n+1) _,neg_zero,zero_add,add_zero]
lemma d_left_zero (x : F.X 0) : (C φ).d 1 0 (left φ 0 x)=right φ 0 (φ.f 0 x) := by
  apply ext_zero φ
  rw [d_snd φ 0,fst_left φ 0,snd_left φ 0,map_zero,add_zero,snd_right φ 0]
lemma d_left_cycle (n : ℕ) (x : Cycles F n) :
    (C φ).d (n+1) n (left φ n x)=right φ n (φ.f n x) := by
  cases n with
  | zero => exact d_left_zero φ x
  | succ n =>
    rw [d_left]
    have hx : F.d (n+1) n x=0 := x.property
    rw [hx,map_zero,neg_zero,zero_add]
end ConeCoordinates

end

end

end OAI
