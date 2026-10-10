import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Shift.ShiftedHom

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace ArExplicit.TriangleRecurrence

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (T : Triangle C) (hT : T ∈ distTriang C) (Y : C)
include hT

theorem connecting_surjective (h : ∀ f : T.obj₂ ⟶ Y, f = 0) :
    Function.Surjective (fun f : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y => T.mor₃ ≫ f) := by
  intro f
  obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f (h _)
  exact ⟨g, hg.symm⟩

theorem connecting_injective (h : ∀ f : T.obj₂⟦(1 : ℤ)⟧ ⟶ Y, f = 0) :
    Function.Injective (fun f : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y => T.mor₃ ≫ f) := by
  intro f g hfg
  change T.mor₃ ≫ f = T.mor₃ ≫ g at hfg
  have hz : T.mor₃ ≫ (f - g) = 0 := by
    rw [Preadditive.comp_sub, hfg, sub_self]
  obtain ⟨a, ha⟩ := T.rotate.rotate.yoneda_exact₂
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) (f - g) hz
  have ha0 : a = 0 := h a
  have hf : f - g = 0 := by
    rw [ha, ha0]
    exact Limits.comp_zero
  exact sub_eq_zero.mp hf

theorem connecting_bijective
    (h₀ : ∀ f : T.obj₂ ⟶ Y, f = 0)
    (h₁ : ∀ f : T.obj₂⟦(1 : ℤ)⟧ ⟶ Y, f = 0) :
    Function.Bijective (fun f : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y => T.mor₃ ≫ f) :=
  ⟨connecting_injective T hT Y h₁, connecting_surjective T hT Y h₀⟩

def connectingEquiv
    (h₀ : ∀ f : T.obj₂ ⟶ Y, f = 0)
    (h₁ : ∀ f : T.obj₂⟦(1 : ℤ)⟧ ⟶ Y, f = 0) :
    (T.obj₁⟦(1 : ℤ)⟧ ⟶ Y) ≃+ (T.obj₃ ⟶ Y) :=
  AddEquiv.ofBijective
    ({ toFun f := T.mor₃ ≫ f
       map_zero' := Limits.comp_zero
       map_add' f g := by simp only [Preadditive.comp_add] } :
        (T.obj₁⟦(1 : ℤ)⟧ ⟶ Y) →+ (T.obj₃ ⟶ Y))
    (connecting_bijective T hT Y h₀ h₁)

omit hT in

def shiftedMapEquiv (X Z : C) (a b c : ℤ) (h : b + a = c) :
    ShiftedHom X Z b ≃ (X⟦a⟧ ⟶ Z⟦c⟧) :=
  (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C a)).homEquiv.trans
    (((shiftFunctorAdd' C b a c h).symm.app Z).homToEquiv)

omit hT in

theorem degreeThreeComposition_bijective (X I : C)
    (a : X⟦(2 : ℤ)⟧ ⟶ I) (b : I ⟶ X) (d : X ⟶ (X⟦(2 : ℤ)⟧)⟦(1 : ℤ)⟧)
    (hd : Triangle.mk a b d ∈ distTriang C) (n : ℤ)
    (h₀ : ∀ f : I ⟶ X⟦n + 3⟧, f = 0)
    (h₁ : ∀ f : I⟦(1 : ℤ)⟧ ⟶ X⟦n + 3⟧, f = 0) :
    Function.Bijective (fun β : ShiftedHom X X n =>
      ShiftedHom.comp (a := (3 : ℤ)) (b := n)
        (d ≫ (shiftFunctorAdd' C (2 : ℤ) 1 3 (by decide)).inv.app X) β rfl) := by
  let e := shiftedMapEquiv X X 3 n (n + 3) rfl
  let e' := ((shiftFunctorAdd' C (2 : ℤ) 1 3 (by decide)).app X).homFromEquiv
    (Z := X⟦n + 3⟧)
  have h := (connecting_bijective (Triangle.mk a b d) hd (X⟦n + 3⟧) h₀ h₁).comp
    (e'.bijective.comp e.bijective)
  convert! h using 1
  ext β
  simp only [Function.comp_apply, e, e', shiftedMapEquiv, Equiv.trans_apply,
    ShiftedHom.comp, Category.assoc]
  rfl

end ArExplicit.TriangleRecurrence

end

end OAI
