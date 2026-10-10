import OAI.Algebra.AuslanderReiten.Homology.TriangleHomExact

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit.TriangleGradedSequence

universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (X : C)

abbrev Bottom (n : ℤ) := X ⟶ (T⟦n⟧).obj₁
abbrev Middle (n : ℤ) := X ⟶ (T⟦n⟧).obj₂
abbrev Top (n : ℤ) := X ⟶ (T⟦n⟧).obj₃

def nextIso (n : ℤ) : T⟦n + 1⟧ ≅ (T⟦n⟧)⟦(1 : ℤ)⟧ :=
  (CategoryTheory.shiftFunctorAdd' (Triangle C) n 1 (n + 1) rfl).app T

def first (n : ℤ) : Bottom T X n →ₗ[k] Middle T X n :=
  Linear.rightComp k X (T⟦n⟧).mor₁

def second (n : ℤ) : Middle T X n →ₗ[k] Top T X n :=
  Linear.rightComp k X (T⟦n⟧).mor₂

def connecting (n : ℤ) : Top T X n →ₗ[k] Bottom T X (n + 1) :=
  Linear.rightComp k X ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁)

variable (hT : T ∈ distTriang C)
include hT

theorem exact_middle (n : ℤ) :
    LinearMap.range (first k T X n) = LinearMap.ker (second k T X n) :=
  shiftedTriangleHom_middle_exact k T hT X n

theorem exact_top (n : ℤ) :
    LinearMap.range (second k T X n) = LinearMap.ker (connecting k T X n) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change (g ≫ (T⟦n⟧).mor₂) ≫ ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁) = 0
    erw [Category.assoc, ← Category.assoc (T⟦n⟧).mor₂, comp_distTriang_mor_zero₂₃ _ (T.shift_distinguished hT n)]
    erw [Limits.zero_comp, Limits.comp_zero]
  · intro hf
    have hz : f ≫ (T⟦n⟧).mor₃ = 0 := by
      apply (cancel_mono (nextIso T n).inv.hom₁).mp
      change f ≫ ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁) = 0 at hf
      erw [Category.assoc, Limits.zero_comp]
      exact hf
    obtain ⟨g, hg⟩ := (T⟦n⟧).coyoneda_exact₃ (T.shift_distinguished hT n) f hz
    exact ⟨g, hg.symm⟩

omit hT [Limits.HasZeroObject C] [Pretriangulated C] in
private theorem next_first (n : ℤ) :
    ((T⟦n⟧)⟦(1 : ℤ)⟧).mor₁ = -((T⟦n⟧).mor₁⟦(1 : ℤ)⟧') := by
  simp [Triangle.shiftFunctor, Triangle.shiftFunctor_eq]
  rfl

theorem exact_next (n : ℤ) :
    LinearMap.range (connecting k T X n) = LinearMap.ker (first k T X (n + 1)) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change (g ≫ ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁)) ≫ (T⟦n + 1⟧).mor₁ = 0
    erw [Category.assoc g, Category.assoc (T⟦n⟧).mor₃, ← (nextIso T n).inv.comm₁]
    erw [next_first, Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc (T⟦n⟧).mor₃,
      comp_distTriang_mor_zero₃₁ _ (T.shift_distinguished hT n)]
    erw [Limits.zero_comp, neg_zero, Limits.comp_zero]
  · intro hf
    have hz : (f ≫ (nextIso T n).hom.hom₁) ≫ ((T⟦n⟧)⟦(1 : ℤ)⟧).mor₁ = 0 := by
      erw [Category.assoc, ← (nextIso T n).hom.comm₁, ← Category.assoc]
      change ((first k T X (n + 1)) f) ≫ _ = 0
      rw [show first k T X (n + 1) f = 0 from hf]
      simp
    erw [next_first, Preadditive.comp_neg, neg_eq_zero] at hz
    obtain ⟨g, hg⟩ := (T⟦n⟧).coyoneda_exact₁ (T.shift_distinguished hT n)
      (f ≫ (nextIso T n).hom.hom₁) hz
    refine ⟨g, ?_⟩
    change g ≫ ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁) = f
    erw [← Category.assoc, ← hg, Category.assoc]
    have hi : (nextIso T n).hom.hom₁ ≫ (nextIso T n).inv.hom₁ = 𝟙 _ := by
      exact congrArg (fun m => m.hom₁) (nextIso T n).hom_inv_id
    erw [hi, Category.comp_id]

end ArExplicit.TriangleGradedSequence

end

end OAI
