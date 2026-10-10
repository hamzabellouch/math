import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorBimap
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftSign

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

abbrev rightTerm (p : ℤ) := ScalarLeftModule k Aᵐᵒᵖ (Q.X p)
abbrev leftTerm (q : ℤ) := ScalarLeftModule k A (Z.X q)
abbrev term (p q : ℤ) := Tensor k A (rightTerm k A Q p) (leftTerm k A Z q)

/-- The balanced map for actual maps between terms of the two input complexes. -/
def map {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') (g : Z.X q ⟶ Z.X q') :
    term k A Q Z p q →ₗ[k] term k A Q Z p' q' :=
  bimap (k := k)
    (M := rightTerm k A Q p) (M' := rightTerm k A Q p')
    (N := leftTerm k A Z q) (N' := leftTerm k A Z q') f.hom g.hom

@[simp] theorem map_comp {p p' p'' q q' q'' : ℤ}
    (f : Q.X p ⟶ Q.X p') (f' : Q.X p' ⟶ Q.X p'')
    (g : Z.X q ⟶ Z.X q') (g' : Z.X q' ⟶ Z.X q'') :
    (map k A Q Z f' g').comp (map k A Q Z f g) = map k A Q Z (f ≫ f') (g ≫ g') :=
  bimap_comp _ _ _ _

@[simp] theorem map_zero_left {p p' q q' : ℤ} (g : Z.X q ⟶ Z.X q') :
    map k A Q Z (0 : Q.X p ⟶ Q.X p') g = 0 := bimap_zero_left _

@[simp] theorem map_zero_right {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') :
    map k A Q Z f (0 : Z.X q ⟶ Z.X q') = 0 := bimap_zero_right _

/-- The column at right degree p, including the standard total-complex sign (-1)^p. -/
def column (p : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ :=
  (((fixedTensorFunctor k A (rightTerm k A Q p)).mapHomologicalComplex (.up ℤ)).obj Z)⟦-p⟧

@[simp] theorem column_d (p n m : ℤ) :
    ((column k A Q Z p).d n m).hom =
      (-p).negOnePow • map k A Q Z (𝟙 (Q.X p)) (Z.d (n + -p) (m + -p)) := by
  apply BalancedTensor.ext
  intro x y
  rfl

/-- Horizontal tensor maps reindex the unchanged left factor along the total degree. -/
def horizontal (n p p' : ℤ) (h : p+1=p') :
    term k A Q Z p (n + -p) →ₗ[k] term k A Q Z p' ((n+1) + -p') :=
  map k A Q Z (Q.d p p') (eqToHom (congrArg Z.X (by omega)))

theorem horizontal_square (n p p' p'' : ℤ) (h : p+1=p') (h' : p'+1=p'') :
    (horizontal k A Q Z (n+1) p' p'' h').comp (horizontal k A Q Z n p p' h) = 0 := by
  unfold horizontal
  rw [map_comp,Q.d_comp_d,map_zero_left]
end LittleFinitistic.ComplexTensor

end

end OAI
