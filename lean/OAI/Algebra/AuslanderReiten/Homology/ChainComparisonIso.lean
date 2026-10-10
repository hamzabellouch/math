import Mathlib.Algebra.Homology.HomologicalComplex

namespace OAI

namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] {P Q R : ChainComplex C ℕ}

theorem comparisonIso_trans (e : P ≅ Q) (f : Q ≅ R) (m n : ℕ)
    (p : P.X m ⟶ P.X n) (q : Q.X m ⟶ Q.X n) (r : R.X m ⟶ R.X n)
    (he : p ≫ e.hom.f n = e.hom.f m ≫ q)
    (hf : q ≫ f.hom.f n = f.hom.f m ≫ r) :
    p ≫ (e ≪≫ f).hom.f n = (e ≪≫ f).hom.f m ≫ r := by
  change p ≫ (e.hom.f n ≫ f.hom.f n) = (e.hom.f m ≫ f.hom.f m) ≫ r
  rw [← Category.assoc, he, Category.assoc, hf, ← Category.assoc]

end ArExplicit

end OAI
