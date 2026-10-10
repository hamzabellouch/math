import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionCoverExt
import OAI.Algebra.AuslanderReiten.Ext.NatCubicExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u

private theorem cubicAugmentedSquare {C : Type*} [Category C]
    {P₃ P₀ Q₃ Q₀ B S N : C}
    (φ₃ : P₃ ⟶ Q₃) (φ₀ : P₀ ⟶ Q₀) (p : P₃ ⟶ P₀) (q : Q₃ ⟶ Q₀)
    (π : P₀ ⟶ B) (ρ : Q₀ ⟶ N) (e : B ⟶ S) (j : S ⟶ N) (f : P₃ ⟶ S)
    (hφ : φ₀ ≫ ρ = π ≫ (e ≫ j)) (hc : p ≫ φ₀ = φ₃ ≫ q)
    (hf : f = p ≫ π ≫ e) :
    φ₃ ≫ (q ≫ ρ) = f ≫ j := by
  rw [← Category.assoc, ← hc, Category.assoc, hφ, hf]
  simp only [Category.assoc]

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {B S N : ModuleCat.{u} R}

theorem resolutionExt_cubic_conjugate
    (P : ProjectiveResolution B) (Q : ProjectiveResolution N)
    (e : B ≅ S) (j : S ≅ N)
    (φ : ProjectiveResolution.Hom P Q (e.hom ≫ j.hom))
    (p : P.complex.X 3 ⟶ P.complex.X 0)
    (q : ∀ n : ℕ, Q.complex.X (n+3) ⟶ Q.complex.X n)
    (hq : ∀ n, q (n+1) ≫ Q.complex.d (n+1) n =
      Q.complex.d (n+4) (n+3) ≫ q n)
    (f : P.complex.X 3 ⟶ S) (hf : P.complex.d 4 3 ≫ f = 0)
    (hfc : f = p ≫ P.π.f 0 ≫ e.hom)
    (hc : p ≫ φ.hom.f 0 = φ.hom.f 3 ≫ q 0) :
    selfExtIso (k := k) j 3 ((Ext.mk₀ e.inv).comp
      (P.extMk f 4 rfl hf) (zero_add _)) =
      ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q q hq) := by
  rw [ResolutionProducts.natCubic_endExt_eq]
  apply resolutionExt_cover_conjugate P Q e j φ 3 f (q 0 ≫ Q.π.f 0) hf
    (ResolutionProducts.natCubic_augmented_cycle Q q hq)
  exact cubicAugmentedSquare _ _ _ _ _ _ _ _ _ φ.hom_f_zero_comp_π_f_zero hc hfc

end ArExplicit

end

end OAI
