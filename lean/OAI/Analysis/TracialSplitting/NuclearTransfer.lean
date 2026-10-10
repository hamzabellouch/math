import OAI.Analysis.TracialSplitting.ConditionalSplitting

namespace OAI

universe uR uS


section

noncomputable section

universe v

namespace Pureness

namespace NuclearLift

variable (B : Type) [CStarAlgebra B]

instance : Star (ULift.{v} B) := ⟨fun x => ⟨star x.down⟩⟩

instance : StarRing (ULift.{v} B) where
  star_involutive x := by apply ULift.down_injective; exact star_star x.down
  star_mul x y := by apply ULift.down_injective; exact star_mul x.down y.down
  star_add x y := by apply ULift.down_injective; exact star_add x.down y.down

instance : StarModule ℂ (ULift.{v} B) where
  star_smul c x := by apply ULift.down_injective; exact star_smul c x.down

instance : CStarRing (ULift.{v} B) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le x.down

instance : CStarAlgebra (ULift.{v} B) where

end NuclearLift

namespace CStarAlgebraNorm

variable {R : Type uR} {S : Type uS} [Ring R] [StarRing R] [Algebra ℂ R]
  [Ring S] [StarRing S] [Algebra ℂ S]

def comapEquiv (p : CStarAlgebraNorm S) (e : R ≃⋆ₐ[ℂ] S) : CStarAlgebraNorm R where
  toFun x := p.toAlgebraNorm (e x)
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact map_add_le_add p.toAlgebraNorm (e x) (e y)
  neg' x := by simp
  mul_le' x y := by rw [map_mul]; exact map_mul_le_mul p.toAlgebraNorm (e x) (e y)
  eq_zero_of_map_eq_zero' x hx := e.injective (by simpa using p.toAlgebraNorm.eq_zero_of_map_eq_zero' (e x) hx)
  smul' scalar element := by rw [map_smul, map_smul_eq_mul]
  cstar x := by
    change p.toAlgebraNorm (e (star x*x)) = p.toAlgebraNorm (e x)*p.toAlgebraNorm (e x)
    rw [map_mul,map_star]
    exact p.cstar (e x)

lemma comapEquiv_injective (e : R ≃⋆ₐ[ℂ] S) :
    Function.Injective (fun p : CStarAlgebraNorm S => p.comapEquiv e) := by
  intro p q h
  have he : p.toAlgebraNorm = q.toAlgebraNorm := by
    apply AlgebraNorm.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    exact congrArg (fun t : CStarAlgebraNorm R => t.toAlgebraNorm x) h
  cases p
  cases q
  cases he
  rfl

end CStarAlgebraNorm

open scoped TensorProduct

theorem IsNuclear.small {A : Type} [CStarAlgebra A] (hA : IsNuclear.{0,v} A) :
    IsNuclear.{0,0} A := by
  intro B instB
  let E : A ⊗[ℂ] ULift.{v} B ≃ₐ[ℂ] A ⊗[ℂ] B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[ℂ] A) ULift.algEquiv
  have hstar : ∀ x, E (star x) = star (E x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy => simp only [star_add,map_add,hx,hy]
  let e : A ⊗[ℂ] ULift.{v} B ≃⋆ₐ[ℂ] A ⊗[ℂ] B := StarAlgEquiv.ofAlgEquiv E hstar
  exact ⟨fun p q => CStarAlgebraNorm.comapEquiv_injective e ((hA (ULift.{v} B)).elim _ _)⟩

end Pureness

end

end

end OAI
