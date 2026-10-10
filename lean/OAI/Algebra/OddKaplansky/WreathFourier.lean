import OAI.Algebra.OddKaplansky.Fourier

namespace OAI

universe contextUniverse1

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5

section

namespace OddKaplansky.CharacterIdempotents
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {A : Type portUniverse2} {G : Type portUniverse3} [Field K] [Group A] [Fintype A] [Group G]
lemma pushed_conjugate (f : A →* G) (χ ψ : A →* Kˣ) (σ : A ≃* A) (g : G)
    (hg : ∀ a, g * f a * g⁻¹ = f (σ a)) (hχ : ∀ a, ψ (σ a) = χ a) :
    MonoidAlgebra.single g 1 * pushed f χ * MonoidAlgebra.single g⁻¹ 1 = pushed f ψ := by
  rw [pushed_eq_sum, pushed_eq_sum]
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  calc
    _ = ∑ a : A, MonoidAlgebra.single (f (σ a)) ((ψ (σ a) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one, hg, hχ]
    _ = _ := Equiv.sum_comp σ.toEquiv (fun a : A =>
      (MonoidAlgebra.single (f a) ((ψ a : K)⁻¹) : MonoidAlgebra K G))
end
end OddKaplansky.CharacterIdempotents

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse4} {H : Type portUniverse5} [Field K] [Group H] [sectionInstance9 : Fintype H]
variable (M : ℕ) [sectionInstance10 : NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
abbrev Base := H → Fourier.C M
abbrev Wreath := RegularWreathProduct (Fourier.C M) H

def shift (h : H) : Base (H := H) M ≃* Base (H := H) M where
  toFun a x := a (h⁻¹ * x)
  invFun a x := a (h * x)
  left_inv a := by funext x; simp
  right_inv a := by funext x; simp
  map_mul' _ _ := rfl
@[simp] lemma shift_apply
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h : H) (a : Base (H := H) M) (x : H) : shift M h a x = a (h⁻¹*x) := rfl
@[simp] lemma shift_one
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : shift (H := H) M 1 = MulEquiv.refl _ := by ext a x; simp
@[simp] lemma shift_mul
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h g : H) (a : Base (H := H) M) : shift M (h*g) a = shift M h (shift M g a) := by
  funext x
  simp [mul_assoc]
lemma character_shift (h : H) (lmb a : Base (H := H) M) :
    Fourier.character M hζ (shift M h lmb) (shift M h a) = Fourier.character M hζ lmb a := by
  simp only [Fourier.character_apply, shift_apply]
  congr 1
  apply congrArg Multiplicative.ofAdd
  exact Equiv.sum_comp (Equiv.mulLeft h⁻¹) (fun x : H => (lmb x).toAdd * (a x).toAdd)
def base : Base (H := H) M →* Wreath (H := H) M where
  toFun a := ⟨a,1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp
@[simp] lemma base_left
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (a : Base (H := H) M) : (base M a).left = a := rfl
@[simp] lemma base_right
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (a : Base (H := H) M) : (base M a).right = 1 := rfl
def top : H →* Wreath (H := H) M := RegularWreathProduct.inl
lemma base_injective
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : Function.Injective (base (H := H) M) := by intro a b he; exact congrArg RegularWreathProduct.left he
lemma top_injective
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : Function.Injective (top (H := H) M) := by intro a b he; exact congrArg RegularWreathProduct.right he
lemma top_conjugate
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h : H) (a : Base (H := H) M) :
    top M h * base M a * (top M h)⁻¹ = base M (shift M h a) := by
  ext <;> simp [top, base]
lemma normal_form
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (g : Wreath (H := H) M) : g = base M g.left * top M g.right := by
  ext <;> simp [base, top]
def projector (lmb : Base (H := H) M) : MonoidAlgebra K (Wreath (H := H) M) :=
  CharacterIdempotents.pushed (base M) (Fourier.character M hζ lmb)
def topElt (h : H) : MonoidAlgebra K (Wreath (H := H) M) := MonoidAlgebra.single (top M h) 1
lemma projector_idempotent (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0) (lmb : Base (H := H) M) :
    projector M hζ lmb * projector M hζ lmb = projector M hζ lmb :=
  CharacterIdempotents.pushed_idempotent _ _ hc
lemma projector_orthogonal (lmb μ : Base (H := H) M) (hne : lmb ≠ μ) :
    projector M hζ lmb * projector M hζ μ = 0 :=
  CharacterIdempotents.pushed_orthogonal _ _ _ (fun he => hne (Fourier.character_injective M hζ he))
lemma projector_ne_zero (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0) (lmb : Base (H := H) M) :
    projector M hζ lmb ≠ 0 := CharacterIdempotents.pushed_ne_zero _ (base_injective M) _ hc
lemma translated (h : H) (lmb : Base (H := H) M) :
    topElt M h * projector M hζ lmb * topElt M h⁻¹ = projector M hζ (shift M h lmb) := by
  simp only [topElt, map_inv]
  exact CharacterIdempotents.pushed_conjugate _ _ _ (shift M h) _ (top_conjugate M h)
    (character_shift M hζ h lmb)
lemma sum_projector (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0) :
    ∑ lmb : Base (H := H) M, projector M hζ lmb = 1 := by
  have he := congrArg (MonoidAlgebra.mapDomainAlgHom K K (base (H := H) M)) (Fourier.sum_projector M hζ hc)
  simpa only [map_sum, map_one, projector, CharacterIdempotents.pushed] using he
end
end OddKaplansky.WreathFourier

end

end OAI
