import OAI.Algebra.OddKaplansky.WreathFourier

namespace OAI

universe contextUniverse1

universe portUniverse1 portUniverse2

section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [sectionInstance11 : Fintype H]
variable (M : ℕ) [sectionInstance12 : NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

@[simp] lemma shift_inverse_shift
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h : H) (a : Base (H := H) M) :
    shift M h⁻¹ (shift M h a) = a := by funext x; simp
@[simp] lemma shift_shift_inverse
    {H : Type contextUniverse1}
    [Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h : H) (a : Base (H := H) M) :
    shift M h (shift M h⁻¹ a) = a := by funext x; simp

lemma character_shift_right (h : H) (lmb a : Base (H := H) M) :
    Fourier.character M hζ lmb (shift M h a) = Fourier.character M hζ (shift M h⁻¹ lmb) a := by
  have he := character_shift M hζ h (shift M h⁻¹ lmb) a
  simpa only [shift_shift_inverse] using he

def rhoGroup : Wreath (H := H) M →*
    Matrix (Base (H := H) M) (Base (H := H) M) (MonoidAlgebra K H) where
  toFun g := Matrix.of fun x y => if x = shift M g.right y then
    MonoidAlgebra.single g.right (Fourier.character M hζ x g.left : K) else 0
  map_one' := by
    apply Matrix.ext
    intro x y
    simp [Matrix.one_apply, MonoidAlgebra.one_def]
  map_mul' g k := by
    apply Matrix.ext
    intro x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (shift M k.right y)]
    · simp only [Matrix.of_apply, RegularWreathProduct.mul_left,
        RegularWreathProduct.mul_right, shift_mul, ite_true]
      change (if x = shift M g.right (shift M k.right y) then
        MonoidAlgebra.single (g.right*k.right)
          (Fourier.character M hζ x (g.left * shift M g.right k.left) : K) else 0) = _
      by_cases he : x = shift M g.right (shift M k.right y)
      · rw [ite_eq_left he, ite_eq_left he, MonoidAlgebra.single_mul_single]
        congr 1
        rw [map_mul, Units.val_mul, character_shift_right, he, shift_inverse_shift]
      · simp [he]
    · intro z _ hzy
      simp [hzy]
    · simp

def rho : MonoidAlgebra K (Wreath (H := H) M) →ₐ[K]
    Matrix (Base (H := H) M) (Base (H := H) M) (MonoidAlgebra K H) :=
  MonoidAlgebra.lift K _ _ (rhoGroup M hζ)

lemma rho_single (g : Wreath (H := H) M) (c : K) (x y : Base (H := H) M) :
    rho M hζ (MonoidAlgebra.single g c) x y =
    if x = shift M g.right y then MonoidAlgebra.single g.right
      (c * (Fourier.character M hζ x g.left : K)) else 0 := by
  rw [rho, MonoidAlgebra.lift_single]
  change c • (if x = shift M g.right y then
    MonoidAlgebra.single g.right (Fourier.character M hζ x g.left : K) else 0) = _
  split_ifs <;> simp

lemma rho_top (h : H) (x y : Base (H := H) M) : rho M hζ (topElt M h) x y =
    if x = shift M h y then MonoidAlgebra.single h 1 else 0 := by
  rw [topElt, rho_single]
  simp [top]

end
end OddKaplansky.WreathFourier

end

end OAI
