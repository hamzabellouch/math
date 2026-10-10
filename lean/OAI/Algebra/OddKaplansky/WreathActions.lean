import OAI.Algebra.OddKaplansky.MatrixActions

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3

section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {H : Type portUniverse2} {R : Type portUniverse3} [Field K] [Group H] [Fintype H] [sectionInstance18 : Fintype R]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (lmb : R → Base (H := H) M)
local notation "φ" => MatrixUnits.lift (K := K) (freeUnit M hζ lmb)

def diagonal (a : Base (H := H) M) (r : R) : Matrix H H K :=
  Matrix.diagonal (fun x => (Fourier.character M hζ (shift M x (lmb r)) a : K))

lemma top_represents (h : H) : MatrixActions.Represents φ (topElt M h) (fun _ : R => TranslationMatrix.matrix (K := K) h) := by
  intro F
  constructor
  · rw [MatrixUnits.lift_apply,MatrixUnits.lift_apply]
    simp only [Finset.mul_sum,mul_smul_comm,topElt_freeUnit]
    apply Finset.sum_congr rfl
    intro r _
    simp only [Pi.mul_apply,TranslationMatrix.mul_apply]
    have he := Equiv.sum_comp (Equiv.mulLeft h) (fun x : H => ∑ y : H, F r (h⁻¹*x) y • freeUnit M hζ lmb (r,x,y))
    simpa only [Equiv.coe_mulLeft,inv_mul_cancel_left] using he
  · rw [MatrixUnits.lift_apply,MatrixUnits.lift_apply]
    simp only [Finset.sum_mul,smul_mul_assoc,freeUnit_topElt]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro x _
    simp only [Pi.mul_apply,TranslationMatrix.right_mul_apply]
    have he := Equiv.sum_comp (Equiv.mulLeft h⁻¹) (fun y : H => F r x (h*y) • freeUnit M hζ lmb (r,x,y))
    simpa only [Equiv.coe_mulLeft,mul_inv_cancel_left] using he

lemma base_represents (a : Base (H := H) M) : MatrixActions.Represents φ (baseElt M a) (diagonal M hζ lmb a) := by
  intro F
  constructor
  · simp only [MatrixUnits.lift_apply,Finset.mul_sum,mul_smul_comm,baseElt_freeUnit,smul_smul,Pi.mul_apply,diagonal,Matrix.diagonal_mul,mul_comm]
  · simp only [MatrixUnits.lift_apply,Finset.sum_mul,smul_mul_assoc,freeUnit_baseElt,smul_smul,Pi.mul_apply,diagonal,Matrix.mul_diagonal]

lemma diagonal_inv
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (a : Base (H := H) M) (r : R) :
    diagonal M hζ lmb a r * diagonal M hζ lmb a⁻¹ r = 1 := by
  rw [diagonal,diagonal,Matrix.diagonal_mul_diagonal]
  simp only [map_inv,Units.val_inv_eq_inv_val,mul_inv_cancel₀ (Units.ne_zero _),Matrix.diagonal_one]

lemma diagonal_inv' (a : Base (H := H) M) (r : R) :
    diagonal M hζ lmb a⁻¹ r * diagonal M hζ lmb a r = 1 := by simpa only [inv_inv] using diagonal_inv M hζ lmb a⁻¹ r

lemma conjugate_represents (a : Base (H := H) M) (h : H) :
    MatrixActions.Represents φ (baseElt M a * topElt M h * baseElt M a⁻¹)
      (fun r => diagonal M hζ lmb a r * TranslationMatrix.matrix h * diagonal M hζ lmb a⁻¹ r) :=
  MatrixActions.represents_mul φ (MatrixActions.represents_mul φ (base_represents M hζ lmb a) (top_represents M hζ lmb h)) (base_represents M hζ lmb a⁻¹)
end
end OddKaplansky.WreathFourier

end

end OAI
