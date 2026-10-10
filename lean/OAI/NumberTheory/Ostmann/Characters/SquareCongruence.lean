import OAI.NumberTheory.Ostmann.Arithmetic.CompositeSquareRootsDensity
import OAI.NumberTheory.Ostmann.Arithmetic.ResidueHaar

namespace OAI

noncomputable section
namespace Ostmann.Characters

theorem transfer_congruence_iff_square {G : Type*} [CommGroup G]
    (v w CL CR t x y : G) (ht : x*y=t) :
    v*CR*y=w*CL*x ↔ x^2=(w*CL)⁻¹*(v*CR*t) := by
  rw [eq_inv_mul_iff_mul_eq]
  constructor
  · intro h
    calc
      (w*CL)*x^2 = (w*CL*x)*x := by simp only [pow_two, mul_assoc]
      _ = (v*CR*y)*x := by rw [h]
      _ = v*CR*(x*y) := by ac_rfl
      _ = v*CR*t := by rw [ht]
  · intro h
    apply mul_right_cancel (b:=x)
    calc
      (v*CR*y)*x = v*CR*(x*y) := by ac_rfl
      _ = v*CR*t := by rw [ht]
      _ = (w*CL)*x^2 := h.symm
      _ = (w*CL*x)*x := by simp only [pow_two, mul_assoc]

def constrainedProductEquiv {G : Type*} [CommGroup G] (v w CL CR t : G) :
    {z : G × G // z.1*z.2=t ∧ v*CR*z.2=w*CL*z.1} ≃
      {x : G // x^2=(w*CL)⁻¹*(v*CR*t)} where
  toFun z := ⟨z.val.1, (transfer_congruence_iff_square v w CL CR t
    z.val.1 z.val.2 z.property.1).mp z.property.2⟩
  invFun x := ⟨(x.val,x.val⁻¹*t), by
    refine ⟨by simp, ?_⟩
    exact (transfer_congruence_iff_square v w CL CR t x.val (x.val⁻¹*t)
      (by simp)).mpr x.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change z.val.1⁻¹*t=z.val.2
      calc
        _ = z.val.1⁻¹*(z.val.1*z.val.2) :=
          congrArg (fun a => z.val.1⁻¹*a) z.property.1.symm
        _ = _ := by simp
  right_inv x := rfl

theorem constrainedProduct_card_le (n : ℕ) [NeZero n]
    (v w CL CR t : (ZMod n)ˣ) :
    Nat.card {z : (ZMod n)ˣ × (ZMod n)ˣ //
      z.1*z.2=t ∧ v*CR*z.2=w*CL*z.1} ≤ 2*n.divisors.card := by
  rw [Nat.card_congr (constrainedProductEquiv v w CL CR t)]
  exact Arithmetic.card_unit_square_fiber_le_two_divisors n _

theorem constrainedProduct_density_le_rpow (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∀ [NeZero n],
      ∀ v w CL CR t : (ZMod n)ˣ,
      (Nat.card {z : (ZMod n)ˣ × (ZMod n)ˣ //
        z.1*z.2=t ∧ v*CR*z.2=w*CL*z.1} : ℝ) /
      Nat.card {z : (ZMod n)ˣ × (ZMod n)ˣ // z.1*z.2=t} ≤
        C*(n:ℝ)^(ε-1) := by
  obtain ⟨C,hC,hbound⟩ := Arithmetic.unit_square_fiber_density_le_rpow ε hε
  refine ⟨C,hC,fun n _ v w CL CR t => ?_⟩
  rw [Nat.card_congr (constrainedProductEquiv v w CL CR t),
    Arithmetic.ResidueHaar.fixedProduct_card]
  exact hbound n _

end Ostmann.Characters

end

end OAI
