import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormCRT
import OAI.NumberTheory.Ostmann.Construction.DiagonalTransform

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open Construction

def smallProduct (xs : List SmallSlot) : ℕ := (xs.map SmallSlot.value).prod

def coefficientDenominator (D : ℕ) (outerU xs : List SmallSlot) (p : ℕ) : ℕ :=
  D*smallProduct outerU*(smallProduct xs/p)

theorem small_dvd_smallProduct {xs : List SmallSlot} {z : SmallSlot} (hz : z∈xs) :
    z.value∣smallProduct xs := by
  apply List.dvd_prod
  exact List.mem_map.mpr ⟨z,hz,rfl⟩

theorem diagonal_denominator_split (D P q : ℕ) (outerU xs : List SmallSlot)
    (z : SmallSlot) (hz : z∈xs) :
    (D*halfProduct P outerU)*(halfProduct q xs/z.value)=
      P*q*coefficientDenominator D outerU xs z.value := by
  have hd := small_dvd_smallProduct hz
  unfold smallProduct at hd
  unfold halfProduct coefficientDenominator smallProduct
  rw [Nat.mul_div_assoc q hd]
  ring

theorem diagonal_modFraction_split {p : ℕ} [Fact p.Prime]
    (D P q : ℕ) (outerU xs : List SmallSlot) (v : ℤ)
    (hp : p∣smallProduct xs) :
    modFraction p v ((D*halfProduct P outerU)*(halfProduct q xs/p))=
      ((v:ZMod p)/(coefficientDenominator D outerU xs p:ZMod p))/
        ((P:ZMod p)*(q:ZMod p)) := by
  have he : (D*halfProduct P outerU)*(halfProduct q xs/p)=
      P*q*coefficientDenominator D outerU xs p := by
    unfold smallProduct at hp
    unfold halfProduct coefficientDenominator smallProduct
    rw [Nat.mul_div_assoc q hp]
    ring
  rw [he]
  simp only [modFraction,Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
  ring

def coefficientUnit {p : ℕ} [Fact p.Prime] (v : ℤ) (A : ℕ)
    (hv : IsUnit (v:ZMod p)) (hA : IsUnit (A:ZMod p)) : (ZMod p)ˣ :=
  Units.mk0 ((v:ZMod p)/(A:ZMod p)) (div_ne_zero hv.ne_zero hA.ne_zero)

@[simp] theorem coefficientUnit_coe {p : ℕ} [Fact p.Prime] (v : ℤ) (A : ℕ)
    (hv : IsUnit (v:ZMod p)) (hA : IsUnit (A:ZMod p)) :
    (coefficientUnit v A hv hA : ZMod p)=(v:ZMod p)/(A:ZMod p) := rfl

theorem diagonal_factor_eq_transformFactor {p : ℕ} [Fact p.Prime]
    (d : Decomposition) (D P q : ℕ) (outerU xs : List SmallSlot) (v : ℤ)
    (hp : p∣smallProduct xs) (hv : IsUnit (v:ZMod p))
    (hA : IsUnit (coefficientDenominator D outerU xs p:ZMod p))
    (hq : IsUnit (q:ZMod p)) :
    ‖residueTransform d p
      (modFraction p v ((D*halfProduct P outerU)*(halfProduct q xs/p)))‖^2=
      transformFactor (residueTransform d p)
        (coefficientUnit v (coefficientDenominator D outerU xs p) hv hA)
        hq.unit (P:ZMod p) := by
  rw [diagonal_modFraction_split D P q outerU xs v hp]
  simp only [transformFactor,coefficientUnit_coe,IsUnit.unit_spec]

theorem coprime_prod_div_of_pairwise {xs : List ℕ} (hxs : xs.Pairwise Nat.Coprime)
    {p : ℕ} (hp : p∈xs) (hp0 : 0<p) : (xs.prod/p).Coprime p := by
  induction xs with
  | nil => simp at hp
  | cons a xs ih =>
    obtain ⟨ha,hxs⟩ := List.pairwise_cons.mp hxs
    rcases List.mem_cons.mp hp with hpa | hp
    · subst a
      rw [List.prod_cons,Nat.mul_div_cancel_left _ hp0]
      exact Nat.coprime_list_prod_left_iff.mpr (fun n hn => (ha n hn).symm)
    · rw [List.prod_cons,Nat.mul_div_assoc a (List.dvd_prod hp)]
      exact (ha p hp).mul_left (ih hxs hp)

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
