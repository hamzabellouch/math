import OAI.NumberTheory.Ostmann.Conclusion.RegularNorm
import OAI.NumberTheory.Ostmann.Construction.ActualRows

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open scoped BigOperators
open Conclusion Construction
variable {p : ℕ} [Fact p.Prime]

def transformFactor (g : ZMod p→ℂ) (a y : (ZMod p)ˣ) (x : ZMod p) : ℝ :=
  ‖g ((a:ZMod p)/(x*(y:ZMod p)))‖^2

theorem transformFactor_sum (g : ZMod p→ℂ) (hg0 : g 0=0)
    (hgnorm : ∑x:ZMod p,‖g x‖^2=(p:ℝ)) (a y : (ZMod p)ˣ) :
    ∑x:ZMod p,transformFactor g a y x=(p:ℝ) := by
  rw [←sum_units_eq_sum (transformFactor g a y) (by simp [transformFactor,hg0])]
  have he (x : (ZMod p)ˣ) : transformFactor g a y x =
      ‖g (((a*y⁻¹)*x⁻¹:(ZMod p)ˣ):ZMod p)‖^2 := by
    simp only [transformFactor,div_eq_mul_inv,mul_inv_rev,Units.val_mul,Units.val_inv_eq_inv_val,mul_assoc]
  simp_rw [he]
  exact prime_unit_norm_sum g hg0 hgnorm (a*y⁻¹)

def unitFactor (x : ZMod p) : ℝ := if IsUnit x then 1 else 0

theorem unitFactor_sum : ∑x:ZMod p,unitFactor x=(p-1:ℕ) := by
  classical
  rw [←sum_units_eq_sum unitFactor (by simp [unitFactor])]
  simp only [unitFactor,Units.isUnit,ite_true,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [ZMod.card_units_eq_totient,Nat.totient_prime (Fact.out : p.Prime)]

theorem transformFactor_average (g : ZMod p→ℂ) (hg0 : g 0=0)
    (hgnorm : ∑x:ZMod p,‖g x‖^2=(p:ℝ)) (a : (ZMod p)ˣ) :
    (∑z:ZMod p×(ZMod p)ˣ,transformFactor g a z.2 z.1)/
      Fintype.card (ZMod p×(ZMod p)ˣ)=1 := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [transformFactor_sum g hg0 hgnorm]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,ZMod.card,Nat.cast_mul]
  have hp : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : (Fintype.card (ZMod p)ˣ:ℝ)≠0 := by positivity
  field_simp

theorem unitFactor_average :
    (∑z:ZMod p×(ZMod p)ˣ,unitFactor z.1)/Fintype.card (ZMod p×(ZMod p)ˣ)=
      ((p-1:ℕ):ℝ)/p := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [unitFactor_sum]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,ZMod.card,Nat.cast_mul]
  have hp : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : (Fintype.card (ZMod p)ˣ:ℝ)≠0 := by positivity
  field_simp

theorem actual_transformFactor_average (d : Decomposition) (a : (ZMod p)ˣ) :
    (∑z:ZMod p×(ZMod p)ˣ,transformFactor (residueTransform d p) a z.2 z.1)/
      Fintype.card (ZMod p×(ZMod p)ˣ)=1 :=
  transformFactor_average _ (by simp [residueTransform_eq,Supply.additiveTransform_zero])
    (residueTransform_sq_sum d p (Fact.out : p.Prime)) a

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
