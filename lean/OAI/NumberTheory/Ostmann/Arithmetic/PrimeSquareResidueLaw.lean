import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeSquareResidueLawBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeSquareResidueLaw
open scoped BigOperators
open ResidueHaar HistoryCRTIntegration
attribute [local instance] Classical.propDecidable

def pairDigitsEquiv (A B C D : Type*) : (A × B) × (C × D) ≃ (A × C) × (B × D) where
  toFun z := ((z.1.1,z.2.1),(z.1.2,z.2.2))
  invFun z := ((z.1.1,z.2.1),(z.1.2,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem average_pair {A B : Type*} [Fintype A] [Fintype B] (F : A × B → ℂ) :
    average F = average (fun a => average (fun b => F (a,b))) := by
  simp only [average,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,
    Fintype.sum_prod_type,← Finset.mul_sum]
  ring

variable (p : ℕ) [Fact p.Prime]

def unitPairLiftEquiv : UnitPair p × (ZMod p × ZMod p) ≃ UnitPair (p^2) :=
  (pairDigitsEquiv _ _ _ _).trans ((unitLiftEquiv p).prodCongr (unitLiftEquiv p))

def mixedPairLiftEquiv : MixedPair p × (ZMod p × ZMod p) ≃ MixedPair (p^2) :=
  (pairDigitsEquiv _ _ _ _).trans ((ringLiftEquiv p).prodCongr (unitLiftEquiv p))

@[simp] theorem unitPairLiftEquiv_fst (z : UnitPair p × (ZMod p × ZMod p)) :
    ((unitPairLiftEquiv p z).1:ZMod (p^2)) = lift p (z.1.1:ZMod p) z.2.1 :=
  unitLiftEquiv_coe p _

@[simp] theorem unitPairLiftEquiv_snd (z : UnitPair p × (ZMod p × ZMod p)) :
    ((unitPairLiftEquiv p z).2:ZMod (p^2)) = lift p (z.1.2:ZMod p) z.2.2 :=
  unitLiftEquiv_coe p _

@[simp] theorem mixedPairLiftEquiv_fst (z : MixedPair p × (ZMod p × ZMod p)) :
    (mixedPairLiftEquiv p z).1 = lift p z.1.1 z.2.1 := rfl

@[simp] theorem mixedPairLiftEquiv_snd (z : MixedPair p × (ZMod p × ZMod p)) :
    ((mixedPairLiftEquiv p z).2:ZMod (p^2)) = lift p (z.1.2:ZMod p) z.2.2 :=
  unitLiftEquiv_coe p _

omit [Fact p.Prime] in
theorem lift_eq_intCast [Fact p.Prime] (x u : ZMod p) :
    lift p x u = (((x.val:ℤ)+(p:ℤ)*(u.val:ℤ):ℤ):ZMod (p^2)) := by
  simp only [lift,Nat.cast_add,Nat.cast_mul,Int.cast_add,Int.cast_mul,Int.cast_natCast]

def reduction : ZMod (p^2) →+* ZMod p :=
  ZMod.castHom (by simpa only [pow_two] using dvd_mul_right p p) (ZMod p)

@[simp] theorem lift_reduction (x u : ZMod p) : reduction p (lift p x u) = x := by
  simp only [lift,map_natCast,Nat.cast_add,Nat.cast_mul,map_add,map_mul,
    ZMod.natCast_self,zero_mul,add_zero,ZMod.natCast_zmod_val]

theorem ringLiftEquiv_base_reduction (z : ZMod (p^2)) :
    ((ringLiftEquiv p).symm z).1 = reduction p z := by
  have h := lift_reduction p ((ringLiftEquiv p).symm z).1
    ((ringLiftEquiv p).symm z).2
  rw [show lift p ((ringLiftEquiv p).symm z).1 ((ringLiftEquiv p).symm z).2 = z from
    (ringLiftEquiv p).apply_symm_apply z] at h
  exact h.symm

@[simp] theorem unitLiftEquiv_reduction (z : (ZMod p)ˣ × ZMod p) :
    reduction p (unitLiftEquiv p z : ZMod (p^2)) = (z.1:ZMod p) := by
  rw [unitLiftEquiv_coe,lift_reduction]

theorem unit_pair_average (F : UnitPair (p^2) → ℂ) :
    average F = average (fun b : UnitPair p =>
      average (fun u : ZMod p × ZMod p => F (unitPairLiftEquiv p (b,u)))) :=
  (average_equiv (unitPairLiftEquiv p) F).symm.trans (average_pair _)

theorem mixed_pair_average (F : MixedPair (p^2) → ℂ) :
    average F = average (fun b : MixedPair p =>
      average (fun u : ZMod p × ZMod p => F (mixedPairLiftEquiv p (b,u)))) :=
  (average_equiv (mixedPairLiftEquiv p) F).symm.trans (average_pair _)

theorem unit_joint_average (F : UnitPair p × (ZMod p × ZMod p) → ℂ) :
    average (fun z : UnitPair (p^2) => F ((unitPairLiftEquiv p).symm z)) =
      average (fun b : UnitPair p => average (fun u : ZMod p × ZMod p => F (b,u))) :=
  (average_equiv (unitPairLiftEquiv p).symm F).trans (average_pair F)

theorem mixed_joint_average (F : MixedPair p × (ZMod p × ZMod p) → ℂ) :
    average (fun z : MixedPair (p^2) => F ((mixedPairLiftEquiv p).symm z)) =
      average (fun b : MixedPair p => average (fun u : ZMod p × ZMod p => F (b,u))) :=
  (average_equiv (mixedPairLiftEquiv p).symm F).trans (average_pair F)

end Ostmann.Arithmetic.PrimeSquareResidueLaw

end

end OAI
