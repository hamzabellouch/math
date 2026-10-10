import OAI.NumberTheory.Ostmann.Arithmetic.ResidueHaar

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeSquareResidueLaw
attribute [local instance] Classical.propDecidable

variable (p : ℕ) [Fact p.Prime]

def lift (x u : ZMod p) : ZMod (p^2) := ((x.val + p*u.val : ℕ) : ZMod (p^2))

theorem lift_lt (x u : ZMod p) : x.val + p*u.val < p^2 := by
  have hx := x.val_lt
  have hu := Nat.mul_le_mul_left p (Nat.succ_le_of_lt u.val_lt)
  nlinarith

@[simp] theorem lift_val (x u : ZMod p) : (lift p x u).val = x.val+p*u.val :=
  ZMod.val_natCast_of_lt (lift_lt p x u)

theorem quotient_lt (z : ZMod (p^2)) : z.val / p < p := by
  apply (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr
  simpa only [pow_two] using z.val_lt

def ringLiftEquiv : ZMod p × ZMod p ≃ ZMod (p^2) where
  toFun z := lift p z.1 z.2
  invFun z := ((z.val : ZMod p),((z.val / p : ℕ):ZMod p))
  left_inv z := by
    apply Prod.ext
    · simp [lift_val,Nat.cast_add,Nat.cast_mul]
    · change (((lift p z.1 z.2).val / p : ℕ) : ZMod p) = z.2
      rw [lift_val,Nat.add_mul_div_left _ _ (Fact.out : p.Prime).pos,
        Nat.div_eq_of_lt z.1.val_lt,Nat.zero_add,ZMod.natCast_zmod_val]
  right_inv z := by
    change lift p (z.val:ZMod p) ((z.val/p:ℕ):ZMod p) = z
    unfold lift
    rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt (quotient_lt p z),
      Nat.mod_add_div,ZMod.natCast_zmod_val]

@[simp] theorem ringLiftEquiv_apply (z : ZMod p × ZMod p) :
    ringLiftEquiv p z = lift p z.1 z.2 := rfl

@[simp] theorem ringLiftEquiv_symm_fst (z : ZMod (p^2)) :
    ((ringLiftEquiv p).symm z).1 = (z.val:ZMod p) := rfl

@[simp] theorem ringLiftEquiv_symm_snd (z : ZMod (p^2)) :
    ((ringLiftEquiv p).symm z).2 = ((z.val/p:ℕ):ZMod p) := rfl

theorem lift_isUnit_iff (x u : ZMod p) : IsUnit (lift p x u) ↔ IsUnit x := by
  rw [lift,ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (by decide)]
  have hbase : IsUnit x ↔ ¬ p ∣ x.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [ZMod.isUnit_iff_coprime,Nat.coprime_comm,
      (Fact.out : p.Prime).coprime_iff_not_dvd]
  rw [hbase]
  exact not_congr (Nat.dvd_add_iff_left (dvd_mul_right p u.val)).symm

def unitsSubtypeEquiv (M : Type*) [Monoid M] : Mˣ ≃ {x : M // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := by apply Units.ext; exact IsUnit.unit_spec _
  right_inv x := by apply Subtype.ext; exact x.property.unit_spec

def unitLiftEquiv : (ZMod p)ˣ × ZMod p ≃ (ZMod (p^2))ˣ :=
  (((unitsSubtypeEquiv (ZMod p)).prodCongr (Equiv.refl (ZMod p))).trans
    ((Equiv.prodSubtypeFstEquivSubtypeProd).symm.trans
      ((ringLiftEquiv p).subtypeEquiv (fun z => (lift_isUnit_iff p z.1 z.2).symm)))).trans
        (unitsSubtypeEquiv (ZMod (p^2))).symm

@[simp] theorem unitLiftEquiv_coe (z : (ZMod p)ˣ × ZMod p) :
    (unitLiftEquiv p z : ZMod (p^2)) = lift p (z.1:ZMod p) z.2 := by
  exact IsUnit.unit_spec _

end Ostmann.Arithmetic.PrimeSquareResidueLaw

end

end OAI
