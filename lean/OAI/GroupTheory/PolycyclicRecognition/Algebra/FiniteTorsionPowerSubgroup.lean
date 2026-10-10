import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIntegerReductions
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeCyclicExtension
import Mathlib.GroupTheory.Torsion

namespace OAI

/-! # A characteristic torsion-free subgroup of finite index in an abelian group

When the torsion subgroup is finite, its order annihilates it. The subgroup of
that power is torsion-free, and finite reduction gives its finite index.
-/

noncomputable section
namespace PolycyclicRecognition
variable (A : Type) [CommGroup A]

def abelianPowerReduction (n : ℕ) :
    A →* Multiplicative (Additive A ⧸ integerMultiples (Additive A) n) where
  toFun a := Multiplicative.ofAdd ((integerMultiples (Additive A) n).mkQ (Additive.ofMul a))
  map_one' := by change (integerMultiples (Additive A) n).mkQ 0 = 0; exact map_zero _
  map_mul' a b := congrArg Multiplicative.ofAdd
    ((integerMultiples (Additive A) n).mkQ.map_add (Additive.ofMul a) (Additive.ofMul b))

theorem abelianPowerReduction_ker (n : ℕ) :
    (abelianPowerReduction A n).ker = (powMonoidHom n : A →* A).range := by
  ext a
  change (Submodule.Quotient.mk (Additive.ofMul a) :
    Additive A ⧸ integerMultiples (Additive A) n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_integerMultiples]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.toMul, ?_⟩
    apply Additive.ofMul.injective
    simpa only [powMonoidHom_apply, ofMul_pow, natCast_zsmul, ofMul_toMul] using hb
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    simpa only [natCast_zsmul, powMonoidHom_apply, ofMul_pow] using congrArg Additive.ofMul hb

theorem abelianPowerRange_characteristic (n : ℕ) :
    ((powMonoidHom n : A →* A).range).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e a ha
  obtain ⟨b, ⟨c, hc⟩, rfl⟩ := ha
  refine ⟨e c, ?_⟩
  change e c ^ n = e b
  simpa only [powMonoidHom_apply, map_pow] using congrArg e hc

theorem abelianPowerRange_finiteIndex (n : ℕ)
    [Finite (Additive A ⧸ integerMultiples (Additive A) n)] :
    ((powMonoidHom n : A →* A).range).FiniteIndex := by
  rw [← abelianPowerReduction_ker A n]
  infer_instance

theorem abelianPowerRange_torsionFree [Finite (CommGroup.torsion A)] :
    HasNoNontrivialTorsion ((powMonoidHom (Nat.card (CommGroup.torsion A)) : A →* A).range) := by
  let n := Nat.card (CommGroup.torsion A)
  have hn : 0 < n := Nat.card_pos
  intro x m hm hxm
  obtain ⟨a, ha⟩ := x.property
  have hpow : (a ^ n) ^ m = 1 := by
    have hx : (x : A) ^ m = 1 := congrArg (fun t : (powMonoidHom n : A →* A).range => (t : A)) hxm
    rw [← ha] at hx
    exact hx
  have hat : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n * m, Nat.mul_pos hn (Nat.pos_of_ne_zero hm), by rwa [pow_mul]⟩
  have han : a ^ n = 1 := congrArg (fun t : CommGroup.torsion A => (t : A))
    (pow_card_eq_one' (x := (⟨a, hat⟩ : CommGroup.torsion A)))
  apply Subtype.ext
  exact ha.symm.trans han

end PolycyclicRecognition

end

end OAI
