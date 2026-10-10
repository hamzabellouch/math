import OAI.Algebra.OddKaplansky.OrderedMatrices

namespace OAI

universe contextUniverse1

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.OrderedOrbitBlock
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier OrderedCosetCoordinates
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H] [sectionInstance62 : LinearOrder H]
local instance orderedOrbitBlockDecidableEq : DecidableEq H := Classical.decEq H
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (lmb : Base (H := H) M) (T : Subgroup H)
variable (hT : ∀ g : H, g ∈ T ↔ shift M g lmb = lmb)
lemma shift_eq_iff
    {H : Type contextUniverse1}
    [contextInstance1 : Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    [LinearOrder.{contextUniverse1} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    (lmb : @OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
    (T : @Subgroup.{contextUniverse1} H contextInstance1)
    (hT : ∀ (g : H),
  Iff
    (@Membership.mem.{contextUniverse1, contextUniverse1} H (@Subgroup.{contextUniverse1} H contextInstance1)
      (@SetLike.instMembership.{contextUniverse1, contextUniverse1} (@Subgroup.{contextUniverse1} H contextInstance1) H
        (@Subgroup.instSetLike.{contextUniverse1} H contextInstance1))
      T g)
    (@Eq.{contextUniverse1 + 1} (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
      (@DFunLike.coe.{contextUniverse1 + 1, contextUniverse1 + 1, contextUniverse1 + 1}
        (@MulEquiv.{contextUniverse1, contextUniverse1} (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
          (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
            @Multiplicative.mul.{0} (ZMod M)
              (@Distrib.toAdd.{0} (ZMod M)
                (@instDistribOfSemiring.{0} (ZMod M)
                  (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
          (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
            @Multiplicative.mul.{0} (ZMod M)
              (@Distrib.toAdd.{0} (ZMod M)
                (@instDistribOfSemiring.{0} (ZMod M)
                  (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
        (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M) (fun _ => @OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
        (@EquivLike.toFunLike.{contextUniverse1 + 1, contextUniverse1 + 1, contextUniverse1 + 1}
          (@MulEquiv.{contextUniverse1, contextUniverse1} (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
            (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
            (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
              @Multiplicative.mul.{0} (ZMod M)
                (@Distrib.toAdd.{0} (ZMod M)
                  (@instDistribOfSemiring.{0} (ZMod M)
                    (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
            (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
              @Multiplicative.mul.{0} (ZMod M)
                (@Distrib.toAdd.{0} (ZMod M)
                  (@instDistribOfSemiring.{0} (ZMod M)
                    (@CommSemiring.toSemiring.{0} (ZMod M)
                      (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
          (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
          (@MulEquiv.instEquivLike.{contextUniverse1, contextUniverse1} (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
            (@OddKaplansky.WreathFourier.Base.{contextUniverse1} H M)
            (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
              @Multiplicative.mul.{0} (ZMod M)
                (@Distrib.toAdd.{0} (ZMod M)
                  (@instDistribOfSemiring.{0} (ZMod M)
                    (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
            (@Pi.instMul.{contextUniverse1, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
              @Multiplicative.mul.{0} (ZMod M)
                (@Distrib.toAdd.{0} (ZMod M)
                  (@instDistribOfSemiring.{0} (ZMod M)
                    (@CommSemiring.toSemiring.{0} (ZMod M)
                      (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))))
        (@OddKaplansky.WreathFourier.shift.{contextUniverse1} H contextInstance1 M g) lmb)
      lmb)) (g h : H) : shift M g lmb = shift M h lmb ↔ (g : H ⧸ T) = h := by
  rw [QuotientGroup.eq,hT]
  constructor
  · intro he
    rw [shift_mul,← he,← shift_mul,inv_mul_cancel,shift_one]
    rfl
  · intro he
    have hh := congrArg (shift M g) he
    simpa only [← shift_mul,mul_inv_cancel_left] using hh.symm
include hT in
lemma coset_shift (q : H ⧸ T) (t : T) : shift M (rep T q * t) lmb = shift M (rep T q) lmb := by
  apply (shift_eq_iff M lmb T hT _ _).mpr
  simp only [mk_rep_mul,rep_mk]
def unit (q r : H ⧸ T) (t : T) : MonoidAlgebra K (Wreath (H := H) M) :=
  normal M hζ (shift M (rep T q) lmb) (rep T q * t * (rep T r)⁻¹)
include hT hc in
lemma unit_mul (q r s z : H ⧸ T) (t u : T) :
    unit M hζ lmb T q r t * unit M hζ lmb T s z u =
      if r=s then unit M hζ lmb T q z (t*u) else 0 := by
  rw [unit,unit,normal_mul M hζ hc]
  have he : shift M (rep T q) lmb = shift M (rep T q * t * (rep T r)⁻¹) (shift M (rep T s) lmb) ↔ r=s := by
    rw [← shift_mul,shift_eq_iff M lmb T hT]
    constructor
    · intro hh
      have hm : (rep T q)⁻¹ * (rep T q * t * (rep T r)⁻¹ * rep T s) ∈ T := QuotientGroup.eq.mp hh
      have hr : (rep T r)⁻¹ * rep T s ∈ T := by
        have hmul := T.mul_mem (T.inv_mem t.property) hm
        simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_left] using hmul
      have hf := QuotientGroup.eq.mpr hr
      simpa only [rep_mk] using hf
    · intro hrs
      subst s
      simp only [mul_assoc,inv_mul_cancel,mul_one,mk_rep_mul,rep_mk]
  by_cases h : r=s
  · rw [ite_eq_left (he.mpr h),ite_eq_left h]
    subst s
    simp only [unit,Subgroup.coe_mul,mul_assoc,inv_mul_cancel_left]
  · rw [ite_eq_right (fun hh => h (he.mp hh)),ite_eq_right h]

def entry (q r : H ⧸ T) : MonoidAlgebra K T →ₗ[K] MonoidAlgebra K (Wreath (H := H) M) where
  toFun a := ∑ t : T, a.coeff t • unit M hζ lmb T q r t
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum,smul_smul]
lemma entry_apply (q r : H ⧸ T) (a : MonoidAlgebra K T) :
    entry M hζ lmb T q r a = ∑ t : T, a.coeff t • unit M hζ lmb T q r t := rfl
lemma entry_single (q r : H ⧸ T) (t : T) (c : K) :
    entry M hζ lmb T q r (MonoidAlgebra.single t c) = c • unit M hζ lmb T q r t := by
  rw [entry_apply]
  simp [MonoidAlgebra.coeff_single,Finsupp.single_apply,ite_smul]
include hT hc in
lemma entry_mul (q r s z : H ⧸ T) (a b : MonoidAlgebra K T) :
    entry M hζ lmb T q r a * entry M hζ lmb T s z b =
      if r=s then entry M hζ lmb T q z (a*b) else 0 := by
  induction a using MonoidAlgebra.induction_on with
  | of t =>
    induction b using MonoidAlgebra.induction_on with
    | of u => simp only [MonoidAlgebra.of_apply,entry_single,one_smul,MonoidAlgebra.single_mul_single,one_mul,unit_mul M hζ hc lmb T hT]
    | add b c hb hc => simp only [map_add,mul_add,hb,hc]; split_ifs <;> simp
    | smul c b hb => simp only [map_smul,mul_smul_comm,hb]; split_ifs <;> simp
  | add a c ha hc => simp only [map_add,add_mul,ha,hc]; split_ifs <;> simp
  | smul c a ha => simp only [map_smul,smul_mul_assoc,ha]; split_ifs <;> simp

def lift : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T) →ₗ[K] MonoidAlgebra K (Wreath (H := H) M) where
  toFun F := ∑ q, ∑ r, entry M hζ lmb T q r (F q r)
  map_add' F G := by simp [Finset.sum_add_distrib]
  map_smul' c F := by simp [Finset.smul_sum]
lemma lift_apply (F : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T)) :
    lift M hζ lmb T F = ∑ q, ∑ r, entry M hζ lmb T q r (F q r) := rfl
include hT hc in
lemma entry_lift (q r : H ⧸ T) (a : MonoidAlgebra K T)
    (G : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T)) :
    entry M hζ lmb T q r a * lift M hζ lmb T G =
      ∑ z, entry M hζ lmb T q z (a * G r z) := by
  simp only [lift_apply,Finset.mul_sum,entry_mul M hζ hc lmb T hT,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
include hT hc in
lemma lift_mul (F G : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T)) :
    lift M hζ lmb T F * lift M hζ lmb T G = lift M hζ lmb T (F*G) := by
  rw [lift_apply]
  simp only [Finset.sum_mul,entry_lift M hζ hc lmb T hT]
  rw [lift_apply]
  simp only [Matrix.mul_apply,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact Finset.sum_comm

def identity : MonoidAlgebra K (Wreath (H := H) M) := ∑ q : H ⧸ T, projector M hζ (shift M (rep T q) lmb)
lemma entry_one (q r : H ⧸ T) : entry M hζ lmb T q r 1 = unit M hζ lmb T q r 1 := by
  rw [MonoidAlgebra.one_def,entry_single,one_smul]
lemma lift_one : lift M hζ lmb T 1 = identity M hζ lmb T := by
  simp [lift_apply,Matrix.one_apply,apply_ite,entry_one,unit,normal,identity]
lemma unit_cocycle (g : H) (r : H ⧸ T) :
    unit M hζ lmb T (g • r) r (OrderedCosetMatrix.cocycle T g r) =
      normal M hζ (shift M (rep T (g • r)) lmb) g := by
  rw [unit,OrderedCosetMatrix.cocycle_reconstruct,mul_inv_cancel_right]
lemma lift_groupMatrix (g : H) :
    lift M hζ lmb T (OrderedCosetMatrix.groupMatrix T g) = identity M hζ lmb T * topElt M g := by
  rw [lift_apply,Finset.sum_comm]
  simp only [OrderedCosetMatrix.groupMatrix,apply_ite,map_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    entry_single,one_smul,unit_cocycle]
  rw [identity,Finset.sum_mul]
  exact Equiv.sum_comp (MulAction.toPerm g) (fun q : H ⧸ T => normal M hζ (shift M (rep T q) lmb) g)
lemma lift_representation (e : MonoidAlgebra K H) :
    lift M hζ lmb T (OrderedCosetMatrix.representation T e) =
      identity M hζ lmb T * MonoidAlgebra.mapDomainAlgHom K K (top M) e := by
  induction e using MonoidAlgebra.induction_on with
  | of g => simpa only [MonoidAlgebra.of_apply,OrderedCosetMatrix.representation_single,one_smul,
      MonoidAlgebra.mapDomainAlgHom_apply,MonoidAlgebra.mapDomain_single,topElt] using lift_groupMatrix M hζ lmb T g
  | add a b ha hb => simp only [map_add,mul_add,ha,hb]
  | smul c a ha => simp only [map_smul,mul_smul_comm,ha]
section Cross
variable (mu : Base (H := H) M) (U : Subgroup H)
variable (hsep : ∀ g : H, lmb ≠ shift M g mu)
include hc hsep in
lemma unit_cross (q r : H ⧸ T) (s z : H ⧸ U) (t : T) (u : U) :
    unit M hζ lmb T q r t * unit M hζ mu U s z u = 0 := by
  rw [unit,unit,normal_mul M hζ hc]
  apply ite_eq_right
  intro he
  apply hsep ((rep T q)⁻¹ * (rep T q * t * (rep T r)⁻¹) * rep U s)
  have hh := congrArg (shift M (rep T q)⁻¹) he
  simpa only [← shift_mul,inv_mul_cancel,shift_one,MulEquiv.refl_apply,mul_assoc] using hh
include hc hsep in
lemma entry_cross (q r : H ⧸ T) (s z : H ⧸ U) (a : MonoidAlgebra K T) (b : MonoidAlgebra K U) :
    entry M hζ lmb T q r a * entry M hζ mu U s z b = 0 := by
  rw [entry_apply,entry_apply]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    unit_cross M hζ hc lmb T mu U hsep,smul_zero,Finset.sum_const_zero]
include hc hsep in
lemma lift_cross (F : Matrix (H ⧸ T) (H ⧸ T) (MonoidAlgebra K T))
    (G : Matrix (H ⧸ U) (H ⧸ U) (MonoidAlgebra K U)) :
    lift M hζ lmb T F * lift M hζ mu U G = 0 := by
  rw [lift_apply,lift_apply]
  simp only [Finset.sum_mul,Finset.mul_sum,entry_cross M hζ hc lmb T mu U hsep,Finset.sum_const_zero]
end Cross
end
end OddKaplansky.OrderedOrbitBlock

end

end OAI
