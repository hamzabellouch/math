import OAI.Algebra.OddKaplansky.WreathMultiply

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3

section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {H : Type portUniverse2} {R : Type portUniverse3} [Field K] [Group H] [Fintype H] [sectionInstance16 : Fintype R]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (lmb : R → Base (H := H) M)
variable (hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)))

def freeUnit (a : R × H × H) : MonoidAlgebra K (Wreath (H := H) M) :=
  normal M hζ (shift M a.2.1 (lmb a.1)) (a.2.1*a.2.2⁻¹)

lemma freeUnit_mul
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [contextInstance4 : Group.{contextUniverse2} H]
    [contextInstance5 : Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [contextInstance8 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (hc : @Ne.{contextUniverse1 + 1} K
  (@Nat.cast.{contextUniverse1} K
    (@AddMonoidWithOne.toNatCast.{contextUniverse1} K
      (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
        (@Ring.toAddGroupWithOne.{contextUniverse1} K
          (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance3)))))
    (@Fintype.card.{contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@Pi.instFintype.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M)
        (fun a b => Classical.propDecidable (@Eq.{contextUniverse2 + 1} H a b)) contextInstance5 fun _ =>
        @Multiplicative.fintype.{0} (ZMod M) (@ZMod.fintype M contextInstance8))))
  (@OfNat.ofNat.{contextUniverse1} K (nat_lit 0)
    (@Zero.toOfNat0.{contextUniverse1} K
      (@MulZeroClass.toZero.{contextUniverse1} K
        (@instMulZeroClassOfSemiring.{contextUniverse1} K
          (@CommSemiring.toSemiring.{contextUniverse1} K
            (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))))))))
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
    (hinj : @Function.Injective.{max (contextUniverse2 + 1) (contextUniverse3 + 1), contextUniverse2 + 1} (Prod.{contextUniverse3, contextUniverse2} R H)
  (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) fun a =>
  @DFunLike.coe.{contextUniverse2 + 1, contextUniverse2 + 1, contextUniverse2 + 1}
    (@MulEquiv.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
        @Multiplicative.mul.{0} (ZMod M)
          (@Distrib.toAdd.{0} (ZMod M)
            (@instDistribOfSemiring.{0} (ZMod M)
              (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
      (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
        @Multiplicative.mul.{0} (ZMod M)
          (@Distrib.toAdd.{0} (ZMod M)
            (@instDistribOfSemiring.{0} (ZMod M)
              (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
    (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (fun _ => @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
    (@EquivLike.toFunLike.{contextUniverse2 + 1, contextUniverse2 + 1, contextUniverse2 + 1}
      (@MulEquiv.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
      (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@MulEquiv.instEquivLike.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))))
    (@OddKaplansky.WreathFourier.shift.{contextUniverse2} H contextInstance4 M (@Prod.snd.{contextUniverse3, contextUniverse2} R H a))
    (lmb (@Prod.fst.{contextUniverse3, contextUniverse2} R H a))) (r s : R) (x y z t : H) :
    freeUnit M hζ lmb (r,x,y) * freeUnit M hζ lmb (s,z,t) =
      if r = s ∧ y = z then freeUnit M hζ lmb (r,x,t) else 0 := by
  have he : shift M x (lmb r) = shift M (x*y⁻¹) (shift M z (lmb s)) ↔ r = s ∧ y = z := by
    constructor
    · intro h
      have hh := @hinj (r,x) (s,x*y⁻¹*z) (show shift M x (lmb r) = shift M (x*y⁻¹*z) (lmb s) by simpa only [shift_mul] using h)
      have hr : r = s := congrArg Prod.fst hh
      have hx : x = x*y⁻¹*z := congrArg Prod.snd hh
      refine ⟨hr,?_⟩
      have hy : 1 = y⁻¹*z := mul_left_cancel (by simpa only [mul_assoc,mul_one] using hx)
      exact inv_mul_eq_one.mp hy.symm
    · rintro ⟨rfl,rfl⟩
      rw [← shift_mul]
      simp only [mul_assoc,inv_mul_cancel,mul_one]
  simp only [freeUnit,normal_mul M hζ hc,he]
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    simp only [mul_assoc,inv_mul_cancel_left]
  · rfl

lemma freeUnit_independent
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {R : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [contextInstance4 : Group.{contextUniverse2} H]
    [contextInstance5 : Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} R]
    (M : Nat)
    [contextInstance8 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    (hc : @Ne.{contextUniverse1 + 1} K
  (@Nat.cast.{contextUniverse1} K
    (@AddMonoidWithOne.toNatCast.{contextUniverse1} K
      (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
        (@Ring.toAddGroupWithOne.{contextUniverse1} K
          (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance3)))))
    (@Fintype.card.{contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@Pi.instFintype.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M)
        (fun a b => Classical.propDecidable (@Eq.{contextUniverse2 + 1} H a b)) contextInstance5 fun _ =>
        @Multiplicative.fintype.{0} (ZMod M) (@ZMod.fintype M contextInstance8))))
  (@OfNat.ofNat.{contextUniverse1} K (nat_lit 0)
    (@Zero.toOfNat0.{contextUniverse1} K
      (@MulZeroClass.toZero.{contextUniverse1} K
        (@instMulZeroClassOfSemiring.{contextUniverse1} K
          (@CommSemiring.toSemiring.{contextUniverse1} K
            (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))))))))
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
    (hinj : @Function.Injective.{max (contextUniverse2 + 1) (contextUniverse3 + 1), contextUniverse2 + 1} (Prod.{contextUniverse3, contextUniverse2} R H)
  (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) fun a =>
  @DFunLike.coe.{contextUniverse2 + 1, contextUniverse2 + 1, contextUniverse2 + 1}
    (@MulEquiv.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
        @Multiplicative.mul.{0} (ZMod M)
          (@Distrib.toAdd.{0} (ZMod M)
            (@instDistribOfSemiring.{0} (ZMod M)
              (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
      (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
        @Multiplicative.mul.{0} (ZMod M)
          (@Distrib.toAdd.{0} (ZMod M)
            (@instDistribOfSemiring.{0} (ZMod M)
              (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
    (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (fun _ => @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
    (@EquivLike.toFunLike.{contextUniverse2 + 1, contextUniverse2 + 1, contextUniverse2 + 1}
      (@MulEquiv.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M)))))))
      (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
      (@MulEquiv.instEquivLike.{contextUniverse2, contextUniverse2} (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@OddKaplansky.WreathFourier.Base.{contextUniverse2} H M)
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))
        (@Pi.instMul.{contextUniverse2, 0} H (fun _ => OddKaplansky.Fourier.C M) fun _ =>
          @Multiplicative.mul.{0} (ZMod M)
            (@Distrib.toAdd.{0} (ZMod M)
              (@instDistribOfSemiring.{0} (ZMod M)
                (@CommSemiring.toSemiring.{0} (ZMod M) (@CommRing.toCommSemiring.{0} (ZMod M) (ZMod.commRing M))))))))
    (@OddKaplansky.WreathFourier.shift.{contextUniverse2} H contextInstance4 M (@Prod.snd.{contextUniverse3, contextUniverse2} R H a))
    (lmb (@Prod.fst.{contextUniverse3, contextUniverse2} R H a))) : LinearIndependent K (freeUnit M hζ lmb) := by
  let f : R × H × H → Base (H := H) M × H := fun a => (shift M a.2.1 (lmb a.1), a.2.1*a.2.2⁻¹)
  have hf : Function.Injective f := by
    rintro ⟨r,x,y⟩ ⟨s,z,t⟩ he
    have hrs := @hinj (r,x) (s,z) (congrArg Prod.fst he)
    have hr : r = s := congrArg Prod.fst hrs
    have hx : x = z := congrArg Prod.snd hrs
    subst s
    subst z
    have hy : y = t := inv_injective (mul_left_cancel (congrArg Prod.snd he))
    subst t
    rfl
  exact (normal_independent M hζ hc).comp f hf

lemma topElt_normal (h g : H) (μ : Base (H := H) M) :
    topElt M h * normal M hζ μ g = normal M hζ (shift M h μ) (h*g) := by
  unfold normal
  rw [← mul_assoc,topElt_projector,mul_assoc,topElt_mul]

lemma topElt_freeUnit
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
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (h : H) (r : R) (x y : H) :
    topElt M h * freeUnit M hζ lmb (r,x,y) = freeUnit M hζ lmb (r,h*x,y) := by
  simp only [freeUnit,topElt_normal,shift_mul,mul_assoc]

lemma freeUnit_topElt
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
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (h : H) (r : R) (x y : H) :
    freeUnit M hζ lmb (r,x,y) * topElt M h = freeUnit M hζ lmb (r,x,h⁻¹*y) := by
  simp only [freeUnit,normal,mul_assoc,topElt_mul,mul_inv_rev,inv_inv]

def baseElt (a : Base (H := H) M) : MonoidAlgebra K (Wreath (H := H) M) := MonoidAlgebra.single (base M a) 1

lemma projector_baseElt (a μ : Base (H := H) M) :
    projector M hζ μ * baseElt M a = (Fourier.character M hζ μ a : K) • projector M hζ μ :=
  CharacterIdempotents.pushed_mul_single _ _ _

lemma baseElt_projector (a μ : Base (H := H) M) :
    baseElt M a * projector M hζ μ = (Fourier.character M hζ μ a : K) • projector M hζ μ := by
  let f := MonoidAlgebra.mapDomainAlgHom K K (base (H := H) M)
  have hh := congrArg f (mul_comm (MonoidAlgebra.single a (1 : K)) (CharacterIdempotents.projector (Fourier.character M hζ μ)))
  have hf : f (MonoidAlgebra.single a 1) = baseElt M a := by simp [f,baseElt]
  rw [map_mul,map_mul,hf] at hh
  exact hh.trans (projector_baseElt M hζ a μ)

lemma topElt_baseElt (h : H) (a : Base (H := H) M) :
    topElt (K := K) M h * baseElt M a = baseElt M (shift M h a) * topElt M h := by
  have hg := top_conjugate M h a
  have he := congrArg (fun g : Wreath (H := H) M => g * top M h) hg
  simp only [mul_assoc,inv_mul_cancel,mul_one] at he
  simp only [topElt,baseElt,MonoidAlgebra.single_mul_single,one_mul,he]

lemma baseElt_freeUnit
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
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (a : Base (H := H) M) (r : R) (x y : H) :
    baseElt M a * freeUnit M hζ lmb (r,x,y) =
      (Fourier.character M hζ (shift M x (lmb r)) a : K) • freeUnit M hζ lmb (r,x,y) := by
  simp only [freeUnit,normal,← mul_assoc,baseElt_projector,smul_mul_assoc]

lemma freeUnit_baseElt
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
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (a : Base (H := H) M) (r : R) (x y : H) :
    freeUnit M hζ lmb (r,x,y) * baseElt M a =
      (Fourier.character M hζ (shift M y (lmb r)) a : K) • freeUnit M hζ lmb (r,x,y) := by
  simp only [freeUnit,normal,mul_assoc,topElt_baseElt]
  rw [← mul_assoc,projector_baseElt]
  rw [character_shift_right,← shift_mul]
  simp only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one,smul_mul_assoc]
end
end OddKaplansky.WreathFourier

end

end OAI
