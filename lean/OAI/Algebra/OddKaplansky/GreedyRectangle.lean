import OAI.Algebra.OddKaplansky.GreedyInverse

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3 contextUniverse4 contextUniverse5

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5

section
namespace OddKaplansky.GreedyRing
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {D : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommRing D] [Fintype S] [LinearOrder S]
variable (ε : D →+* K) (unitLift : ∀ d : D, ε d ≠ 0 → IsUnit d)
variable (E : Matrix S S D) (hE : E*E=E)
variable {W : Type portUniverse4} {N : Type portUniverse5} [Fintype W] [sectionInstance58 : LinearOrder W] [Fintype N] [sectionInstance59 : LinearOrder N]
variable (hpair : Fintype.card N*Fintype.card S=Fintype.card W*Fintype.card (I ε E))

def pairing : (N×S) ≃ (W×I ε E) :=
  (@FiniteChoice.orderedIndex (N×S) (FiniteChoice.tupleOrder N S) inferInstance).trans
    ((finCongr (by simpa only [Fintype.card_prod] using hpair)).trans
      (@FiniteChoice.orderedIndex (W×I ε E) (FiniteChoice.tupleOrder W (I ε E)) inferInstance).symm)

def coordinateEquiv : (N → S → D) ≃ₗ[D] (W → LinearMap.range (Matrix.toLin' E)) :=
  (LinearEquiv.curry D D N S).symm.trans
    ((LinearEquiv.funCongrLeft D D (pairing ε E hpair).symm).trans
      ((LinearEquiv.curry D D W (I ε E)).trans
        (LinearEquiv.piCongrRight (fun _ : W => (imageBasis ε unitLift E hE).equivFun.symm))))
def rectangleJ : Matrix W N (Module.End D (S → D)) :=
  IdempotentFree.J (Matrix.toLin' E) (coordinateEquiv ε unitLift E hE hpair)
def rectangleY : Matrix N W (Module.End D (S → D)) :=
  IdempotentFree.Y (Matrix.toLin' E) (coordinateEquiv ε unitLift E hE hpair)
lemma rectangleYJ : rectangleY ε unitLift E hE hpair*rectangleJ ε unitLift E hE hpair=1 := by
  have hi : Matrix.toLin' E ∘ₗ Matrix.toLin' E=Matrix.toLin' E := by rw [← Matrix.toLin'_mul,hE]
  convert IdempotentFree.YJ (Matrix.toLin' E) hi (coordinateEquiv ε unitLift E hE hpair) using 1 <;> congr ; exact Subsingleton.elim _ _
lemma rectangleJY : rectangleJ ε unitLift E hE hpair*rectangleY ε unitLift E hE hpair=Matrix.diagonal (fun _ : W => Matrix.toLin' E) := by
  convert IdempotentFree.JY (Matrix.toLin' E) (coordinateEquiv ε unitLift E hE hpair) using 1 <;> congr ; exact Subsingleton.elim _ _
variable [Algebra K D] [Module.Finite K D]
include unitLift hE in
lemma image_dimension : Module.finrank K (LinearMap.range (Matrix.toLin' E))=Fintype.card (I ε E)*Module.finrank K D := by
  have hh := ((imageBasis ε unitLift E hE).equivFun.restrictScalars K).finrank_eq
  simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hh
lemma pair_dimension
    {K : Type contextUniverse1}
    {D : Type contextUniverse2}
    {S : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [contextInstance4 : CommRing.{contextUniverse2} D]
    [contextInstance5 : Fintype.{contextUniverse3} S]
    [LinearOrder.{contextUniverse3} S]
    (ε : @RingHom.{contextUniverse2, contextUniverse1} D K
  (@Semiring.toNonAssocSemiring.{contextUniverse2} D
    (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
  (@Semiring.toNonAssocSemiring.{contextUniverse1} K
    (@CommSemiring.toSemiring.{contextUniverse1} K
      (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))))
    (unitLift : ∀ (d : D),
  @Ne.{contextUniverse1 + 1} K
      (@DFunLike.coe.{max (contextUniverse1 + 1) (contextUniverse2 + 1), contextUniverse2 + 1, contextUniverse1 + 1}
        (@RingHom.{contextUniverse2, contextUniverse1} D K
          (@Semiring.toNonAssocSemiring.{contextUniverse2} D
            (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
          (@Semiring.toNonAssocSemiring.{contextUniverse1} K
            (@CommSemiring.toSemiring.{contextUniverse1} K
              (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))))
        D (fun _ => K)
        (@RingHom.instFunLike.{contextUniverse2, contextUniverse1} D K
          (@Semiring.toNonAssocSemiring.{contextUniverse2} D
            (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
          (@Semiring.toNonAssocSemiring.{contextUniverse1} K
            (@CommSemiring.toSemiring.{contextUniverse1} K
              (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))))
        ε d)
      (@OfNat.ofNat.{contextUniverse1} K (nat_lit 0)
        (@Zero.toOfNat0.{contextUniverse1} K
          (@MulZeroClass.toZero.{contextUniverse1} K
            (@instMulZeroClassOfSemiring.{contextUniverse1} K
              (@CommSemiring.toSemiring.{contextUniverse1} K
                (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))))))) →
    @IsUnit.{contextUniverse2} D
      (@Semiring.toMonoid.{contextUniverse2} D
        (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
      d)
    (E : Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (hE : @Eq.{max (contextUniverse2 + 1) (contextUniverse3 + 1)} (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
  (@HMul.hMul.{max contextUniverse2 contextUniverse3, max contextUniverse2 contextUniverse3, max contextUniverse2 contextUniverse3} (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D) (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{contextUniverse2, contextUniverse3, contextUniverse3, contextUniverse3} S S S D contextInstance5
      (@Distrib.toMul.{contextUniverse2} D
        (@instDistribOfSemiring.{contextUniverse2} D
          (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))))
      (@Semiring.toAddCommMonoid.{contextUniverse2} D
        (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))))
    E E)
  E)
    {W : Type contextUniverse4}
    {N : Type contextUniverse5}
    [Fintype.{contextUniverse4} W]
    [LinearOrder.{contextUniverse4} W]
    [Fintype.{contextUniverse5} N]
    [LinearOrder.{contextUniverse5} N]
    [contextInstance17 : @Algebra.{contextUniverse1, contextUniverse2} K D (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))
  (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))]
    [@Module.Finite.{contextUniverse1, contextUniverse2} K D
  (@CommSemiring.toSemiring.{contextUniverse1} K (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))
  (@Semiring.toAddCommMonoid.{contextUniverse2} D
    (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
  (@Algebra.toModule.{contextUniverse1, contextUniverse2} K D (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3))
    (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)) contextInstance17)] (hw : Fintype.card W=Module.finrank K (S → D))
    (hn : Fintype.card N=Module.finrank K (LinearMap.range (Matrix.toLin' E))) :
    Fintype.card N*Fintype.card S=Fintype.card W*Fintype.card (I ε E) := by
  rw [hn,hw,image_dimension ε unitLift E hE]
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  ring
end
end OddKaplansky.GreedyRing

end

end OAI
