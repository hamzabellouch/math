import OAI.Algebra.OddKaplansky.PrescribedSector

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section
namespace OddKaplansky.OrderedCosetMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [sectionInstance63 : Fintype G] [sectionInstance64 : LinearOrder G] (T : Subgroup G)
local instance orderedGreedyGroupDecidableEq : DecidableEq G := Classical.decEq G
variable [sectionInstance65 : IsMulCommutative T]
local instance orderedGreedyCommGroup : CommGroup T := { (inferInstance : Group T) with mul_comm := mul_comm' }
local instance orderedGreedyQuotientOrder : LinearOrder (G ⧸ T) := OrderedCosetCoordinates.quotientOrder T
local instance orderedGreedyQuotientDecidableEq : DecidableEq (G ⧸ T) := Classical.decEq _
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hexp : ∀ t : T, t^p=1)
def augmentation : D (K := K) T →+* K := LocalAlgebra.augment.toRingHom
lemma augmentation_unit
    {K : Type contextUniverse1}
    {G : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [contextInstance3 : Group.{contextUniverse2} G]
    [Fintype.{contextUniverse2} G]
    [LinearOrder.{contextUniverse2} G]
    (T : @Subgroup.{contextUniverse2} G contextInstance3)
    [@IsMulCommutative.{contextUniverse2}
  (@Subtype.{contextUniverse2 + 1} G fun x =>
    @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
      (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
        (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
      T x)
  (@Subgroup.mul.{contextUniverse2} G contextInstance3 T)]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p]
    (hexp : ∀
  (t :
    @Subtype.{contextUniverse2 + 1} G fun x =>
      @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
        (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
          (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
        T x),
  @Eq.{contextUniverse2 + 1}
    (@Subtype.{contextUniverse2 + 1} G fun x =>
      @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
        (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
          (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
        T x)
    (@HPow.hPow.{contextUniverse2, 0, contextUniverse2}
      (@Subtype.{contextUniverse2 + 1} G fun x =>
        @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
          (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
            (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
          T x)
      Nat
      (@Subtype.{contextUniverse2 + 1} G fun x =>
        @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
          (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
            (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
          T x)
      (@instHPow.{contextUniverse2, 0}
        (@Subtype.{contextUniverse2 + 1} G fun x =>
          @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
            (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
              (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
            T x)
        Nat (@Subgroup.npow.{contextUniverse2} G contextInstance3 T))
      t p)
    (@OfNat.ofNat.{contextUniverse2}
      (@Subtype.{contextUniverse2 + 1} G fun x =>
        @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
          (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
            (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
          T x)
      (nat_lit 1)
      (@One.toOfNat1.{contextUniverse2}
        (@Subtype.{contextUniverse2 + 1} G fun x =>
          @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
            (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
              (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
            T x)
        (@Subgroup.one.{contextUniverse2} G contextInstance3 T)))) (x : D (K := K) T) (hx : augmentation T x≠0) : IsUnit x :=
  (LocalAlgebra.isUnit_iff p hexp x).mpr hx
variable (e : MonoidAlgebra K G) (he : e*e=e)
lemma representation_idempotent
    {K : Type contextUniverse1}
    {G : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [contextInstance3 : Group.{contextUniverse2} G]
    [Fintype.{contextUniverse2} G]
    [LinearOrder.{contextUniverse2} G]
    (T : @Subgroup.{contextUniverse2} G contextInstance3)
    [@IsMulCommutative.{contextUniverse2}
  (@Subtype.{contextUniverse2 + 1} G fun x =>
    @Membership.mem.{contextUniverse2, contextUniverse2} G (@Subgroup.{contextUniverse2} G contextInstance3)
      (@SetLike.instMembership.{contextUniverse2, contextUniverse2} (@Subgroup.{contextUniverse2} G contextInstance3) G
        (@Subgroup.instSetLike.{contextUniverse2} G contextInstance3))
      T x)
  (@Subgroup.mul.{contextUniverse2} G contextInstance3 T)]
    (e : @MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
  (@CommSemiring.toSemiring.{contextUniverse1} K (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
    (he : @Eq.{max (contextUniverse1 + 1) (contextUniverse2 + 1)}
  (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
    (@CommSemiring.toSemiring.{contextUniverse1} K
      (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
  (@HMul.hMul.{max contextUniverse1 contextUniverse2, max contextUniverse1 contextUniverse2, max contextUniverse1 contextUniverse2}
    (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
      (@CommSemiring.toSemiring.{contextUniverse1} K
        (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
    (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
      (@CommSemiring.toSemiring.{contextUniverse1} K
        (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
    (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
      (@CommSemiring.toSemiring.{contextUniverse1} K
        (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
    (@instHMul.{max contextUniverse1 contextUniverse2}
      (@MonoidAlgebra.{contextUniverse1, contextUniverse2} K G
        (@CommSemiring.toSemiring.{contextUniverse1} K
          (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
      (@MonoidAlgebra.instMul.{contextUniverse1, contextUniverse2} K G
        (@CommSemiring.toSemiring.{contextUniverse1} K
          (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2)))
        (@MulOne.toMul.{contextUniverse2} G
          (@MulOneClass.toMulOne.{contextUniverse2} G
            (@Monoid.toMulOneClass.{contextUniverse2} G
              (@DivInvMonoid.toMonoid.{contextUniverse2} G (@Group.toDivInvMonoid.{contextUniverse2} G contextInstance3)))))))
    e e)
  e) : representation T e*representation T e=representation T e := by
  exact ((representation T).map_mul e e).symm.trans (congrArg (representation T) he)
variable {W : Type portUniverse3} {N : Type portUniverse4} [Fintype W] [LinearOrder W] [Fintype N] [LinearOrder N]
variable (hw : Fintype.card W=Fintype.card G)
variable (hn : Fintype.card N=Module.finrank K (LinearMap.range (Algebra.lmul K (MonoidAlgebra K G) e)))
include hexp he hw hn in
lemma greedy_pair : Fintype.card N*Fintype.card (G ⧸ T)=Fintype.card W*Fintype.card (GreedyRing.I (augmentation T) (representation T e)) := by
  apply GreedyRing.pair_dimension (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he)
  · rw [(unpack (K := K) T).finrank_eq,Module.finrank_eq_card_basis (MonoidAlgebra.basis G K)]
    exact hw
  · change Fintype.card N=Module.finrank K (LinearMap.range (endomorphism T e))
    rw [endomorphism_rank]
    exact hn

def explicitJ : Matrix W N (Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T)) := fun w n =>
  (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm
    (GreedyRing.rectangleJ (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he) (greedy_pair T p hexp e he hw hn) w n)
def explicitY : Matrix N W (Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T)) := fun n w =>
  (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm
    (GreedyRing.rectangleY (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he) (greedy_pair T p hexp e he hw hn) n w)
lemma explicit_products :
    explicitY T p hexp e he hw hn*explicitJ T p hexp e he hw hn=1 ∧
    explicitJ T p hexp e he hw hn*explicitY T p hexp e he hw hn=Matrix.diagonal (fun _ : W => representation T e) := by
  let φ := (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm
  have hYJ := GreedyRing.rectangleYJ (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he) (greedy_pair T p hexp e he hw hn)
  have hJY := GreedyRing.rectangleJY (augmentation T) (augmentation_unit T p hexp) (representation T e) (representation_idempotent T e he) (greedy_pair T p hexp e he hw hn)
  constructor
  · funext n n'
    have hh := congrArg (fun F => φ (F n n')) hYJ
    simpa only [explicitY,explicitJ,Matrix.mul_apply,map_sum,map_mul,Matrix.one_apply,apply_ite,map_one,map_zero] using hh
  · funext w w'
    have hh := congrArg (fun F => φ (F w w')) hJY
    have hφ : φ (Matrix.toLin' (representation T e))=representation T e :=
      (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm_apply_apply _
    simp only [Matrix.toLin'_apply'] at hh hφ
    simpa only [explicitJ,explicitY,Matrix.mul_apply,map_sum,map_mul,Matrix.diagonal_apply,apply_ite,map_zero,hφ] using hh
end
end OddKaplansky.OrderedCosetMatrix

end

end OAI
