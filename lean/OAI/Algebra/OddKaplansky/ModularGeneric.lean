import OAI.Algebra.OddKaplansky.OrbitSelection

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3 contextUniverse4

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5

section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {H : Type portUniverse2} {I : Type portUniverse3} [Field K] [sectionInstance27 : Fintype K] [Group H] [Fintype H] [Fintype I]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

@[instance_reducible]
def shiftAction : MulAction H (Base (H := H) M) where
  smul h a := shift M h a
  one_smul a := by change shift M 1 a = a; rw [shift_one]; rfl
  mul_smul h g a := shift_mul M h g a

def lamp : Base (H := H) M := Pi.mulSingle 1 (Multiplicative.ofAdd (1 : ZMod M))
lemma weight_diagonal
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance2)) ζ M) {J : Type portUniverse4} [Fintype J] (lmb : J → Base (H := H) M) (r : J) :
    diagonal M hζ lmb (lamp (H := H) M)⁻¹ r = Matrix.diagonal (fun x => (weight M hζ (lmb r) x : K)) := by
  unfold diagonal
  congr 1
  funext x
  simp only [map_inv,Units.val_inv_eq_inv_val,lamp,Fourier.character_mulSingle,shift_apply,mul_one,weight,Units.val_inv_eq_inv_val]

namespace Blocks
variable {R : Type portUniverse5} [Fintype R] (B : Matrix H I K) (lmb : R → Base (H := H) M)
def weights (r : R) (x : H) : K := weight M hζ (lmb r) x
def projection (r : R) := WeightedProjection.projection B (weights M hζ lmb r)
def element := MatrixUnits.lift (K := K) (freeUnit M hζ lmb) (projection M hζ B lmb)
lemma idempotent
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {I : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} I]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    {R : Type contextUniverse4}
    [Fintype.{contextUniverse4} R]
    (B : Matrix.{contextUniverse2, contextUniverse3, contextUniverse1} H I K)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)))
    (hN : ∀ r, (WeightedProjection.gram B (weights M hζ lmb r)).det ≠ 0) :
    element M hζ B lmb * element M hζ B lmb = element M hζ B lmb := by
  unfold element
  apply MatrixUnits.lift_idempotent (freeUnit M hζ lmb) (freeUnit_mul M hζ hc lmb hinj) (projection M hζ B lmb)
  intro r
  exact WeightedProjection.idempotent B (weights M hζ lmb r) (hN r)
lemma annihilate (ell : ℕ) (hleft : ∀ s : H, (TranslationMatrix.matrix (K := K) s - 1)^ell * B = 0)
    (hright : ∀ s : H, B.transpose * (TranslationMatrix.matrix (K := K) s - 1)^ell = 0) (s : H) :
    (topElt M s-1)^ell*element M hζ B lmb=0 ∧
    element M hζ B lmb*(baseElt M (lamp (H := H) M)*topElt M s*baseElt M (lamp (H := H) M)⁻¹-1)^ell=0 := by
  let φ := MatrixUnits.lift (K := K) (freeUnit M hζ lmb)
  have hu := MatrixActions.represents_pow φ (MatrixActions.represents_sub φ (top_represents M hζ lmb s) (MatrixActions.represents_one φ)) ell
  have hv := MatrixActions.represents_pow φ (MatrixActions.represents_sub φ (conjugate_represents M hζ lmb (lamp (H := H) M) s) (MatrixActions.represents_one φ)) ell
  constructor
  · apply MatrixActions.annihilates_left φ hu
    funext r
    exact WeightedProjection.annihilate_left B (weights M hζ lmb r) _ (hleft s)
  · apply MatrixActions.annihilates_right φ hv
    funext r
    apply WeightedProjection.annihilate_right B (weights M hζ lmb r)
    change B.transpose * Matrix.diagonal (fun x => (weight M hζ (lmb r) x : K)) * _ = 0
    rw [← weight_diagonal M hζ lmb r]
    exact WeightedProjection.conjugate_annihilate B _ _ _
      (diagonal_inv M hζ lmb (lamp (H := H) M) r) (diagonal_inv' M hζ lmb (lamp (H := H) M) r) ell (hright s)
lemma rank_bound
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    {I : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    [Fintype.{contextUniverse3} I]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance3)) ζ M)
    {R : Type contextUniverse4}
    [Fintype.{contextUniverse4} R]
    (B : Matrix.{contextUniverse2, contextUniverse3, contextUniverse1} H I K)
    (lmb : R → @OddKaplansky.WreathFourier.Base.{contextUniverse2} H M) (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)))
    (hN : ∀ r, (WeightedProjection.gram B (weights M hζ lmb r)).det ≠ 0) :
    Fintype.card R * Fintype.card I * Fintype.card H ≤
      Module.finrank K (LinearMap.range (Algebra.lmul K _ (element M hζ B lmb))) := by
  let C (r : R) := (WeightedProjection.gram B (weights M hζ lmb r))⁻¹ * B.transpose * Matrix.diagonal (weights M hζ lmb r)
  have hCB (r : R) : C r * B = 1 := by
    change (WeightedProjection.gram B _)⁻¹ * B.transpose * Matrix.diagonal _ * B = 1
    simpa only [WeightedProjection.gram,Matrix.mul_assoc] using
      Matrix.nonsing_inv_mul (WeightedProjection.gram B (weights M hζ lmb r)) (isUnit_iff_ne_zero.mpr (hN r))
  have hd := MatrixUnits.regular_rank_bound (freeUnit M hζ lmb) (freeUnit_mul M hζ hc lmb hinj)
    (freeUnit_independent M hζ hc lmb hinj) B C hCB
  have heq : (fun r => B*C r) = projection M hζ B lmb := by
    funext r
    simp only [C,projection,WeightedProjection.projection,Matrix.mul_assoc]
  rw [heq] at hd
  exact hd
end Blocks

include hζ in
lemma modular_idempotent (hM : Fintype.card Kˣ = M)
    (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (B : Matrix H I K) (hB : LinearIndependent K B.col)
    (ell : ℕ) (hleft : ∀ s : H, (TranslationMatrix.matrix (K := K) s - 1)^ell * B = 0)
    (hright : ∀ s : H, B.transpose * (TranslationMatrix.matrix (K := K) s - 1)^ell = 0)
    (hI : 4 * Fintype.card I < M) (hH : 4 * (Fintype.card H - 1) < M)
    (hlarge : Fintype.card H < 48 * Fintype.card I) :
    ∃ e : MonoidAlgebra K (Wreath (H := H) M), e*e=e ∧
      (∀ s : H, (topElt M s-1)^ell*e=0 ∧
        e*(baseElt M (lamp (H := H) M)*topElt M s*baseElt M (lamp (H := H) M)⁻¹-1)^ell=0) ∧
      Fintype.card (Wreath (H := H) M) < 96 * Module.finrank K (LinearMap.range (Algebra.lmul K _ e)) := by
  let : MulAction H (Base (H := H) M) := shiftAction M
  let R := OrbitSelection.Rep (H := H) (Admissible M hζ B)
  let lmb : R → Base (H := H) M := OrbitSelection.representative (Admissible M hζ B)
  have hlmb (r : R) : Admissible M hζ B (lmb r) := (OrbitSelection.representative_spec (Admissible M hζ B) r).2
  have hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)) := by
    apply OrbitSelection.orbit_injective (Admissible M hζ B)
    intro a ha g hga
    exact ha.1 g (congrFun hga)
  have hN (r : R) : (WeightedProjection.gram B (Blocks.weights M hζ lmb r)).det ≠ 0 := (hlmb r).2
  refine ⟨Blocks.element M hζ B lmb,Blocks.idempotent M hζ B lmb hc hinj hN,
    Blocks.annihilate M hζ B lmb ell hleft hright,?_⟩
  have hd := Blocks.rank_bound M hζ B lmb hc hinj hN
  have ha := cardinality M hζ hM B hB hI hH
  have hb := OrbitSelection.card_good (H := H) (Admissible M hζ B)
  change Fintype.card {a // Admissible M hζ B a} ≤ Fintype.card R * Fintype.card H at hb
  have hbase : 0 < Fintype.card (Base (H := H) M) := Fintype.card_pos
  have hR : 0 < Fintype.card R := by nlinarith
  have hsmall : Fintype.card (Base (H := H) M) < 96 * Fintype.card R * Fintype.card I := by
    have hh := Nat.mul_lt_mul_of_pos_left hlarge hR
    nlinarith
  have hn : 0 < Fintype.card H := Fintype.card_pos
  have hw := Nat.mul_lt_mul_of_pos_right hsmall hn
  have hcard : Fintype.card (Wreath (H := H) M) = Fintype.card (Base (H := H) M) * Fintype.card H := by
    rw [← Fintype.card_prod]
    apply Fintype.card_congr
    exact { toFun := fun g => (g.left,g.right)
            invFun := fun z => ⟨z.1,z.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [hcard]
  nlinarith
end
end OddKaplansky.WreathFourier

end

end OAI
