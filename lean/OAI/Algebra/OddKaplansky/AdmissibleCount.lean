import OAI.Algebra.OddKaplansky.PolynomialGrid

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3

section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {H : Type portUniverse2} {I : Type portUniverse3} [Field K] [Fintype K] [Group H] [sectionInstance22 : Fintype H] [Fintype I]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hM : Fintype.card Kˣ = M)

def weight (lmb : Base (H := H) M) (x : H) : Kˣ :=
  (Fourier.cyclicCharacter M hζ (lmb x⁻¹))⁻¹

lemma weight_bijective
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [contextInstance3 : Fintype.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{contextUniverse1} K (@CommRing.toCommMonoid.{contextUniverse1} K (@Field.toCommRing.{contextUniverse1} K contextInstance2)) ζ M)
    (hM : @Eq.{1} Nat
  (@Fintype.card.{contextUniverse1}
    (@Units.{contextUniverse1} K
      (@Semiring.toMonoid.{contextUniverse1} K
        (@CommSemiring.toSemiring.{contextUniverse1} K
          (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2)))))
    (@instFintypeUnitsOfDecidableEq.{contextUniverse1} K
      (@Semiring.toMonoid.{contextUniverse1} K
        (@CommSemiring.toSemiring.{contextUniverse1} K
          (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance2))))
      contextInstance3 fun a b => Classical.propDecidable (@Eq.{contextUniverse1 + 1} K a b)))
  M) : Function.Bijective (weight (H := H) M hζ) := by
  have hχ : Function.Bijective (Fourier.cyclicCharacter M hζ) := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · exact Fourier.cyclicCharacter_injective M hζ
    · simpa only [Fourier.C,Fintype.card_multiplicative,ZMod.card] using hM.symm
  constructor
  · intro lmb μ he
    funext x
    apply hχ.injective
    have hh := congrFun he x⁻¹
    simpa only [weight,inv_inv] using congrArg Inv.inv hh
  · intro f
    choose a ha using fun x => hχ.surjective ((f x⁻¹)⁻¹)
    refine ⟨a,?_⟩
    funext x
    simp only [weight,ha,inv_inv]

variable [DecidableEq H] [DecidableEq I]
def Admissible (B : Matrix H I K) (lmb : Base (H := H) M) : Prop :=
  FreeShiftCount.Free lmb ∧ (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det ≠ 0

include hM in
lemma card_singular (B : Matrix H I K) (hB : LinearIndependent K B.col) :
    Fintype.card {lmb : Base (H := H) M // (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det = 0} * M ≤
      Fintype.card I * M ^ Fintype.card H := by
  let E := Equiv.ofBijective (weight (H := H) M hζ) (weight_bijective M hζ hM)
  let E' : {lmb : Base (H := H) M // (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det = 0} ≃
      {f : H → Kˣ // MvPolynomial.eval (fun x => (f x : K)) (WeightedGram.polynomial B) = 0} :=
    E.subtypeEquiv (fun lmb => by rw [WeightedGram.eval_polynomial]; rfl)
  have hz := PolynomialGrid.card_units_zero_le_general (WeightedGram.polynomial B) (WeightedGram.nonzero B hB)
  have he := Fintype.card_congr E'
  simp only [Fintype.card_eq_nat_card] at he hz ⊢
  have hM' := hM
  simp only [Fintype.card_eq_nat_card] at hM'
  rw [← he,hM'] at hz
  have hd := WeightedGram.totalDegree B
  simp only [Fintype.card_eq_nat_card] at hd
  exact hz.trans (Nat.mul_le_mul_right _ hd)

include hM in
lemma cardinality (B : Matrix H I K) (hB : LinearIndependent K B.col)
    (hI : 4*Fintype.card I < M) (hH : 4*(Fintype.card H-1) < M) :
    Fintype.card (Base (H := H) M) < 2 * Fintype.card {lmb : Base (H := H) M // Admissible M hζ B lmb} := by
  let A := Base (H := H) M
  have hc : Fintype.card (Fourier.C M) = M := by simp [Fourier.C]
  have h0 : 0 < M ^ Fintype.card H := pow_pos (Nat.pos_of_ne_zero (NeZero.ne M)) _
  have hn := FreeShiftCount.card_not_free (H := H) (C := Fourier.C M)
  rw [hc] at hn
  have hs := card_singular M hζ hM B hB
  have hu : Fintype.card {lmb : A // ¬ Admissible M hζ B lmb} ≤
      Fintype.card {lmb : A // ¬ FreeShiftCount.Free lmb} +
      Fintype.card {lmb : A // (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det = 0} := by
    let f : {lmb : A // ¬ Admissible M hζ B lmb} →
        {lmb : A // ¬ FreeShiftCount.Free lmb} ⊕
        {lmb : A // (B.transpose * Matrix.diagonal (fun x => (weight M hζ lmb x : K)) * B).det = 0} :=
      fun lmb => if h : FreeShiftCount.Free lmb.val then Sum.inr ⟨lmb.val,by simpa only [Admissible,h,true_and,not_not] using lmb.property⟩
      else Sum.inl ⟨lmb.val,h⟩
    have hf : Function.Injective f := by
      intro a b he
      apply Subtype.ext
      have h := congrArg (Sum.elim Subtype.val Subtype.val) he
      simpa only [f,apply_dite,Sum.elim_inl,Sum.elim_inr,dite_eq_ite,ite_self] using h
    simpa only [Fintype.card_sum] using Fintype.card_le_of_injective f hf
  have hc' : Fintype.card {lmb : A // Admissible M hζ B lmb} +
      Fintype.card {lmb : A // ¬ Admissible M hζ B lmb} = M ^ Fintype.card H := by
    rw [Fintype.card_subtype_compl, Nat.add_sub_of_le (Fintype.card_subtype_le _)]
    simp only [A,Base,Fintype.card_fun,hc]
  have hsum : 2*(Fintype.card I+(Fintype.card H-1)) < M := by omega
  have hmul := Nat.mul_lt_mul_of_pos_right hsum h0
  have hub := Nat.mul_le_mul_right M hu
  have hh : 2*Fintype.card {lmb : A // ¬ Admissible M hζ B lmb} < M ^ Fintype.card H := by
    have hp : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    simp only [A, Fintype.card_eq_nat_card] at hn hs hub hmul ⊢
    nlinarith
  change Fintype.card A < _
  have hca : Fintype.card A = M ^ Fintype.card H := by simp only [A,Base,Fintype.card_fun,hc]
  rw [hca]
  simp only [A, Fintype.card_eq_nat_card] at hc' hh ⊢
  omega
end
end OddKaplansky.WreathFourier

end

end OAI
