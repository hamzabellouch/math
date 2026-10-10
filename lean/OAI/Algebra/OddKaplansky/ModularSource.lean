import OAI.Algebra.OddKaplansky.HighCount

namespace OAI

universe contextUniverse1

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {E : Type portUniverse2} [Field K] [Fintype E] [DecidableEq E]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
lemma regular_translation (s : C (E := E) p) :
    regular (K := K) p (delta p s.toAdd) = TranslationMatrix.matrix s := by
  ext x y
  simp only [regular_delta,TranslationMatrix.matrix]
  congr 1
end
end OddKaplansky.Augmentation

namespace OddKaplansky.ModularSource
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse3} [Field K] [sectionInstance39 : Fintype K]
variable (p M ell : ℕ) [sectionInstance40 : Fact p.Prime] [sectionInstance41 : NeZero M] [CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
abbrev P := Multiplicative (Fin 3 → ZMod p)
lemma card_P : Fintype.card (P p) = p^3 := by simp [P]
lemma base_nonzero
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    (p : Nat)
    (M : Nat)
    [Fact (Nat.Prime p)]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p] (hM : M+1=p^4) : (Fintype.card (WreathFourier.Base (H := P p) M) : K) ≠ 0 := by
  have hm : (M : K) ≠ 0 := by
    have hc := congrArg (fun n : ℕ => (n : K)) hM
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,CharP.cast_eq_zero K p,zero_pow (by omega : 4≠0)] at hc
    intro hz
    rw [hz,zero_add] at hc
    exact one_ne_zero hc
  have hcard : Fintype.card (WreathFourier.Base (H := P p) M) = M^(p^3) := by simp [WreathFourier.Base,Fourier.C]
  rw [hcard,Nat.cast_pow]
  exact pow_ne_zero _ hm
lemma quartic_large
    (p : Nat)
    (M : Nat)
    [Fact (Nat.Prime p)]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (hp : 5 ≤ p) (hM : M+1=p^4) : 4*p^3 < M := by
  have h1 : 2 ≤ p^3 := by have hh := Nat.pow_le_pow_left hp 3; norm_num at hh; omega
  have h2 := Nat.mul_le_mul_right (p^3) hp
  nlinarith [show p^4=p*p^3 by ring]
lemma left_ann
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    (p : Nat)
    (ell : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p]
    : ∀ s : P p, (TranslationMatrix.matrix (K := K) s - 1)^ell * Augmentation.columns (K := K) (E := Fin 3) p ell = 0 := by
  intro s
  rw [← Augmentation.regular_translation (K := K) p s]
  exact Augmentation.columns_annihilated p ell s.toAdd
lemma right_ann
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse1} K]
    (p : Nat)
    (ell : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p]
    : ∀ s : P p, (Augmentation.columns (K := K) (E := Fin 3) p ell).transpose * (TranslationMatrix.matrix (K := K) s - 1)^ell = 0 := by
  intro s
  rw [← Augmentation.regular_translation (K := K) p s]
  exact Augmentation.columns_transpose_annihilated p ell s.toAdd
lemma high_small (hp : 5≤p) (hM : M+1=p^4) : 4*Fintype.card (Augmentation.High (E := Fin 3) p ell) < M := by
  have hh := Augmentation.card_high_le p ell
  have hm := quartic_large p M hp hM
  omega
lemma point_small (hp : 5≤p) (hM : M+1=p^4) : 4*(Fintype.card (P p)-1)<M := by
  rw [card_P]
  have hm := quartic_large p M hp hM
  omega
lemma high_large (hp : 5≤p) (he : p=2*ell+1) : Fintype.card (P p) < 48*Fintype.card (Augmentation.High (E := Fin 3) p ell) := by
  rw [card_P]
  exact Augmentation.high_ratio p ell he (by omega)
include hζ in
lemma exists_idempotent (hp : 5 ≤ p) (hpell : p=2*ell+1) (hM : M+1=p^4)
    (hK : Fintype.card Kˣ = M) :
    ∃ e : MonoidAlgebra K (WreathFourier.Wreath (H := P p) M), e*e=e ∧
      (∀ s : P p, (WreathFourier.topElt M s-1)^ell*e=0 ∧
        e*(WreathFourier.baseElt M (WreathFourier.lamp (H := P p) M)*WreathFourier.topElt M s*WreathFourier.baseElt M (WreathFourier.lamp (H := P p) M)⁻¹-1)^ell=0) ∧
      Fintype.card (WreathFourier.Wreath (H := P p) M) < 96 * Module.finrank K (LinearMap.range (Algebra.lmul K _ e)) := by
  have h := WreathFourier.modular_idempotent (K := K) (H := P p) (I := Augmentation.High (E := Fin 3) p ell) M hζ hK
    (by simpa only [Fintype.card_eq_nat_card] using base_nonzero (K := K) p M hM)
    (Augmentation.columns (K := K) (E := Fin 3) p ell)
    (Augmentation.columns_independent (K := K) (E := Fin 3) p ell) ell
    (by intro s; convert left_ann (K := K) p ell s using 1 ; congr <;> exact Subsingleton.elim _ _)
    (by intro s; convert right_ann (K := K) p ell s using 1 ; congr <;> exact Subsingleton.elim _ _)
    (by simpa only [Fintype.card_eq_nat_card] using high_small p M ell hp hM)
    (by simpa only [Fintype.card_eq_nat_card] using point_small p M hp hM)
    (by simpa only [Fintype.card_eq_nat_card] using high_large p ell hp hpell)
  exact h
end
end OddKaplansky.ModularSource

end

end OAI
