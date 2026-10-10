import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale

namespace OAI

/-! The tuple/padding pair catalog injects into its integer product:
the two factors have disjoint prime supports. Thus the numerical bin
endpoint bounds the whole catalog, without an extra tuple factor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma ProhibitedPrimeFamily.pair_cross_coprime {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (a b : data.pairs) : a.val.1.Coprime b.val.2 := by
  apply (Nat.disjoint_primeFactors (data.tuple_squarefree _ a.property).ne_zero
    (data.padding_squarefree _ b.property).ne_zero).mp
  exact data.disjoint.mono (data.tuple_pool _ a.property) (data.padding_pool _ b.property)

lemma ProhibitedPrimeFamily.pair_product_injective {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) :
    Function.Injective (fun a : data.pairs => a.val.1 * a.val.2) := by
  intro a b hab
  change a.val.1 * a.val.2 = b.val.1 * b.val.2 at hab
  have hdab : a.val.1 ∣ b.val.1 := (data.pair_cross_coprime a b).dvd_of_dvd_mul_right
    (hab ▸ dvd_mul_right a.val.1 a.val.2)
  have hdba : b.val.1 ∣ a.val.1 := (data.pair_cross_coprime b a).dvd_of_dvd_mul_right
    (hab.symm ▸ dvd_mul_right b.val.1 b.val.2)
  have hd : a.val.1 = b.val.1 := Nat.dvd_antisymm hdab hdba
  have hq : a.val.2 = b.val.2 := by
    rw [← hd] at hab
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (data.tuple_squarefree _ a.property).ne_zero) hab
  exact Subtype.ext (Prod.ext hd hq)

lemma ProhibitedPrimeFamily.pairs_card_le {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (B : ℕ)
    (hB : ∀ dq ∈ data.pairs, dq.1 * dq.2 ≤ B) : data.pairs.card ≤ B := by
  have hp (a : data.pairs) : 0 < a.val.1 * a.val.2 :=
    Nat.mul_pos (Nat.pos_of_ne_zero (data.tuple_squarefree _ a.property).ne_zero)
      (Nat.pos_of_ne_zero (data.padding_squarefree _ a.property).ne_zero)
  let f : data.pairs → Fin B := fun a =>
    ⟨a.val.1 * a.val.2 - 1, by have := hp a; have := hB _ a.property; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply data.pair_product_injective
    change a.val.1 * a.val.2 = b.val.1 * b.val.2
    have he : a.val.1 * a.val.2 - 1 = b.val.1 * b.val.2 - 1 := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    omega
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma paddingPairEligible_product_upper {L η : ℝ} {d q : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (he : PaddingPairEligible L η d q) :
    d * q ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
  by_cases hz : d * q = 0
  · simp [hz]
  let j := paddingBin η 0 (Real.log (d * q : ℕ))
  have hj := (mem_paddingBinIndices_iff L η j hη).mp he.2
  have hx := (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mp rfl
  simp only [add_zero] at hx
  have hu : Real.log (d * q : ℕ) ≤ 100 * L + 1 := by
    nlinarith [hj.2, hx.2]
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hp : (0 : ℝ) < (d * q : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hu

lemma actualProhibitedPrimeFamily_pairs_card (h J M : ℕ) (E : Finset ℕ)
    (A W L η : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (hL : 1 ≤ L)
    (hη : 0 < η) (hηone : η ≤ 1)
    (he : ∀ d q, eligible d q → PaddingPairEligible L η d q) :
    ((actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).pairs.card : ℝ) ≤
      Real.exp (101 * L) := by
  let data := actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE
  have hb : data.pairs.card ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
    apply data.pairs_card_le
    intro dq hdq
    have hm := (actualProhibitedPrimeFamily_pairs h J M E A W L eligible hA hW hE
      dq.1 dq.2).mp hdq
    exact paddingPairEligible_product_upper hη hηone (he _ _ hm.2.2.2)
  have hbr : (data.pairs.card : ℝ) ≤ (⌊Real.exp (100 * L + 1)⌋₊ : ℝ) := by exact_mod_cast hb
  exact (hbr.trans (Nat.floor_le (Real.exp_pos _).le)).trans
    (Real.exp_le_exp.mpr (by linarith))

end TwoPointCorrelations

end OAI
