import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeRegroup
import OAI.NumberTheory.CubicMoment.Estimates.UpperTailGrouping

namespace OAI

/-! All coordinate assumptions for the independent Gauss-tail prime box
follow from one surviving original tuple. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

theorem tailPrimeTuplePiece_rough_scales (i j : ℕ) {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H U : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      ∀ q ∈ largePrimeTupleBox i j X,
        tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        (∀ a, 1 ≤ largeTupleNormScale (fun a => (k a).val) a) ∧
        ∀ B : ℝ, 0 ≤ B → B ≤ 3*X → ∀ a,
          (2*B)^(ξ/2) < largeTupleNormScale (fun a => (k a).val) a := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hξ).eventually_ge_atTop 2,
    eventually_const_mul_rpow_le (by linarith : ξ/2 < ξ) (2*6^(ξ/2))]
    with X hX hXtwo hgap
  intro ℓ H U N k q hq hne
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hscale (a : Fin i ⊕ Fin j) :
      X^ξ/2 < largeTupleNormScale (fun a => (k a).val) a := by
    have hrough := tailPrimeTupleNorm_rough hX hξz hq ht a
    have hup := (largePrimeTuplePiece_coordinate_range k hw a).2
    linarith
  refine ⟨fun a => (by linarith [hscale a]),?_⟩
  intro B hB hBX a
  calc
    (2*B)^(ξ/2) ≤ (6*X)^(ξ/2) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ = 6^(ξ/2)*X^(ξ/2) := Real.mul_rpow (by norm_num) hXp.le
    _ ≤ X^ξ/2 := by linarith
    _ < largeTupleNormScale (fun a => (k a).val) a := hscale a


lemma tailPrimeTuplePiece_witness {i j : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hne : tailPrimeTuplePiece i j ℓ ξ H U X k ≠ 0) :
    ∃ q ∈ largePrimeTupleBox i j X,
      tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  unfold tailPrimeTuplePiece
  rw [Finset.sum_eq_zero h,mul_zero]

theorem eventually_tailPrimeTuple_coordinate_envelope {i j : ℕ} {κ ξ : ℝ}
    (hκ : 0 ≤ κ) (hκsmall : κ < 1/12) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H U : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      ∀ q ∈ largePrimeTupleBox i j X,
        tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        ∀ a, 2*largeTupleNormScale (fun a => (k a).val) a ≤ Real.exp primeProductWeights.radius*X := by
  have hC : 0 < Real.exp primeProductWeights.radius/6 := by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_rpow_le_const_mul (show (2/3+2*κ:ℝ) < 1 by linarith) hC]
    with X hX hgap
  intro ℓ H U N k hhigh q hq hne a
  have hw := (mul_ne_zero_iff.mp hne).2
  have hlo := (largePrimeTuplePiece_coordinate_range k hw a).1
  have hhi := tailPrimeTupleNorm_upper hX hκ hξz k hhigh hq hne a
  rw [Real.rpow_one] at hgap
  nlinarith

theorem eventually_tailPrimeTuplePiece_full {i j : ℕ} {κ ξ : ℝ}
    (hκ : 0 ≤ κ) (hκsmall : κ < 1/12) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H U : ℝ)
      (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      tailPrimeTuplePiece i j ℓ ξ H U X k ≠ 0 →
      tailPrimeTuplePiece i j ℓ ξ H U X k =
        ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
          tailPrimeTupleIndependentSum i j ℓ ξ H U X (fun a => (k a).val) := by
  filter_upwards [eventually_tailPrimeTuple_coordinate_envelope hκ hκsmall hξz] with X hcoord
  intro ℓ H U k hhigh hne
  obtain ⟨q,hq,hqne⟩ := tailPrimeTuplePiece_witness k hne
  exact tailPrimeTuplePiece_full i j ℓ ξ H U X k (hcoord ℓ H U k hhigh q hq hqne)

end CubicFirstMoment

end

end OAI
