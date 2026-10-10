import OAI.NumberTheory.Ostmann.Arithmetic.CRTLineAverage

namespace OAI

/-! # Exact products of the internal-prime line probabilities -/

namespace Ostmann

open scoped BigOperators

private theorem uniform_indicator_probability {X : Type*} [Fintype X]
    (P : X → Prop) [DecidablePred P] :
    (Fintype.card X : ℝ)⁻¹ * (∑ x, if P x then (1 : ℝ) else 0) =
      (Fintype.card {x : X // P x} : ℝ) / Fintype.card X := by
  have h : (∑ x, if P x then (1 : ℝ) else 0) = (Fintype.card {x : X // P x} : ℝ) := by
    rw [Fintype.card_subtype]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h, div_eq_mul_inv, mul_comm]

/-- In the prime environment every feasible local line contributes exactly
`1/(p-1)`, and the factors multiply over all distinct internal primes. -/
theorem crt_unit_lines_probability {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (a b : ∀ i, (ZMod (p i))ˣ) :
    (Fintype.card ((ZMod (∏ i, p i))ˣ × (ZMod (∏ i, p i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, if a i * (crtUnitPairEquiv p hc z i).1 =
          b i * (crtUnitPairEquiv p hc z i).2 then (1 : ℝ) else 0) =
    ∏ i, (Fintype.card (ZMod (p i))ˣ : ℝ)⁻¹ := by
  classical
  rw [crt_unit_pair_average p hc (fun i z => if a i * z.1 = b i * z.2 then (1 : ℝ) else 0)]
  apply Finset.prod_congr rfl
  intro i _
  rw [uniform_indicator_probability]
  exact unitLine_probability (a i) (b i)

/-- In the external-integer environment every feasible line contributes
`1/p`, including a zero second coefficient. -/
theorem crt_external_lines_probability {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (a : ∀ i, (ZMod (p i))ˣ) (b : ∀ i, ZMod (p i)) :
    (Fintype.card (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, if (a i : ZMod (p i)) * (crtExternalPairEquiv p hc z i).1 =
          b i * (crtExternalPairEquiv p hc z i).2 then (1 : ℝ) else 0) =
    ∏ i, (p i : ℝ)⁻¹ := by
  classical
  rw [crt_external_pair_average p hc
    (fun i z => if (a i : ZMod (p i)) * z.1 = b i * z.2 then (1 : ℝ) else 0)]
  apply Finset.prod_congr rfl
  intro i _
  rw [uniform_indicator_probability]
  exact externalLine_probability (a i) (b i)

end Ostmann

end OAI
