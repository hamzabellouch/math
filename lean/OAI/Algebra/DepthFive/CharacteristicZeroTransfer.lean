import OAI.Algebra.DepthFive.ComplexEmbedding
import OAI.Algebra.DepthFive.CoefficientMap
import OAI.Algebra.DepthFive.ImmMap
import OAI.Algebra.DepthFive.CoefficientDescent

namespace OAI

noncomputable section
universe u

namespace Problem335

/-- A circuit over a countable characteristic-zero field can be realized over
`ℂ`, with exactly the same number of gates and the same IMM identity. -/
theorem exists_complex_circuit_of_countable {K : Type u} [Field K] [CharZero K]
    [Countable K] {n : ℕ} (c : Depth5Circuit K n)
    (hc : circuitValue c = imm K n) :
    ∃ d : Depth5Circuit ℂ n, circuitValue d = imm ℂ n ∧ circuitSize d = circuitSize c := by
  obtain ⟨f⟩ := countable_field_embeds_complex K
  refine ⟨c.mapCoefficients f, ?_, circuitSize_mapCoefficients f c⟩
  rw [circuitValue_mapCoefficients, hc, map_imm]

/-- Any pointwise real gate-count lower bound over `ℂ` transfers to every
countable field of characteristic zero. -/
theorem countable_circuit_bound_of_complex {K : Type u} [Field K] [CharZero K]
    [Countable K] {n : ℕ} {b : ℝ}
    (h : ∀ d : Depth5Circuit ℂ n,
      circuitValue d = imm ℂ n → b ≤ (circuitSize d : ℝ))
    (c : Depth5Circuit K n) (hc : circuitValue c = imm K n) :
    b ≤ (circuitSize c : ℝ) := by
  obtain ⟨d, hd, hs⟩ := exists_complex_circuit_of_countable c hc
  simpa only [hs] using h d hd

/-- Restriction to the coefficient subfield preserves and reflects the IMM identity. -/
theorem restrictCircuit_computes_imm {K : Type u} [Field K] {n : ℕ}
    (c : Depth5Circuit K n) :
    circuitValue (restrictCircuit c) = imm (circuitCoefficientField c) n ↔
      circuitValue c = imm K n := by
  have hi := MvPolynomial.map_injective (σ := Fin n × Fin n × Fin n)
    (circuitCoefficientField c).subtype
    (circuitCoefficientField c).subtype.injective
  rw [← hi.eq_iff, map_circuitValue_restrictCircuit, map_imm]

/-- Every characteristic-zero IMM circuit has a same-size complex realization.
Only the finitely many occurring coefficients are embedded, not the entire field. -/
theorem exists_complex_circuit {K : Type u} [Field K] [CharZero K]
    {n : ℕ} (c : Depth5Circuit K n) (hc : circuitValue c = imm K n) :
    ∃ d : Depth5Circuit ℂ n, circuitValue d = imm ℂ n ∧ circuitSize d = circuitSize c := by
  obtain ⟨d, hd, hs⟩ := exists_complex_circuit_of_countable (restrictCircuit c)
    ((restrictCircuit_computes_imm c).mpr hc)
  exact ⟨d, hd, hs.trans (circuitSize_restrictCircuit c)⟩

/-- Pointwise complex gate lower bounds hold over any characteristic-zero field. -/
theorem circuit_bound_of_complex {K : Type u} [Field K] [CharZero K]
    {n : ℕ} {b : ℝ}
    (h : ∀ d : Depth5Circuit ℂ n,
      circuitValue d = imm ℂ n → b ≤ (circuitSize d : ℝ))
    (c : Depth5Circuit K n) (hc : circuitValue c = imm K n) :
    b ≤ (circuitSize c : ℝ) := by
  obtain ⟨d, hd, hs⟩ := exists_complex_circuit c hc
  simpa only [hs] using h d hd

/-- The extension to characteristic zero uses the same absolute threshold as
its complex counterpart. This implication has no lower-bound assumptions other
than the precise complex conclusion. -/
theorem characteristic_zero_depth_five_lower_bound_of_complex
    (h : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ)) :
    ∃ n0 : ℕ, ∀ (K : Type u) [Field K] [CharZero K], ∀ n : ℕ, n0 ≤ n →
      ∀ c : Depth5Circuit K n, circuitValue c = imm K n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  obtain ⟨n0, h0⟩ := h
  refine ⟨n0, ?_⟩
  intro K _ _ n hn c hc
  exact circuit_bound_of_complex (h0 n hn) c hc

end Problem335

end

end OAI
