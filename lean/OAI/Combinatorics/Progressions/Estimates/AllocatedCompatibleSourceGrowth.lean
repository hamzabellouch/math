import OAI.Combinatorics.Progressions.Dynamics.AllocatedCompatibleSourceBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedCompatibleSourceLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p c P e E : ℝ}, 0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ e → 0 ≤ E →
      allocatedCompatibleSourceLog m p c P e E ≤ (p + c + P + e + E + a) ^ a := by
  obtain ⟨a, _ha, hcommon⟩ := exists_allocatedCommonSourceLog_bound m
  let poly : Polynomial ℕ :=
    canonicalScalarSourceLog m (allocatedRefinedPeriodLog m Polynomial.X + 1) +
      (Polynomial.X + ((a + 5 : ℕ) : Polynomial ℕ)) ^ a +
      allocatedOriginalCoverAccuracy Polynomial.X (Polynomial.X + 1) + 4
  obtain ⟨b, hb, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨b, hb, ?_⟩
  intro p c P e E hp hc hP he hE
  let s := p + c + P + e + E
  have hs : 0 ≤ s := by positivity
  have hPs : P ≤ s := by dsimp only [s]; linarith
  have hEs : E ≤ s := by dsimp only [s]; linarith
  have hc0 := hcommon hp hc hP he (show 0 ≤ E + 5 by linarith)
  have hc1 : allocatedCommonSourceLog m p c P e (E + 5) ≤ (s + (a + 5 : ℕ)) ^ a := by
    convert hc0 using 1
    push_cast
    dsimp only [s]
    ring
  have hcanon : canonicalScalarSourceLog m (allocatedRefinedPeriodLog m P + 1) ≤
      canonicalScalarSourceLog m (allocatedRefinedPeriodLog m s + 1) := by
    unfold canonicalScalarSourceLog allocatedRefinedPeriodLog
    gcongr
  have hacc : allocatedOriginalCoverAccuracy P (E + 1) ≤
      allocatedOriginalCoverAccuracy s (s + 1) := by
    unfold allocatedOriginalCoverAccuracy coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  have htotal : allocatedCompatibleSourceLog m p c P e E ≤
      canonicalScalarSourceLog m (allocatedRefinedPeriodLog m s + 1) +
        (s + (a + 5 : ℕ)) ^ a + allocatedOriginalCoverAccuracy s (s + 1) + 4 :=
    add_le_add (add_le_add (add_le_add hcanon hc1) hacc) le_rfl
  apply htotal.trans
  simpa [poly, canonicalScalarSourceLog, allocatedRefinedPeriodLog,
    allocatedOriginalCoverAccuracy, coefficientErrorSpatialLog, coefficientErrorVolumeLog,
    anisotropicSpatialCapLog, Polynomial.eval₂_pow] using hpoly s hs

end Erdos3.VectorPolynomial

end

end OAI
