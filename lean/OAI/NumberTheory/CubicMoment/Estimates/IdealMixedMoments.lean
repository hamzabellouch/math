import OAI.NumberTheory.CubicMoment.Estimates.IdealCubicMoments

namespace OAI

/-! The ordinary mixed sieve on the normalized dual ideal blocks. All
coefficient bounds and the number of ideals are derived explicitly. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma ideal_support_card_le {S : Finset EisensteinIdealExponent} {Y : ℝ}
    (hY : 0 ≤ Y) (hS : ∀ ν ∈ S, idealExponentNorm ν ≤ Y) :
    (S.card : ℝ) ≤ 18*Y := by
  have hsub : S ⊆ fullIdealBall Y := fun ν hν => mem_fullIdealBall.mpr (hS ν hν)
  have hcard : S.card ≤ (nonzeroNormBall Y).card :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le)
  exact (Nat.cast_le.mpr hcard).trans (nonzeroNormBall_card_le hY)

lemma normalizedDualPolynomial_mixed (S : Finset EisensteinIdealExponent)
    (a b : Eisenstein) (J u : ℝ) :
    normalizedDualPolynomial S (fun ν => mixedCubic a b (idealExponentGenerator ν))
      idealExponentNorm J u =
      ∑ ν ∈ S, (((J/idealExponentNorm ν)^(1/2:ℝ):ℝ)*mellinPhase u (idealExponentNorm ν))*
        mixedCubic a b (idealExponentGenerator ν) := by
  unfold normalizedDualPolynomial
  apply Finset.sum_congr rfl
  intro ν hν
  ring

/-- Complete dual ideal supports, including the ramified prime, satisfy
the ordinary sieve bound uniformly in their common norm twist. -/
theorem normalized_ideal_mixed_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (Eisenstein × Eisenstein))
      (S : Finset EisensteinIdealExponent) (Q Y J u : ℝ),
      1 ≤ Q → 1 ≤ Y → 0 < J →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ Y) →
      (∑ p ∈ P, ‖normalizedDualPolynomial S
        (fun ν => mixedCubic p.1 p.2 (idealExponentGenerator ν))
        idealExponentNorm J u‖^2) ≤ C*Q^ε*(Q^2+Y)*Y := by
  obtain ⟨C,hC,hbound⟩ := ideal_mixed_moment hHuxley hε
  refine ⟨18*C,by positivity,?_⟩
  intro P S Q Y J u hQ hY hJ hP hS
  let v : EisensteinIdealExponent → ℂ := fun ν =>
    (((J/idealExponentNorm ν)^(1/2:ℝ):ℝ)*mellinPhase u (idealExponentNorm ν))
  have hv : ∀ ν ∈ S, ‖v ν‖ ≤ 1 := by
    intro ν hν
    dsimp [v]
    rw [norm_mul,mellinPhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (div_nonneg hJ.le (idealExponentNorm_pos ν).le) _)]
    exact dual_dyad_weight_le_one hJ (hS ν hν).1
  have henergy : (∑ ν ∈ S, ‖v ν‖^2) ≤ 18*Y := by
    calc
      _ ≤ ∑ _ν ∈ S, (1:ℝ) := Finset.sum_le_sum (fun ν hν => by
        simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (hv ν hν) 2)
      _ = (S.card : ℝ) := by simp
      _ ≤ 18*Y := ideal_support_card_le (by linarith) (fun ν hν => (hS ν hν).2)
  have h := hbound P S Q Y hQ hY hP (fun ν hν => (hS ν hν).2) v
  simp_rw [normalizedDualPolynomial_mixed]
  calc
    _ ≤ C*Q^ε*(Q^2+Y)*∑ ν ∈ S, ‖v ν‖^2 := h
    _ ≤ C*Q^ε*(Q^2+Y)*(18*Y) := mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
