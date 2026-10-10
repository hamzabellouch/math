import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleDirectMaster_budget (nStages A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type*} [Fintype K] {P Pchart D pRadius Qstride Pphysical : ℝ}
      {u pModel Prho target gainLog : K → ℝ},
      Fintype.card K ≤ nStages → 0 ≤ P →
      Pchart ≤ (P + A) ^ A → D ≤ (P + A) ^ A → pRadius ≤ (P + A) ^ A →
      Qstride ≤ (P + A) ^ A → Pphysical ≤ (P + A) ^ A →
      (∀ k, u k ≤ (P + A) ^ A) → (∀ k, pModel k ≤ (P + A) ^ A) →
      (∀ k, Prho k ≤ (P + A) ^ A) → (∀ k, target k ≤ (P + A) ^ A) →
      (∀ k, gainLog k ≤ (P + A) ^ A) →
      preparedFiniteScheduleDirectMaster Pchart D pRadius Qstride Pphysical
        u pModel Prho target gainLog ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let b := (X + Polynomial.C A) ^ A
  let poly := 5 * b + Polynomial.C nStages * (12 * b + 44)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro K _ P Pchart D pRadius Qstride Pphysical u pModel Prho target gainLog
    hK hP hchart hD hradius hstride hphysical hu hmodel hrho htarget hgain
  have hsum : (∑ k, (u k + pModel k + allocatedModelTestLog (u k) (pModel k) +
      Prho k + target k + gainLog k + 32)) ≤
      (nStages : ℝ) * (12 * (P + A) ^ A + 44) := by
    calc
      _ ≤ ∑ _k : K, (12 * (P + A) ^ A + 44) := by
        apply Finset.sum_le_sum
        intro k _
        unfold allocatedModelTestLog
        linarith only [hu k, hmodel k, hrho k, htarget k, hgain k]
      _ = (Fintype.card K : ℝ) * (12 * (P + A) ^ A + 44) := by simp [mul_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) (by positivity)
  have htotal : preparedFiniteScheduleDirectMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog ≤
      5 * (P + A) ^ A + (nStages : ℝ) * (12 * (P + A) ^ A + 44) := by
    unfold preparedFiniteScheduleDirectMaster
    linarith only [hchart, hD, hradius, hstride, hphysical, hsum]
  apply htotal.trans
  simpa [poly, X, b, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleLocalMaster_budget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {P Pchart D pRadius Qstride Pphysical u pModel Prho target gainLog : ℝ},
      0 ≤ P →
      Pchart ≤ (P + A) ^ A → D ≤ (P + A) ^ A → pRadius ≤ (P + A) ^ A →
      Qstride ≤ (P + A) ^ A → Pphysical ≤ (P + A) ^ A →
      u ≤ (P + A) ^ A → pModel ≤ (P + A) ^ A →
      Prho ≤ (P + A) ^ A → target ≤ (P + A) ^ A → gainLog ≤ (P + A) ^ A →
      preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride Pphysical
        u pModel Prho target gainLog ≤ (P + C) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteScheduleDirectMaster_budget 1 A
  refine ⟨C, hC, ?_⟩
  intro P Pchart D pRadius Qstride Pphysical u pModel Prho target gainLog
    hP hchart hD hradius hstride hphysical hu hmodel hrho htarget hgain
  have h := hbound (K := Unit)
    (u := fun _ => u) (pModel := fun _ => pModel) (Prho := fun _ => Prho)
    (target := fun _ => target) (gainLog := fun _ => gainLog)
    (by simp) hP hchart hD hradius hstride hphysical
    (fun _ => hu) (fun _ => hmodel) (fun _ => hrho) (fun _ => htarget) (fun _ => hgain)
  simpa only [preparedFiniteScheduleDirectMaster, preparedFiniteScheduleLocalMaster,
    Finset.univ_unique, Finset.sum_singleton] using h

end Erdos3.VectorPolynomial

end

end OAI
