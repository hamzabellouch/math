import OAI.Combinatorics.Ryser.Selection.Parameters
import OAI.Combinatorics.Ryser.Selection.SmallRange
import OAI.Combinatorics.Ryser.Selection.LargeCertificates
import OAI.Combinatorics.Ryser.Selection.UniformDensity

namespace OAI

universe u
noncomputable section
namespace RyserCoveringCounterexample.Selection

def smallCertificateBase (D q m : ℕ) : ℝ :=
  (2 * (m : ℝ)) * ((2 * (D : ℝ) ^ 3) / (q : ℝ))

def densityFailureBound (D q : ℕ) : ℝ :=
  (densityChunkCount D : ℝ) * Real.exp (-densityRate D * (q : ℝ) * Real.log (q : ℝ))

def certificateEventBound (D K q m : ℕ) : ℝ :=
  if (m : ℝ) ≤ selectionCutoff D * (q : ℝ) then
    smallCertificateBase D q m ^ ((K - 2) * m)
  else densityFailureBound D q + Real.exp (-(((K : ℝ) * densityDelta D - 2) * (m : ℝ)))

theorem certificateEventBound_nonneg (D K q m : ℕ) :
    0 ≤ certificateEventBound D K q m := by
  unfold certificateEventBound smallCertificateBase densityFailureBound
  split_ifs <;> positivity

theorem smallCertificateBase_eq (D q m : ℕ) :
    smallCertificateBase D q m = 2 * equationBound D * (m : ℝ) / (q : ℝ) := by
  unfold smallCertificateBase equationBound
  ring

theorem smallCertificateBase_le_half (D q m : ℕ) (hD : 1 ≤ D) (hq : 0 < q)
    (hsmall : (m : ℝ) ≤ selectionCutoff D * (q : ℝ)) :
    smallCertificateBase D q m ≤ 1 / 2 := by
  have hC := equationBound_pos D hD
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hfactor : 0 ≤ 2 * equationBound D / (q : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hC.le) hqr.le
  have hscaled := mul_le_mul_of_nonneg_left hsmall hfactor
  have hhalf : (2 * equationBound D / (q : ℝ)) *
      (selectionCutoff D * (q : ℝ)) = 1 / 2 := by
    unfold selectionCutoff
    field_simp [hC.ne', hqr.ne']; ring
  rw [hhalf] at hscaled
  rw [smallCertificateBase_eq]
  calc
    _ = (2 * equationBound D / (q : ℝ)) * (m : ℝ) := by ring
    _ ≤ 1 / 2 := hscaled

theorem exists_threshold_certificate_event_bound (D : ℕ) (hD : 1 ≤ D) (K : ℕ) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (n : ℕ) (data : Data F n), Bounded D data → Q ≤ Fintype.card F →
      ∀ (I : Finset (Fin n)) (T : Finset (Position n K)),
      T ⊆ targetPositions I K → T.card ≤ 2 * I.card →
      (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤
        certificateEventBound D K (Fintype.card F) I.card := by
  obtain ⟨Q, hQ⟩ := prob_feasibleMass_lt_densityDelta_le.{u} D hD K
  refine ⟨Q, ?_⟩
  intro F _ _ _ n data hdata hq I T hT hcard
  unfold certificateEventBound
  by_cases hsmall : (I.card : ℝ) ≤ selectionCutoff D * (Fintype.card F : ℝ)
  · rw [ite_eq_left hsmall]
    have hbase := smallCertificateBase_le_half D (Fintype.card F) I.card hD
      Fintype.card_pos hsmall
    exact prob_noFeasibleOutside_small_le data hdata I T hT hcard
      (hbase.trans (by norm_num))
  · rw [ite_eq_right hsmall]
    have hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card := by
      calc
        _ = selectionCutoff D * (Fintype.card F : ℝ) := by
          unfold selectionCutoff
          ring
        _ < I.card := lt_of_not_ge hsmall
    have hdensity := hQ F n data hdata hq I T hlarge hcard
    have hdensity' :
        (poolLaw F n K).prob (fun pool => (feasibleMass data I T pool : ℝ) <
          densityDelta D * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤
        densityFailureBound D (Fintype.card F) := by
      simpa only [densityFailureBound, mul_assoc] using hdensity
    exact (prob_noFeasibleOutside_le_density_bad_add_exp data I T (densityDelta D)
      hT hcard).trans (add_le_add hdensity' le_rfl)

end RyserCoveringCounterexample.Selection

end

end OAI
