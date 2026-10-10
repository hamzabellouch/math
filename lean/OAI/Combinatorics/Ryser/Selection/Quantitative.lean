import OAI.Combinatorics.Ryser.Selection.CertificateBounds
import OAI.Combinatorics.Ryser.Selection.CertificateUnion
import OAI.Combinatorics.Ryser.Selection.LayerNormalization
import OAI.Combinatorics.Ryser.Selection.LayerBounds
import OAI.Combinatorics.Ryser.Selection.NumericLimits

namespace OAI

universe u
noncomputable section
open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem layer_count_le_bounded (D n K q m : ℕ) (hn : n ≤ D * q) :
    (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m ≤
      (Real.exp 1 * (D : ℝ) * (q : ℝ) / (m : ℝ)) ^ m *
        (3 * (K : ℝ) ^ 2) ^ m := by
  have hnreal : (n : ℝ) ≤ (D : ℝ) * (q : ℝ) := by exact_mod_cast hn
  have hbase : Real.exp 1 * (n : ℝ) / (m : ℝ) ≤
      Real.exp 1 * (D : ℝ) * (q : ℝ) / (m : ℝ) := by
    simpa only [mul_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnreal (Real.exp_pos 1).le) (Nat.cast_nonneg m)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hbase m) (by positivity)

theorem exists_threshold_selection_failure_bound (D : ℕ) (hD : 1 ≤ D)
    (K : ℕ) (hK : 6 ≤ K)
    (hsmall : selectionSmallCoefficient D K * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2)
    (hlarge : selectionLargeCoefficient D K *
      Real.exp (2 - (K : ℝ) * densityDelta D) ≤ 1 / 2) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (n : ℕ) (data : Data F n), Bounded D data → Q ≤ Fintype.card F → ∀ R : ℕ,
      (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) ≤
        selectionFailureBound D K R (selectionSmallCoefficient D K)
          (max 1 (selectionLargeCoefficient D K)) (equationBound D)
          (densityChunkCount D : ℝ) (densityRate D) (selectionCutoff D)
          (Fintype.card F) := by
  classical
  obtain ⟨Q, hQ⟩ := exists_threshold_certificate_event_bound.{u} D hD K
  refine ⟨Q, ?_⟩
  intro F _ _ _ n data hdata hq R
  let q := Fintype.card F
  let S := (Finset.range (n + 1)).filter (fun m => 0 < m)
  let A := selectionSmallCoefficient D K
  let B := selectionLargeCoefficient D K
  let C := equationBound D
  let c1 := selectionCutoff D
  let J := (densityChunkCount D : ℝ)
  let c := densityRate D
  let delta := densityDelta D
  have hqpos : 0 < q := Fintype.card_pos
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hqpos
  have hA : 0 ≤ A := selectionSmallCoefficient_nonneg D K hD
  have hB : 0 ≤ B := selectionLargeCoefficient_nonneg D K hD
  have hC : 0 < C := equationBound_pos D hD
  have hc1 : 0 < c1 := selectionCutoff_pos D hD
  have hpos (m : ℕ) (hm : m ∈ S) : 0 < m := (Finset.mem_filter.mp hm).2
  have hsize (m : ℕ) (hm : m ∈ S) : m ≤ D * q := by
    have hmle : m ≤ n := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
    exact hmle.trans hdata.1
  have hprob := prob_not_hasCompatibleChoice_le_size_sum data (by omega : 0 < K)
    (certificateEventBound D K q) (certificateEventBound_nonneg D K q)
    (fun I _ T hT hcard => hQ F n data hdata hq I T hT hcard)
  have hpointwise (m : ℕ) (hm : m ∈ S) :
      ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) *
          certificateEventBound D K q m ≤
        if (m : ℝ) ≤ c1 * (q : ℝ) then
          (A * (2 * C * (m : ℝ) / (q : ℝ)) ^ (K - 3)) ^ m
        else B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
          Real.exp (-(((K : ℝ) * delta - 2) * (m : ℝ)))) := by
    have hcount := mul_le_mul_of_nonneg_right
      (layer_count_le_bounded D n K q m hdata.1)
      (certificateEventBound_nonneg D K q m)
    refine hcount.trans ?_
    by_cases hmrange : (m : ℝ) ≤ c1 * (q : ℝ)
    · rw [ite_eq_left hmrange]
      have hevent : certificateEventBound D K q m =
          (2 * C * (m : ℝ) / (q : ℝ)) ^ ((K - 2) * m) := by
        rw [certificateEventBound, ite_eq_left hmrange, smallCertificateBase_eq]
      rw [hevent]
      exact le_of_eq (by
        simpa only [A, selectionSmallCoefficient, selectionSmallFactor, C] using
          small_layer_coefficient_identity m K C (D : ℝ) (q : ℝ)
            (hpos m hm) (by omega) hqr)
    · rw [ite_eq_right hmrange]
      have hevent : certificateEventBound D K q m =
          J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
            Real.exp (-(((K : ℝ) * delta - 2) * (m : ℝ))) := by
        rw [certificateEventBound, ite_eq_right hmrange]
        rfl
      rw [hevent]
      apply mul_le_mul_of_nonneg_right
      · simpa only [B, selectionLargeCoefficient, selectionLargeFactor, c1] using
          large_layer_count_le m K (D : ℝ) (q : ℝ) c1 (hpos m hm)
            (Nat.cast_nonneg D) hqr hc1 (lt_of_not_ge hmrange)
      · exact le_trans (certificateEventBound_nonneg D K q m) (le_of_eq hevent)
  have hsmallSum := small_certificate_sum_le
    (S.filter (fun m => (m : ℝ) ≤ c1 * (q : ℝ))) K R A C (q : ℝ)
    hA hC.le hqr
    (fun m hm => Nat.succ_le_of_lt (hpos m (Finset.mem_filter.mp hm).1))
    (fun m hm => by
      simpa only [smallCertificateBase_eq] using
        smallCertificateBase_le_half D q m hD hqpos (Finset.mem_filter.mp hm).2)
    hsmall
  have hlargeSum := large_layer_sum_le
    (S.filter (fun m => ¬(m : ℝ) ≤ c1 * (q : ℝ))) D K q B J c c1 delta
    hB (Nat.cast_nonneg _) hc1
    (fun m hm => Nat.succ_le_of_lt (hpos m (Finset.mem_filter.mp hm).1))
    (fun m hm => hsize m (Finset.mem_filter.mp hm).1)
    (fun m hm => lt_of_not_ge (Finset.mem_filter.mp hm).2) hlarge
  calc
    _ ≤ ∑ m ∈ S,
        ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) *
          certificateEventBound D K q m := hprob
    _ ≤ ∑ m ∈ S, if (m : ℝ) ≤ c1 * (q : ℝ) then
        (A * (2 * C * (m : ℝ) / (q : ℝ)) ^ (K - 3)) ^ m
      else B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
        Real.exp (-(((K : ℝ) * delta - 2) * (m : ℝ)))) :=
      Finset.sum_le_sum hpointwise
    _ = (∑ m ∈ S.filter (fun m : ℕ => (m : ℝ) ≤ c1 * (q : ℝ)),
        (A * (2 * C * (m : ℝ) / (q : ℝ)) ^ (K - 3)) ^ m) +
      ∑ m ∈ S.filter (fun m : ℕ => ¬(m : ℝ) ≤ c1 * (q : ℝ)),
        B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
          Real.exp (-(((K : ℝ) * delta - 2) * (m : ℝ)))) :=
      Finset.sum_ite _ _
    _ ≤ ((R : ℝ) * A * (2 * C * (R : ℝ) / (q : ℝ)) ^ (K - 3) +
        (1 / 2 : ℝ) ^ R) +
      (J * ((D : ℝ) * (q : ℝ)) * (max 1 B) ^ (D * q) *
        Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
        (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ))) := add_le_add hsmallSum hlargeSum
    _ = _ := by simp only [selectionFailureBound, A, B, C, J, c, c1, q]; ring

end RyserCoveringCounterexample.Selection

end

end OAI
