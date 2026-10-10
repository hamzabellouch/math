import OAI.Geometry.SurfaceImmersion.Correction.ModulatedPolynomialJets

namespace OAI

/-! A uniform finite-order budget for all demodulated jet slots. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

def amplitudeBudget (N m : ℕ) (B P : ℝ) : ℝ :=
  1 + B + ∑ r ∈ Finset.range (N + 1), jetConstant P m r

lemma amplitudeBudget_ge_one {N m : ℕ} {B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) :
    1 ≤ amplitudeBudget N m B P := by
  have hsum := Finset.sum_nonneg (s := Finset.range (N + 1))
    (fun r _ => jetConstant_nonneg hP m r)
  dsimp only [amplitudeBudget]
  linarith

lemma le_amplitudeBudget {N m : ℕ} {B P : ℝ} (hP : 0 ≤ P) :
    B ≤ amplitudeBudget N m B P := by
  have hsum := Finset.sum_nonneg (s := Finset.range (N + 1))
    (fun r _ => jetConstant_nonneg hP m r)
  dsimp only [amplitudeBudget]
  linarith

lemma jetConstant_le_amplitudeBudget {N m r : ℕ} {B P : ℝ}
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hr : r ≤ N) :
    jetConstant P m r ≤ amplitudeBudget N m B P := by
  have h := Finset.single_le_sum (fun a _ => jetConstant_nonneg hP m a)
    (show r ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
  dsimp only [amplitudeBudget]
  linarith

theorem weighted_amplitudeData {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) {τ s B P : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (m N : ℕ) (hGb : WeightedBound U s (m + N) B (lowJet G))
    (hHb : ∀ j, WeightedBound U s (m + N) 1 (H j))
    (hφb : ∀ j v, WeightedBound U s (m + N) P (fun p => fderiv ℝ (φ j) p (coordinateVector v)))
    (i : Fin 4) (w : List (Fin 2)) (a : Fin 4) (hw : w.length ≤ N) :
    WeightedBound U s m (amplitudeBudget N m B P / τ ^ slotLoss i w)
      (amplitudeData G φ H τ i w a) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hj := weighted_actual_jet hU hG hs hB m w a (hGb.mono_order (by omega))
    have hc := weighted_complexify hU.uniqueDiffOn hs.le (by positivity)
      (jet_smooth hG w a).contDiffOn hj
    apply hc.mono_const
    calc
      B / s ^ (w.length - 2) ≤ B / τ ^ (w.length - 2) :=
        div_le_div_of_nonneg_left hB (pow_pos hτ _) (pow_le_pow_left₀ hτ.le hτs _)
      _ ≤ _ := div_le_div_of_nonneg_right (le_amplitudeBudget hP) (pow_nonneg hτ.le _)
  · have hcomp := (hHb j).component hU.uniqueDiffOn hs.le zero_le_one (hH j).contDiffOn a
    have hc := weighted_amplitudeJet hU hτ hs hτs zero_le_one hP
      (hφ j) (contDiff_pi.mp (hH j) a) (w.map coordinateVector)
      (fun v hv => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
        exact norm_coordinateVector_le v) m
      (hcomp.mono_order (by simp only [List.length_map]; omega))
      (fun v hv => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
        exact (hφb j v).mono_order (by simp only [List.length_map]; omega))
    simp only [List.length_map, mul_one] at hc
    apply hc.mono_const
    exact div_le_div_of_nonneg_right (jetConstant_le_amplitudeBudget hB hP hw)
      (pow_nonneg hτ.le _)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
