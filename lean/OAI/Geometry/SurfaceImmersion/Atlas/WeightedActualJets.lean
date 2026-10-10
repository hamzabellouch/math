import OAI.Geometry.SurfaceImmersion.Geometry.JetWordDecomposition

namespace OAI

/-! Actual jets have precisely one scale loss per derivative beyond the
controlled second jet, with no loss for their first two derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma norm_coordinateVector_le (v : Fin 2) : ‖coordinateVector v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  by_cases h : i = v
  · subst i
    simp [coordinateVector]
  · simp [coordinateVector, h]

/-- A weighted bound on the second-jet map controls every actual higher jet. -/
theorem weighted_actual_jet {U : Set Base} (hU : IsOpen U) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + (w.length - 2)) B (lowJet G)) :
    WeightedBound U s m (B / s ^ (w.length - 2)) (jet G w a) := by
  obtain ⟨v, i, hv, he⟩ := jet_as_lowJet_derivative w a
  rw [he G]
  have hQ := (lowJet_smooth hG).contDiffOn (s := U)
  have hcomp := hb.component hU.uniqueDiffOn hs.le hB hQ (Sum.inr (i, a))
  have hf : ContDiffOn ℝ ∞ (fun p => lowJet G p (Sum.inr (i, a))) U :=
    (contDiff_pi.mp (lowJet_smooth hG) (Sum.inr (i, a))).contDiffOn
  have hvnorm : ∀ x ∈ v.map coordinateVector, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact norm_coordinateVector_le j
  have hcomp' : WeightedBound U s (m + (v.map coordinateVector).length) B
      (fun p => lowJet G p (Sum.inr (i, a))) := by
    simpa only [List.length_map, hv] using hcomp
  have hd := hcomp'.iteratedDirectional hU hs hB hf (v.map coordinateVector) hvnorm m
  simpa only [List.length_map, hv] using hd

end ClosedSurfaceR4.JetPolynomial

end

end OAI
