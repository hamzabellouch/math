import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneL2Lift

namespace OAI

/-! A common compact spatial support gives finite-time L2 bounds and
continuity for each smooth prescribed drift component. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set Filter
open scoped Topology

theorem compact_family_square_envelope {F : ℝ → Plane → ℝ}
    (hF : Continuous (Function.uncurry F)) {K : Set Plane} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F t x = 0) (T : ℝ) :
    ∃ b : Plane → ℝ, Integrable (fun x => b x ^ 2) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |F t x| ≤ b x := by
  classical
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).prod hK).bddAbove_image hF.norm.continuousOn
  let C := max 0 B
  let b : Plane → ℝ := K.indicator (fun _ => C)
  refine ⟨b, ?_, ?_⟩
  · have hi : Integrable (K.indicator (fun _ : Plane => C ^ 2)) :=
      (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
    convert hi using 1
    funext x
    by_cases hx : x ∈ K <;> simp [b, hx]
  · intro t ht x
    by_cases hx : x ∈ K
    · have hb := hB ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      change ‖F t x‖ ≤ B at hb
      simpa only [b, indicator_of_mem hx, Real.norm_eq_abs] using hb.trans (le_max_right 0 B)
    · simp [b, hx, hz t x hx]

theorem compact_family_memLp {F : ℝ → Plane → ℝ}
    (hF : Continuous (Function.uncurry F)) {K : Set Plane} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F t x = 0) (t : ℝ) : MemLp (F t) 2 volume := by
  have hc : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  exact hc.memLp_of_hasCompactSupport (HasCompactSupport.intro hK (hz t))

theorem compact_family_continuousL2 {F : ℝ → Plane → ℝ}
    (hF : Continuous (Function.uncurry F)) {K : Set Plane} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F t x = 0) (T : ℝ) :
    ∃ U : ℝ → PlaneL2, ContinuousOn U (Icc 0 T) ∧
      ∀ t ∈ Icc (0 : ℝ) T, (fun x => U t x) =ᵐ[volume] F t := by
  obtain ⟨b, hb, hbound⟩ := compact_family_square_envelope hF hK hz T
  apply exists_planeL2_continuous_representation
    (fun t _ => compact_family_memLp hF hK hz t)
  exact squareDistanceContinuousOn_of_envelope
    (fun t _ => hF.comp (continuous_const.prodMk continuous_id))
    (fun x => (hF.comp (continuous_id.prodMk continuous_const)).continuousOn) hb hbound

end ForcedComputation.VelocityDetector

end

end OAI
