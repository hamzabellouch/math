import OAI.Analysis.KadisonKastler.RescaledTomitaGraph

namespace OAI

/-! # Selecting a normalized vector in a rescaled graph

If a nonzero operator is supported on the closed graph, one of the
defining graph vectors retains more than half its operator norm. The
algebra element can then be rescaled to make its graph vector a unit
vector. This is the signal-selection step used before finite averaging.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A graph-supported nonzero operator has a normalized defining graph
vector on which it retains more than half its norm. -/
theorem exists_normalized_rescaledGraph_signal
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (hT : T ≠ 0)
    (hsupport : T * rescaledGraphProjection P J Ω c = T) :
    ∃ x : Algebra P, ‖rescaledGraphVector J Ω c x.val‖ = 1 ∧
      ‖T‖ / 2 < ‖T (rescaledGraphVector J Ω c x.val)‖ := by
  have hnorm : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hlarge : ¬ ∀ x : Algebra P,
      ‖T (rescaledGraphVector J Ω c x.val)‖ ≤
        (‖T‖ / 2) * ‖rescaledGraphVector J Ω c x.val‖ := by
    intro hb
    have hh := norm_comp_rescaledGraphProjection_le P J Ω c T (by positivity) hb
    rw [hsupport] at hh
    linarith
  push Not at hlarge
  obtain ⟨x, hx⟩ := hlarge
  let v := rescaledGraphVector J Ω c x.val
  have hv : 0 < ‖v‖ := by
    by_contra hn
    have hz : v = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg v))
    change (‖T‖ / 2) * ‖v‖ < ‖T v‖ at hx
    have hfalse : (0 : ℝ) < 0 := by
      simpa only [hz, norm_zero, map_zero, mul_zero] using hx
    exact (lt_irrefl 0) hfalse
  let a : ℝ := ‖v‖⁻¹
  let y : Algebra P := (a : ℂ) • x
  have he : rescaledGraphVector J Ω c y.val = (a : ℂ) • v := by
    exact (rescaledGraphMap P J Ω c).map_smul (a : ℂ) x
  have ha : 0 < a := inv_pos.mpr hv
  have hanorm : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hnormalize : a * ‖v‖ = 1 := inv_mul_cancel₀ (ne_of_gt hv)
  refine ⟨y, ?_, ?_⟩
  · rw [he, norm_smul, hanorm]
    exact hnormalize
  · have hh := mul_lt_mul_of_pos_left hx ha
    change a * ((‖T‖ / 2) * ‖v‖) < a * ‖T v‖ at hh
    rw [he, map_smul, norm_smul, hanorm]
    calc
      ‖T‖ / 2 = a * ((‖T‖ / 2) * ‖v‖) := by
        calc
          _ = (‖T‖ / 2) * (a * ‖v‖) := by rw [hnormalize, mul_one]
          _ = _ := by ring
      _ < a * ‖T v‖ := hh

end

end KadisonKastler

end OAI
