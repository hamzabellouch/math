import OAI.Analysis.MassAction.NetworkBarrier
import OAI.Analysis.MassAction.FixedMinimum

namespace OAI

noncomputable section

namespace Problem326.BarrierConstruction

/-- Convert the canonical finite-label uniform approximation statement to the
finite-index interface consumed by the network barrier construction. -/
theorem uniformAffineApproximation_of_finite_labels {d : ℕ}
    (hlabels : ∀ E : (Fin d → ℝ) → ℝ, (∀ r, 0 < E r) →
      ∃ Λ : Finset (Affine.Label d), Λ.Nonempty ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
        ∀ h : ℝ, 0 < h → h < h₀ → ∀ p : Fin d → ℝ,
          Affine.Cube (-1) 1 p → ∀ L : Affine.Label d,
            Affine.Active Λ L h (Affine.powerPoint h p) →
            ‖p - L.slope‖ < E L.slope) :
    UniformAffineApproximation d := by
  classical
  intro E hE
  obtain ⟨Λ, hΛ, h₀, hh₀, happrox⟩ := hlabels E hE
  let S := {L : Affine.Label d // L ∈ Λ}
  have hS : Nonempty S := by
    obtain ⟨L, hL⟩ := hΛ
    exact ⟨⟨L, hL⟩⟩
  let : Nonempty S := hS
  let e := Fintype.equivFin S
  let r : Fin (Fintype.card S) → Fin d → ℝ := fun j => (e.symm j).val.slope
  let c : Fin (Fintype.card S) → ℝ → ℝ := fun j => (e.symm j).val.offset
  refine ⟨Fintype.card S, Fintype.card_pos, r, c, h₀, hh₀, ?_⟩
  intro h hh hhsmall p hp j hj i
  have hcube : Affine.Cube (-1) 1 p := fun k => abs_le.mp (hp k)
  have ha : Affine.Active Λ (e.symm j).val h (Affine.powerPoint h p) := by
    refine ⟨(e.symm j).property, ?_⟩
    intro J hJ
    have hc := hj (e ⟨J, hJ⟩)
    simpa only [r, c, Affine.Label.value, Affine.powerPoint, dot,
      Equiv.symm_apply_apply] using hc
  have hn := happrox h hh hhsmall p hcube (e.symm j).val ha
  have hc := (pi_norm_lt_iff (hE (e.symm j).val.slope)).mp hn i
  simpa only [r, Pi.sub_apply, Real.norm_eq_abs] using hc

end Problem326.BarrierConstruction

end

end OAI
