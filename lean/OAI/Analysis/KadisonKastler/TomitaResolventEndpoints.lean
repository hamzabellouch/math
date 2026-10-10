import OAI.Analysis.KadisonKastler.TomitaResolventFaithful

namespace OAI

/-! # Absence of endpoint eigenvectors for the Tomita resolvent -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem one_sub_graphResolvent_eq_zero_iff (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) (x : H) :
    (1 - graphResolvent M J Ω 1) x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    let P := rescaledGraphSubspace M J Ω 1
    let v := P.starProjection (Generator.tupleSingle 0 x)
    have hfirst : v 0 = x := by
      change x - v 0 = 0 at hx
      exact (sub_eq_zero.mp hx).symm
    have hn := P.norm_starProjection_apply_le (Generator.tupleSingle 0 x)
    have hs : ‖Generator.tupleSingle (H := H) (0 : Fin 2) x‖ = ‖x‖ :=
      PiLp.norm_single 2 (fun _ : Fin 2 => H) 0 x
    rw [hs] at hn
    change ‖v‖ ≤ ‖x‖ at hn
    have hsq : ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Fin.sum_univ_two]
    have hsecond : v 1 = 0 := by
      apply norm_eq_zero.mp
      rw [hfirst] at hsq
      have hn0 := norm_nonneg v
      have hn1 := norm_nonneg (v 1)
      nlinarith [sq_nonneg (‖v 1‖)]
    have hv := rescaledGraph_no_horizontal J Ω hsep v
      (P.starProjection_apply_mem _) hsecond
    have hf := congrArg (fun w : TomitaGraphHilbert H => w 0) hv
    exact hfirst.symm.trans hf
  · rintro rfl
    exact map_zero _

end

end KadisonKastler

end OAI
