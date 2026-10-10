import OAI.Analysis.KadisonKastler.RescaledTomitaGraph
import OAI.Analysis.KadisonKastler.ResolventCutBound

namespace OAI

/-! # Contractive compression of the actual graph projection

The first diagonal entry is the bounded graph resolvent. Its comparison
follows directly from the norm comparison of the whole graph projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_graph_operatorEntry_le
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (i j : Fin 2) :
    ‖Generator.operatorEntry T i j‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖T (Generator.tupleSingle j x) i‖ ≤ ‖T‖ * ‖x‖
  have hs : ‖Generator.tupleSingle (H := H) j x‖ = ‖x‖ :=
    PiLp.norm_single 2 (fun _ : Fin 2 => H) j x
  exact (PiLp.norm_apply_le _ _).trans ((T.le_opNorm _).trans_eq (by rw [hs]))

def graphResolvent (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : H →L[ℂ] H :=
  Generator.operatorEntry (rescaledGraphProjection P J Ω c) 0 0

theorem norm_graphResolvent_sub_le
    (P Q : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    ‖graphResolvent P J Ω c - graphResolvent Q J Ω c‖ ≤
      ‖rescaledGraphProjection P J Ω c - rescaledGraphProjection Q J Ω c‖ := by
  have he : graphResolvent P J Ω c - graphResolvent Q J Ω c =
      Generator.operatorEntry
        (rescaledGraphProjection P J Ω c - rescaledGraphProjection Q J Ω c) 0 0 := by
    ext x
    rfl
  rw [he]
  exact norm_graph_operatorEntry_le _ _ _

/-- Once the spectral theorem gives the cut-restricted inverse, the
separated-cut bound uses only the proved graph comparison. -/
theorem norm_cut_product_of_graph_bound
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (P Q R : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hgraph : ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ e)
    (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ 1 + Real.exp (-(1 / 2 : ℝ)))
    (hQB : ‖Q * graphResolvent N J Ω c‖ ≤
      Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ))))
    (hAR : graphResolvent M J Ω c * R = P)
    (hPR : P * R = R)
    (hQBQ : Q * graphResolvent N J Ω c * Q = Q * graphResolvent N J Ω c) :
    ‖Q * P‖ ≤ ((1 + Real.exp (-(1 / 2 : ℝ))) /
      (1 - Real.exp (-(1 / 2 : ℝ)))) * e :=
  norm_logarithmically_separated_cuts_le _ _ _ _ _ he hQ hR hQB
    ((norm_graphResolvent_sub_le M N J Ω c).trans hgraph) hAR hPR hQBQ

end

end KadisonKastler

end OAI
