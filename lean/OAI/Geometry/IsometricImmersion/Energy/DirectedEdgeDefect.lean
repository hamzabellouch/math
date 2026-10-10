import OAI.Geometry.IsometricImmersion.Energy.DirectedIntegralEstimate

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedQuadratic_edge_zero
    (A B C I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p) (hedge : p 1 = edge) :
    multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p = 0 := by
  have hW := directedWeight_edge_zero edge lambda I p hedge
  have hWd (i : Fin 2) := directedWeight_partial_edge_zero edge lambda hI hedge i
  have hm := directedM_differentiableAt edge lambda hI
  have hn := directedN_differentiableAt edge lambda epsilon hI
  obtain ⟨hm0, hn0⟩ := directed_mn_edge_zero edge lambda epsilon I p hedge
  have hmd (i : Fin 2) : coordPartial i (directedM edge lambda I) p = 0 := by
    rw [directedM_partial, hWd i, neg_zero]
  have hnd (i : Fin 2) : coordPartial i (directedN edge lambda epsilon I) p = 0 := by
    rw [directedN_partial edge lambda epsilon hI i, hW, hWd i]
    ring
  have hAm (i : Fin 2) : coordPartial i (fun q => A q * directedM edge lambda I q) p = 0 := by
    rw [HessianCalculus.coordPartial_mul_at hA hm i, hm0, hmd i]
    ring
  have hAn (i : Fin 2) : coordPartial i (fun q => A q * directedN edge lambda epsilon I q) p = 0 := by
    rw [HessianCalculus.coordPartial_mul_at hA hn i, hn0, hnd i]
    ring
  simp only [multiplierQuadratic, multiplierT, multiplierS, multiplierJ,
    hmd, hnd, hAm, hAn, hm0, hn0]
  ring

theorem directedCutoffError_edge_zero
    (A chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord) (hedge : p 1 = edge) :
    directedCutoffError A chi I u edge lambda epsilon p = 0 := by
  obtain ⟨ht, hs⟩ := directed_flux_edge_zero A u I edge lambda epsilon p hedge
  simp [directedCutoffError, multiplierCutoffError, ht, hs]

theorem directedCoercivityDefect_edge_zero
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p) (hedge : p 1 = edge) :
    directedCoercivityDefect A B C chi I u edge lambda epsilon c p = 0 := by
  rw [directedCoercivityDefect, directedWeight_edge_zero edge lambda I p hedge,
    directedQuadratic_edge_zero A B C I u edge lambda epsilon p hA hI hedge]
  simp

end SmoothLocal.Weighted

end

end OAI
