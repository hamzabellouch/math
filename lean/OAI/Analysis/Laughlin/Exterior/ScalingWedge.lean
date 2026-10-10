import OAI.Analysis.Laughlin.Exterior.FourConjugation
import OAI.Analysis.Laughlin.Pair.FactorLimit

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem orbitalScaling_mode (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    orbitalScaling Q d (mode i) = d i • mode i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [orbitalScaling,mode]
  · simp [orbitalScaling,mode,h]

theorem exteriorScaling_wedge (Q n : ℕ) (d : Fin (Q+1) → ℂ) (w : Fin n → Fin (Q+1)) :
    exteriorScaling Q d (ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a))) =
      (∏ a, d (w a)) • ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a)) := by
  unfold exteriorScaling
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ n (fun a => orbitalScaling Q d (mode (w a))) = _
  simp_rw [orbitalScaling_mode]
  exact (ExteriorAlgebra.ιMulti ℂ n).map_smul_univ (fun a => d (w a)) (fun a => mode (w a))

theorem local_diagonal_tendsto (L n : ℕ) (w : Fin n → Fin (L+1)) :
    Tendsto (fun Q : ℕ => ∏ a, modeFactor Q (w a).val) atTop (𝓝 1) := by
  have h : Tendsto (fun Q : ℕ => ∏ a : Fin n, modeFactor Q (w a).val) atTop
      (𝓝 (∏ _a : Fin n, (1 : ℝ))) := by
    apply tendsto_finsetProd
    intro a ha
    exact modeFactor_tendsto (w a).val
  simpa using h

theorem local_diagonal_inverse_tendsto (L n : ℕ) (w : Fin n → Fin (L+1)) :
    Tendsto (fun Q : ℕ => (∏ a, modeFactor Q (w a).val)⁻¹) atTop (𝓝 1) := by
  simpa using (local_diagonal_tendsto L n w).inv₀ (by norm_num)

end Laughlin.Fock

end OAI
