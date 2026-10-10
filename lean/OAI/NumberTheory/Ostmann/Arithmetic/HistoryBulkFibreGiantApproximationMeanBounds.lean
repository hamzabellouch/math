import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction

theorem cmean_error_of_fixed_factor {α : Type*} [Fintype α]
    (μ : FinitePrior α) (factor : ℂ) (source principal : α→ℂ) (error : ℝ)
    (h : ∀u,μ.mass u≠0 → ‖source u-factor*principal u‖≤error) :
    ‖μ.cmean source-factor*μ.cmean principal‖≤error := by
  rw [←FinitePrior.cmean_mul_left,GiantCollisionError.cmean_sub_eq]
  exact GiantCollisionError.norm_cmean_le_of_mass_ne_zero μ _ error h

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
