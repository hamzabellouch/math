import OAI.Analysis.FourierLLogL.Weak.Endpoint
import OAI.Analysis.FourierLLogL.Assembly.Endpoint
import OAI.Analysis.FourierLLogL.Dyadic.Lift
import OAI.Analysis.FourierLLogL.Fourier.Good

/-!
# Almost everywhere Fourier convergence in L log L
-/

open MeasureTheory Filter Set
open scoped Topology

namespace OAI

namespace FourierLLogL

theorem main_of_grid (h : Dyadic.GridBound) {f : Torus → ℂ} (hf : MemLLogL f) :
    ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E,
      Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) :=
  h.unitTreeBound.affine.realGoodBound.goodBound.main_bound_consequence hf
end FourierLLogL

namespace FourierLLogL
/-- Almost everywhere convergence in L log L, all symmetric cutoffs. -/
theorem almost_everywhere_fourier_convergence (f : Torus → ℂ) (hf : MemLLogL f) :
    ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E,
      Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) :=
    main_of_grid Dyadic.gridProof hf

theorem maximal_good_sets : GoodBound :=
    Dyadic.gridProof.unitTreeBound.affine.realGoodBound.goodBound
end FourierLLogL

namespace FourierLLogL
/-- Cor. "Weak-L^1 maximal bound", in the equivalent all-levels form. -/
theorem weak_L1_maximal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Torus → ℂ), MemLLogL f →
      ∀ w : ℝ, 0 < w →
        w*circleMeasure.real (cloudSet f w) ≤ C*luxNorm f :=
    Weak.consequence_maximal maximal_good_sets
end FourierLLogL

end OAI
