import OAI.Probability.InvariantIsing.Haar.HaarCompactness

namespace OAI

/-! The actual matrix-group topology and positivity of finite Haar measure. -/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

instance specialOrthogonal_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialOrthogonal N) where
  continuous_mul := continuous_mul
  continuous_inv := by
    apply Continuous.subtype_mk
    change Continuous (fun U : SpecialOrthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ).transpose)
    fun_prop

end InvariantIsing

end

end OAI
