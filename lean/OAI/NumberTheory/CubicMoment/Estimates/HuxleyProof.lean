import OAI.NumberTheory.CubicMoment.Estimates.HuxleyResiduePoints

namespace OAI

/-! The exact published additive large-sieve input, proved from Gaussian packing. -/
noncomputable section
namespace CubicFirstMoment

theorem huxleyAdditiveLargeSieve_proved : HuxleyAdditiveLargeSieve := by
  refine ⟨huxleyAdditiveConstant,huxleyAdditiveConstant_pos,?_⟩
  intro Q Z hQ hZ v
  rw [huxleySieveMass_eq_points]
  exact huxley_finite_primal_bound Q Z (by linarith) (by linarith)
    (huxleyResiduePointSet Q) (huxleyResiduePointSet_reduced Q)
    (huxleyResiduePointSet_shift Q) (nonzeroNormBall Z)
    (fun n hn => (mem_nonzeroNormBall.mp hn).1) v

end CubicFirstMoment

end

end OAI
