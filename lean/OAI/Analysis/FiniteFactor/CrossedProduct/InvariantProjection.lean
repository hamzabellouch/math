import OAI.Analysis.FiniteFactor.CrossedProduct.EventPositive
import OAI.Analysis.FiniteFactor.CrossedProduct.EventMassUpper

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The source probability contradiction for the original operator and
original algebra. All event, convolution and error estimates are proved
from this p's actual projection and invariance identities. -/
theorem sourceInvariantProjection_trivial
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    (hs : SourceOrderedTorusSampling θ) (hphase : ∃ J, SourceSecondPhasesFrom θ J)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    p = 0 ∨ p = 1 := by
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  by_cases hp1 : p = 1
  · exact Or.inr hp1
  exfalso
  have hlow := sourceProjectionEvent_eventually_positive θ hθ hr hp hproj hp0 hp1 hinv
  obtain ⟨J,hJ⟩ := hphase
  have hbound : ∀ᶠ j : ℕ in atTop, Real.exp (-82)/2 ≤ 1/((j : ℝ)+1) := by
    filter_upwards [hlow,eventually_ge_atTop J] with j hj hJj
    have hphasej : SourceSecondPhasesFrom θ j := fun s hjs => hJ s (hJj.trans hjs)
    exact hj.trans (sourceProjectionEvent_mass_upper θ hθ hs hp hproj hinv j hphasej)
  have hzero : Real.exp (-82)/2 ≤ 0 :=
    ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hbound
  exact (not_le_of_gt (half_pos (Real.exp_pos (-82)))) hzero

end
end FiniteFactor

end OAI
