import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingExistence
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace OAI

/-! Normalization at infinity makes the two outgoing columns linearly independent. -/

open Filter
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circular_columns_coefficient_unique (Yp Ym : ℝ → E₄)
    (hp : Tendsto Yp atTop (nhds ((1,0),(0,0))))
    (hm : Tendsto Ym atTop (nhds ((0,0),(1,0)))) (a b : ℂ)
    (h : ∀ t, 0 ≤ t → a • Yp t+b • Ym t=0) : a=0 ∧ b=0 := by
  have hl := (hp.const_smul a).add (hm.const_smul b)
  have hz : Tendsto (fun t => a • Yp t+b • Ym t) atTop (nhds (0 : E₄)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (h t ht).symm
  have he := tendsto_nhds_unique hl hz
  constructor
  · simpa using congrArg (fun z : E₄ => z.1.1) he
  · simpa using congrArg (fun z : E₄ => z.2.1) he

theorem circular_columns_linearIndependent (Yp Ym : ℝ → E₄)
    (hp : Tendsto Yp atTop (nhds ((1,0),(0,0))))
    (hm : Tendsto Ym atTop (nhds ((0,0),(1,0)))) :
    LinearIndependent ℂ ![Yp,Ym] := by
  rw [linearIndependent_fin2]
  constructor
  · change Ym ≠ 0
    intro hzero
    have he := circular_columns_coefficient_unique Yp Ym hp hm 0 1 (by
      intro t _
      simp [hzero])
    exact one_ne_zero he.2
  · intro a ha
    change a • Ym=Yp at ha
    have he := circular_columns_coefficient_unique Yp Ym hp hm (-1) a (by
      intro t _
      rw [← congrFun ha t]
      simp)
    exact (neg_ne_zero.mpr one_ne_zero) he.1

end DefocusingNLS

end OAI
