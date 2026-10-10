import OAI.Geometry.EinsteinFour.ScalarAdjointCoordinates

namespace OAI

/-! Test pairing for the adjoint operator arising from the actual
density-weighted chart equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

def scalarSchwartzDirectOperator (a : Fin 4 → Fin 4 → S)
    (b : Fin 4 → S) (φ : S) : S :=
  scalarSchwartzHelmholtz φ +
    (∑ i, ∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (D i (D j φ))) +
    ∑ i, SchwartzMap.smulLeftCLM ℂ (b i) (D i φ)

theorem scalarFormalAdjointOperator_pairing (a : Fin 4 → Fin 4 → S)
    (b : Fin 4 → S) (u : T) (φ : S) :
    scalarFormalAdjointOperator a b u φ = u (scalarSchwartzDirectOperator a b φ) := by
  simp only [scalarFormalAdjointOperator, scalarSchwartzDirectOperator,
    add_apply, sub_apply, sum_apply, scalarSchwartzHelmholtz_transpose,
    map_add, map_sum]
  simp only [scalarCoordinateDerivative, scalarSchwartzCoordinateDerivative,
    lineDerivOp_apply_apply, map_neg, smulLeftCLM_apply_apply]
  rw [Finset.sum_neg_distrib]
  abel_nf

theorem scalarFormalAdjointOperator_remainder (a : Fin 4 → Fin 4 → S)
    (b : Fin 4 → S) (u : T) :
    scalarPerturbedOperator a (scalarAdjointDrift a b) u - u -
        M (-scalarAdjointPotential a b : S) u =
      scalarFormalAdjointOperator a b u - u := by
  have hn : M (-scalarAdjointPotential a b : S) u = -M (scalarAdjointPotential a b) u := by
    change M (-(scalarAdjointPotential a b : V → ℂ)) u = _
    rw [smulLeftCLM_neg (scalarAdjointPotential a b).hasTemperateGrowth, neg_apply]
  rw [scalarFormalAdjointOperator_expansion, hn]
  abel

end
end PositiveEinsteinFour.Geometry

end OAI
