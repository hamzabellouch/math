import OAI.Geometry.EinsteinFour.ScalarPoissonKernelMultiplier

namespace OAI

/-! Exact localization of the distributional Laplacian, and the loss of
only one Sobolev order in its smooth-cutoff commutator. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

def scalarSchwartzCoordinateDerivative (i : Fin 4) (a : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a

private theorem scalar_schwartz_sum_multiplier (a : Fin 4 → 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) :
    smulLeftCLM ℂ (∑ i, a i : 𝓢(V, ℂ)) u = ∑ i, smulLeftCLM ℂ (a i) u := by
  have hf : ((∑ i, a i : 𝓢(V, ℂ)) : V → ℂ) = fun x => ∑ i, a i x := by
    funext x
    simp only [sum_apply]
  rw [hf]
  have h := congrArg (fun A : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) => A u)
    (smulLeftCLM_sum (F := ℂ) (s := Finset.univ) (fun i _ => (a i).hasTemperateGrowth))
  simpa only [sum_apply] using h

private theorem scalar_secondDerivative_multiplier (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (i : Fin 4) :
    scalarCoordinateDerivative i (scalarCoordinateDerivative i (smulLeftCLM ℂ a u)) =
      smulLeftCLM ℂ a (scalarCoordinateDerivative i (scalarCoordinateDerivative i u)) +
      (2 : ℂ) • smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarCoordinateDerivative i u) +
      smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i
        (scalarSchwartzCoordinateDerivative i a)) u := by
  rw [scalarCoordinateDerivative_multiplier]
  change ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i}
    (smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) u +
      smulLeftCLM ℂ a (scalarCoordinateDerivative i u)) = _
  rw [LineDeriv.lineDerivOp_add]
  change scalarCoordinateDerivative i (smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) u) +
    scalarCoordinateDerivative i (smulLeftCLM ℂ a (scalarCoordinateDerivative i u)) = _
  rw [scalarCoordinateDerivative_multiplier, scalarCoordinateDerivative_multiplier]
  change smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i
      (scalarSchwartzCoordinateDerivative i a)) u +
      smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) (scalarCoordinateDerivative i u) +
    (smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) (scalarCoordinateDerivative i u) +
      smulLeftCLM ℂ a (scalarCoordinateDerivative i (scalarCoordinateDerivative i u))) = _
  module

/-- The actual distributional Laplacian product rule. -/
theorem scalar_laplacian_multiplier (a : 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) :
    Δ (smulLeftCLM ℂ a u) = smulLeftCLM ℂ a (Δ u) +
      (2 : ℂ) • (∑ i : Fin 4, smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarCoordinateDerivative i u)) + smulLeftCLM ℂ (Δ a : 𝓢(V, ℂ)) u := by
  have hu : (∑ i : Fin 4, smulLeftCLM ℂ a
      (scalarCoordinateDerivative i (scalarCoordinateDerivative i u))) =
        smulLeftCLM ℂ a (Δ u) := by
    rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ), map_sum]
    rfl
  have ha : (∑ i : Fin 4, smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i
      (scalarSchwartzCoordinateDerivative i a)) u) = smulLeftCLM ℂ (Δ a : 𝓢(V, ℂ)) u := by
    rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ),
      scalar_schwartz_sum_multiplier]
    rfl
  rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ)]
  change (∑ i : Fin 4, scalarCoordinateDerivative i
    (scalarCoordinateDerivative i (smulLeftCLM ℂ a u))) = _
  simp_rw [scalar_secondDerivative_multiplier]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hu, ha]

/-- The part created by commuting a smooth cutoff with the Laplacian. -/
def scalarLaplacianCommutator (a : 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) : 𝓢'(V, ℂ) :=
  Δ (smulLeftCLM ℂ a u) - smulLeftCLM ℂ a (Δ u)

theorem scalarLaplacianCommutator_eq (a : 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) :
    scalarLaplacianCommutator a u =
      (2 : ℂ) • (∑ i : Fin 4, smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarCoordinateDerivative i u)) + smulLeftCLM ℂ (Δ a : 𝓢(V, ℂ)) u := by
  rw [scalarLaplacianCommutator, scalar_laplacian_multiplier]
  abel

/-- A cutoff commutator loses only one derivative, including the H1-to-L2 case. -/
theorem scalarLaplacianCommutator_memSobolev (n : ℕ) (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 u) :
    MemSobolev (n : ℝ) 2 (scalarLaplacianCommutator a u) := by
  have hu' : MemSobolev (n : ℝ) 2 u ∧
      ∀ i : Fin 4, MemSobolev (n : ℝ) 2 (scalarCoordinateDerivative i u) := by
    apply (scalar_memSobolev_succ_iff (n : ℝ) u).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hu
  have hsum (S : Finset (Fin 4)) : MemSobolev (n : ℝ) 2
      (∑ i ∈ S, smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarCoordinateDerivative i u)) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero V ℂ (n : ℝ) 2
    | @insert i S hi ih =>
        rw [Finset.sum_insert hi]
        exact (scalar_memSobolev_schwartz_multiplier n
          (scalarSchwartzCoordinateDerivative i a) _ (hu'.2 i)).add ih
  rw [scalarLaplacianCommutator_eq]
  exact (hsum Finset.univ).smul _ |>.add
    (scalar_memSobolev_schwartz_multiplier n (Δ a : 𝓢(V, ℂ)) u hu'.1)

/-- Localizing the equation preserves the lower Sobolev order of its RHS. -/
theorem scalar_cutoff_laplacian_memSobolev (n : ℕ) (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 u)
    (hΔ : MemSobolev (n : ℝ) 2 (Δ u)) :
    MemSobolev (n : ℝ) 2 (Δ (smulLeftCLM ℂ a u)) := by
  have heq : Δ (smulLeftCLM ℂ a u) =
      smulLeftCLM ℂ a (Δ u) + scalarLaplacianCommutator a u := by
    rw [scalarLaplacianCommutator]
    abel
  rw [heq]
  exact (scalar_memSobolev_schwartz_multiplier n a (Δ u) hΔ).add
    (scalarLaplacianCommutator_memSobolev n a u hu)

end
end PositiveEinsteinFour.Geometry

end OAI
