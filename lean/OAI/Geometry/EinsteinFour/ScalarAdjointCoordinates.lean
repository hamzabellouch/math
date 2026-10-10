import OAI.Geometry.EinsteinFour.ScalarPoissonKernelBootstrap

namespace OAI

/-! The density-weighted chart equation gives the formal adjoint of the
nondivergence operator. Its expansion has the same principal coefficients,
a differentiated drift, and an explicit smooth zeroth-order potential. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

def scalarFormalAdjointOperator (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (u : T) : T :=
  normalizedScalarHelmholtz u +
    (∑ i, ∑ j, scalarCoordinateDerivative j (scalarCoordinateDerivative i (M (a i j) u))) -
    ∑ i, scalarCoordinateDerivative i (M (b i) u)

def scalarAdjointDrift (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (j : Fin 4) : S :=
  (∑ i, D i (a i j)) + (∑ i, D i (a j i)) - b j

def scalarAdjointPotential (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) : S :=
  (∑ i, ∑ j, D j (D i (a i j))) - ∑ i, D i (b i)

private theorem scalar_adjoint_multiplier_sum (a : Fin 4 → S) (u : T) :
    M (∑ i, a i : S) u = ∑ i, M (a i) u := by
  have he : ((∑ i, a i : S) : V → ℂ) = fun x => ∑ i, a i x := by
    funext x
    simp only [sum_apply]
  rw [he]
  have hs := congrArg (fun A : T →L[ℂ] T => A u)
    (smulLeftCLM_sum (F := ℂ) (s := Finset.univ) (fun i _ => (a i).hasTemperateGrowth))
  simpa only [sum_apply] using hs

private theorem scalar_adjoint_multiplier_add (a b : S) (u : T) :
    M (a + b : S) u = M a u + M b u := by
  change M ((a : V → ℂ) + (b : V → ℂ)) u = _
  rw [smulLeftCLM_add a.hasTemperateGrowth b.hasTemperateGrowth, add_apply]

private theorem scalar_adjoint_multiplier_sub (a b : S) (u : T) :
    M (a - b : S) u = M a u - M b u := by
  change M ((a : V → ℂ) - (b : V → ℂ)) u = _
  rw [smulLeftCLM_sub a.hasTemperateGrowth b.hasTemperateGrowth, sub_apply]

theorem scalarAdjoint_second_product (a : S) (u : T) (i j : Fin 4) :
    scalarCoordinateDerivative j (scalarCoordinateDerivative i (M a u)) =
      M a (scalarCoordinateDerivative i (scalarCoordinateDerivative j u)) +
        M (D i a) (scalarCoordinateDerivative j u) +
        M (D j a) (scalarCoordinateDerivative i u) + M (D j (D i a)) u := by
  rw [scalarCoordinateDerivative_multiplier]
  change LineDeriv.lineDerivOpCLM ℂ T (EuclideanSpace.basisFun (Fin 4) ℝ j) (_ + _) = _
  rw [map_add]
  change scalarCoordinateDerivative j (M (D i a) u) +
    scalarCoordinateDerivative j (M a (scalarCoordinateDerivative i u)) = _
  rw [scalarCoordinateDerivative_multiplier, scalarCoordinateDerivative_multiplier,
    scalarCoordinateDerivative_commute j i]
  change M (D j (D i a)) u + M (D i a) (scalarCoordinateDerivative j u) +
    (M (D j a) (scalarCoordinateDerivative i u) +
      M a (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) = _
  abel

theorem scalarFormalAdjointOperator_expansion (a : Fin 4 → Fin 4 → S)
    (b : Fin 4 → S) (u : T) :
    scalarFormalAdjointOperator a b u =
      scalarPerturbedOperator a (scalarAdjointDrift a b) u +
        M (scalarAdjointPotential a b) u := by
  have hfirst : (∑ i, ∑ j, M (D i (a i j)) (scalarCoordinateDerivative j u)) =
      ∑ j, ∑ i, M (D i (a i j)) (scalarCoordinateDerivative j u) := Finset.sum_comm
  have hsecond : (∑ i, ∑ j, M (D j (a i j)) (scalarCoordinateDerivative i u)) =
      ∑ j, ∑ i, M (D i (a j i)) (scalarCoordinateDerivative j u) := by
    rfl
  unfold scalarFormalAdjointOperator
  simp_rw [scalarAdjoint_second_product]
  simp only [scalarCoordinateDerivative_multiplier, scalarPerturbedOperator,
    scalarAdjointDrift, scalarAdjointPotential, scalar_adjoint_multiplier_add,
    scalar_adjoint_multiplier_sub, scalar_adjoint_multiplier_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hfirst, hsecond]
  simp only [scalarSchwartzCoordinateDerivative]
  abel

private theorem scalar_adjoint_nine_bound (p q : Fin 4 → ℂ) (b : ℂ) (δ : ℝ)
    (hp : ∀ i, ‖p i‖ ≤ δ) (hq : ∀ i, ‖q i‖ ≤ δ) (hb : ‖b‖ ≤ δ) :
    ‖(∑ i, p i) + (∑ i, q i) - b‖ ≤ 9 * δ := by
  have hp' : ‖∑ i, p i‖ ≤ 4 * δ := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ i : Fin 4, ‖p i‖) ≤ ∑ _i : Fin 4, δ := Finset.sum_le_sum (fun i _ => hp i)
      _ = 4 * δ := by simp
  have hq' : ‖∑ i, q i‖ ≤ 4 * δ := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ i : Fin 4, ‖q i‖) ≤ ∑ _i : Fin 4, δ := Finset.sum_le_sum (fun i _ => hq i)
      _ = 4 * δ := by simp
  calc
    _ ≤ ‖∑ i, p i‖ + ‖∑ i, q i‖ + ‖b‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 4 * δ + 4 * δ + δ := add_le_add (add_le_add hp' hq') hb
    _ = 9 * δ := by ring

theorem scalarAdjointDrift_bound (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (ha : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ) (j : Fin 4) (x : V) :
    ‖scalarAdjointDrift a b j x‖ ≤ 9 * δ := by
  simp only [scalarAdjointDrift, sub_apply, add_apply, sum_apply]
  exact scalar_adjoint_nine_bound _ _ _ δ (fun i => ha i j i x)
    (fun i => ha j i i x) (hb j x)

theorem scalarAdjointDrift_derivative_bound (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (ha : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i k x, ‖D k (b i) x‖ ≤ δ) (j k : Fin 4) (x : V) :
    ‖D k (scalarAdjointDrift a b j) x‖ ≤ 9 * δ := by
  have hD : D k (scalarAdjointDrift a b j) =
      (∑ i, D k (D i (a i j))) + (∑ i, D k (D i (a j i))) - D k (b j) := by
    change (LineDeriv.lineDerivOpCLM ℂ S (EuclideanSpace.basisFun (Fin 4) ℝ k))
      ((∑ i, D i (a i j)) + (∑ i, D i (a j i)) - b j) = _
    rw [map_sub, map_add, map_sum, map_sum]
    rfl
  rw [hD]
  simp only [sub_apply, add_apply, sum_apply]
  exact scalar_adjoint_nine_bound _ _ _ δ (fun i => ha i j k i x)
    (fun i => ha j i k i x) (hb j k x)

end
end PositiveEinsteinFour.Geometry

end OAI
