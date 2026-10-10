import OAI.Geometry.EinsteinFour.HessianCompression
import OAI.Geometry.EinsteinFour.ParameterCost
import OAI.Geometry.EinsteinFour.TraceSubtraction
import OAI.Geometry.EinsteinFour.HessianTraceEquation
import OAI.Geometry.EinsteinFour.TraceGreen

namespace OAI

/-! Assembly of the actual weighted Hessian square and its Green contributions. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Polarization is applied before any symmetry is imposed on the weight tensor. -/
def weightedQuadratic (q : Hessian → ℝ) (m : ℝ) (X L : Hessian) : ℝ :=
  (m * q X + (q (X + L) - q X - q L) / 2) / 6

def plusDerivativeQuadratic (t : Fin 3 → ℝ) (X : Hessian) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, t s * derivativeSlotForm s X

def matrixSlotQuadratic (t : Fin 3 → ℝ) (X : Hessian) : ℝ :=
  ∑ s, t s * matrixSlotForm s X

def traceCorrection (t u : Fin 3 → ℝ) (M : Mat) (m : ℝ) (L : Hessian) : ℝ :=
  -(m * curvaturePairing t u (traceComponent M) (traceComponent M) +
    curvaturePairing t u (traceComponent M) L) / 6

theorem weightedQuadratic_identity (m : ℝ) (X L : Hessian) :
    weightedQuadratic hessianNormSq m X L =
      (m * hessianNormSq X + hessianPairing X L) / 6 := by
  have hn : hessianNormSq (X + L) = hessianNormSq X + hessianNormSq L +
      2 * hessianPairing X L := by
    change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b + L i j a b) ^ 2) = _
    have hp (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
    simp only [hp, hessianNormSq, hessianPairing, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  unfold weightedQuadratic
  rw [hn]
  ring

/-- The coefficients of the four Green calculations are those of the
original curvature operator, on the whole inner-Bianchi tensor space. -/
theorem weightedQuadratic_original (t u : Fin 3 → ℝ) (m : ℝ) (X L : Hessian) :
    weightedQuadratic (originalCurvatureForm t u) m X L =
      4 * weightedQuadratic hessianNormSq m X L -
        (5 / 6 : ℝ) * weightedQuadratic (plusDerivativeQuadratic t) m X L -
        (5 / 3 : ℝ) * weightedQuadratic (matrixSlotQuadratic t) m X L -
        weightedQuadratic (minusDerivativeCurvatureForm u) m X L := by
  unfold weightedQuadratic originalCurvatureForm originalPlusCurvatureForm
    plusDerivativeQuadratic matrixSlotQuadratic
  ring

/-- The local square, rewritten in the original four curvature terms and
with the entire prescribed trace subtracted. -/
theorem local_weighted_original_square (X : Hessian) (M : Mat)
    (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0)
    (hM : symmetric M) (hMt : traceFree M)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M)
    (hY : condition (X - traceComponent M))
    (a : Vec) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi)
    (x y m : ℝ) (hm : 0 < m)
    (htx : ∀ s, -x ≤ t s) (huy : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ 4 * weightedQuadratic hessianNormSq m X (weightTensor a Z) -
        (5 / 6 : ℝ) * weightedQuadratic (plusDerivativeQuadratic t) m X (weightTensor a Z) -
        (5 / 3 : ℝ) * weightedQuadratic (matrixSlotQuadratic t) m X (weightTensor a Z) -
        weightedQuadratic (minusDerivativeCurvatureForm u) m X (weightTensor a Z) +
        traceCorrection t u M m (weightTensor a Z) +
        curvaturePairing t u (highestProjection (weightTensor a Z))
          (highestProjection (weightTensor a Z)) / (24 * m) := by
  have hL := weightTensor_matrix_bianchi a Z hz hb
  have hsquare := weighted_highestProjection_square (X - traceComponent M) (weightTensor a Z)
    hY t u x y m hm htx huy hxy
  have hsub := weighted_trace_subtraction t u ht M hM hMt X (weightTensor a Z)
    hmatrix hbianchi htrace m
  have hXX : curvaturePairing t u X X = originalCurvatureForm t u X := by
    rw [curvaturePairing_self,
      originalCurvatureForm_eq_of_inner_bianchi X hmatrix hbianchi t u ht hu]
  have hXL : curvaturePairing t u X (weightTensor a Z) =
      originalPolarPairing t u X (weightTensor a Z) :=
    (originalPolarPairing_eq_of_inner_bianchi X (weightTensor a Z)
      hmatrix hbianchi hL.1 hL.2 t u ht hu).symm
  rw [← weightedQuadratic_original]
  have heq : weightedQuadratic (originalCurvatureForm t u) m X (weightTensor a Z) +
      traceCorrection t u M m (weightTensor a Z) =
        (m / 6) * curvaturePairing t u (X - traceComponent M) (X - traceComponent M) +
          curvaturePairing t u (X - traceComponent M) (weightTensor a Z) / 6 := by
    change (m * originalCurvatureForm t u X +
      originalPolarPairing t u X (weightTensor a Z)) / 6 + _ = _
    rw [← hXX, ← hXL]
    unfold traceCorrection
    linear_combination (-1 / 6 : ℝ) * hsub
  rw [heq]
  exact hsquare

/-- Substitute the actual real-vector projection cost for the squared
weight used in the coupling argument. -/
theorem local_squared_weight_original (S : Shape) (v : ℝ) (hv : 0 ≤ v)
    (X : Hessian) (M : Mat) (u : Fin 3 → ℝ) (hu : ∑ s, u s = 0)
    (hM : symmetric M) (hMt : traceFree M)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M)
    (hY : condition (X - traceComponent M))
    (x y w : ℝ) (hw : w ≠ 0) (hy : 0 ≤ y)
    (htx : ∀ s, -x ≤ v * S.s s) (huy : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2)
    (p q k l : Vec) :
    0 ≤ weightedQuadratic (originalCurvatureForm (fun s => v * S.s s) u)
        (w ^ 2) X (weightTensor ((-(3 / 4 : ℝ) * w) • (p - q)) (parameters S p k l)) +
      traceCorrection (fun s => v * S.s s) u M (w ^ 2)
        (weightTensor ((-(3 / 4 : ℝ) * w) • (p - q)) (parameters S p k l)) +
      (9 / 64 : ℝ) * ‖p - q‖ ^ 2 *
        (QuarticEnergy.projectionCoefficient v y S.sigma S.rho * ((5 / 3) * ‖p‖ ^ 2) +
          Energy.defectCoefficient v y * ((parameters S p k l).squaredNorm / 6 -
            (5 / 3) * ‖p‖ ^ 2)) := by
  have ht : ∑ s, v * S.s s = 0 := by rw [← Finset.mul_sum, S.trace, mul_zero]
  have hlocal := local_weighted_original_square X M (fun s => v * S.s s) u ht hu
    hM hMt hmatrix hbianchi htrace hY ((-(3 / 4 : ℝ) * w) • (p - q))
    (parameters S p k l) (parameters_traceFree S p k l) (parameters_bianchi S p k l)
    x y (w ^ 2) (sq_pos_of_ne_zero hw) htx huy hxy
  rw [← weightedQuadratic_original] at hlocal
  have hcost := squared_weight_parameter_cost S v hv u hu x y w hw htx huy hy hxy p q k l
  exact hlocal.trans (add_le_add_right hcost _)

/-- The first-derivative form obtained after all four Green calculations. -/
def collectedHessianForm (v b e B C E p2 : ℝ) : ℝ :=
  (-42 - 3 * b ^ 2 - (10 / 3) * v ^ 2) * e +
    75 * B + (25 / 3) * C - (100 / 3) * E + 5 * v ^ 2 * p2

/-- Collect the identity, plus, matrix-slot, minus, and trace contributions.
The nonparallel cubic term retains its exact coefficient. -/
theorem green_contributions_collect (m v b e B C E p2 cubic : ℝ) :
    4 * (m * (-13 * e + 20 * B)) -
        (5 / 6 : ℝ) * (m * (7 * v ^ 2 * e - 4 * B - 4 * C)) -
        (5 / 3 : ℝ) * (m * (-10 * B - 3 * C + 20 * E) + cubic / 12) -
        m * (3 * b ^ 2 * e) +
        m * ((10 + (5 / 2) * v ^ 2) * e - 25 * B + 5 * v ^ 2 * p2) =
      m * collectedHessianForm v b e B C E p2 - (5 / 36 : ℝ) * cubic := by
  unfold collectedHessianForm
  ring

theorem collectedHessianForm_eq_tensor (S : Shape) (v b : ℝ) (p k l : Vec) :
    collectedHessianForm v b ((parameters S p k l).squaredNorm / 6)
      (curvatureContraction S v (parameters S p k l))
      (squareCurvatureContraction S v (parameters S p k l))
      ((curvatureAction S v p k l).squaredNorm / 6) (‖p‖ ^ 2) =
        hessianTensorForm S v b p k l := rfl

section Integral

open MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

local instance : NormedAddCommGroup C(Ω, ℝ) := ContinuousMap.instNormedAddCommGroup
local instance : NormedSpace ℝ C(Ω, ℝ) := ContinuousMap.normedSpace

private def assemblyIntegral : C(Ω, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (μ := μ)).comp (ContinuousMap.toLp 1 μ ℝ)

private theorem assemblyIntegral_apply (f : C(Ω, ℝ)) :
    assemblyIntegral μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f)

private theorem integral_green_combination (I T B U D C : C(Ω, ℝ)) :
    (∫ x, 4 * I x - (5 / 6 : ℝ) * T x - (5 / 3 : ℝ) * B x - U x + D x + C x ∂μ) =
      4 * (∫ x, I x ∂μ) - (5 / 6 : ℝ) * (∫ x, T x ∂μ) -
        (5 / 3 : ℝ) * (∫ x, B x ∂μ) - (∫ x, U x ∂μ) +
          (∫ x, D x ∂μ) + (∫ x, C x ∂μ) := by
  change (∫ x, (((4 : ℝ) • I - (5 / 6 : ℝ) • T - (5 / 3 : ℝ) • B - U + D + C) x) ∂μ) = _
  rw [← assemblyIntegral_apply]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, assemblyIntegral_apply]

/-- Assemble the independently derived four Green identities and the full
trace identity. This is an integration lemma, not an additional geometric
or published-input assumption. -/
theorem weighted_hessian_inequality_of_green_identities
    (I T F U D cost m v b e B C E p2 cubic : C(Ω, ℝ))
    (hlocal : ∀ x, 0 ≤ 4 * I x - (5 / 6 : ℝ) * T x - (5 / 3 : ℝ) * F x -
      U x + D x + cost x)
    (hI : (∫ x, I x ∂μ) = ∫ x, m x * (-13 * e x + 20 * B x) ∂μ)
    (hT : (∫ x, T x ∂μ) = ∫ x, m x * (7 * v x ^ 2 * e x - 4 * B x - 4 * C x) ∂μ)
    (hF : (∫ x, F x ∂μ) = ∫ x, m x * (-10 * B x - 3 * C x + 20 * E x) + cubic x / 12 ∂μ)
    (hU : (∫ x, U x ∂μ) = ∫ x, m x * (3 * b x ^ 2 * e x) ∂μ)
    (hD : (∫ x, D x ∂μ) = ∫ x, m x * ((10 + (5 / 2 : ℝ) * v x ^ 2) * e x -
      25 * B x + 5 * v x ^ 2 * p2 x) ∂μ) :
    0 ≤ ∫ x, m x * collectedHessianForm (v x) (b x) (e x) (B x) (C x) (E x) (p2 x) -
      (5 / 36 : ℝ) * cubic x + cost x ∂μ := by
  let RI : C(Ω, ℝ) := ⟨fun x => m x * (-13 * e x + 20 * B x), by fun_prop⟩
  let RT : C(Ω, ℝ) := ⟨fun x => m x * (7 * v x ^ 2 * e x - 4 * B x - 4 * C x), by fun_prop⟩
  let RF : C(Ω, ℝ) := ⟨fun x => m x * (-10 * B x - 3 * C x + 20 * E x) + cubic x / 12,
    by fun_prop⟩
  let RU : C(Ω, ℝ) := ⟨fun x => m x * (3 * b x ^ 2 * e x), by fun_prop⟩
  let RD : C(Ω, ℝ) := ⟨fun x => m x * ((10 + (5 / 2 : ℝ) * v x ^ 2) * e x -
    25 * B x + 5 * v x ^ 2 * p2 x), by fun_prop⟩
  have hsum : (∫ x, 4 * I x - (5 / 6 : ℝ) * T x - (5 / 3 : ℝ) * F x -
      U x + D x + cost x ∂μ) =
      ∫ x, 4 * RI x - (5 / 6 : ℝ) * RT x - (5 / 3 : ℝ) * RF x -
        RU x + RD x + cost x ∂μ := by
    rw [integral_green_combination, integral_green_combination, hI, hT, hF, hU, hD]
    rfl
  have hpoint (x : Ω) : 4 * RI x - (5 / 6 : ℝ) * RT x - (5 / 3 : ℝ) * RF x -
      RU x + RD x + cost x =
        m x * collectedHessianForm (v x) (b x) (e x) (B x) (C x) (E x) (p2 x) -
          (5 / 36 : ℝ) * cubic x + cost x := by
    rw [show 4 * RI x - (5 / 6 : ℝ) * RT x - (5 / 3 : ℝ) * RF x - RU x + RD x = _ from
      green_contributions_collect (m x) (v x) (b x) (e x) (B x) (C x) (E x) (p2 x) (cubic x)]
  have hn : 0 ≤ ∫ x, 4 * I x - (5 / 6 : ℝ) * T x - (5 / 3 : ℝ) * F x -
      U x + D x + cost x ∂μ := integral_nonneg hlocal
  rw [hsum] at hn
  simpa only [hpoint] using hn

end Integral

end
end PositiveEinsteinFour.HighestHessian

end OAI
