import OAI.Analysis.Mahler.LevelForms
import OAI.Analysis.Mahler.WedgeAlgebra

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

/-- Restriction to any linear space of vectors tangent to an energy level. -/
theorem level_oneForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E) :
    (oneForm (dcLinear (logTau f)) x).toAlternatingMap.compLinearMap S.subtype =
      (energy f x)⁻¹ •
        (oneForm (dcLinear (energy f)) x).toAlternatingMap.compLinearMap S.subtype := by
  ext v
  change dcLinear (logTau f) x (v 0) = (energy f x)⁻¹ * dcLinear (energy f) x (v 0)
  rw [dcLinear_apply, dcLinear_apply,
    dc_logTau_eq_div (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx)) ht]
  ring

theorem level_twoForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E)
    (hS : ∀ v : S, fderiv ℝ (energy f) x v = 0) :
    (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap.compLinearMap S.subtype =
      (energy f x)⁻¹ •
        (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap.compLinearMap S.subtype := by
  ext v
  change extDeriv (oneForm (dcLinear (logTau f))) x (fun i => (v i : E)) =
    (energy f x)⁻¹ * extDeriv (oneForm (dcLinear (energy f))) x (fun i => (v i : E))
  have hv : (fun i => (v i : E)) = ![(v 0 : E), (v 1 : E)] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact extDeriv_logTau_on_level hU hx hf ht (v 0) (v 1) (hS (v 0)) (hS (v 1))

/-- The complete boundary form scales by tau^(-(k+1)), with the actual
shuffle exterior power. No integration identity is assumed. -/
theorem level_boundaryForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E)
    (hS : ∀ v : S, fderiv ℝ (energy f) x v = 0) (k : ℕ) :
    wedge ((oneForm (dcLinear (logTau f)) x).toAlternatingMap.compLinearMap S.subtype)
      (wedgePower ((extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap.compLinearMap S.subtype) k) =
    ((energy f x)⁻¹) ^ (k+1) •
      wedge ((oneForm (dcLinear (energy f)) x).toAlternatingMap.compLinearMap S.subtype)
        (wedgePower ((extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap.compLinearMap S.subtype) k) := by
  rw [level_oneForm_scaling hU hx hf ht S, level_twoForm_scaling hU hx hf ht S hS,
    wedgePower_smul, wedge_smul_left, wedge_smul_right, smul_smul, pow_succ']

lemma coordinateMap_energy (n : ℕ) : energy (coordinateMap n) = normEnergy n := by
  funext z
  rw [energy_eq_tau]
  simp [tau, coordinateMap, normEnergy, EuclideanSpace.norm_sq_eq,
    Complex.normSq_eq_norm_sq, Complex.ofReal_sum]

lemma normEnergy_fderiv {n : ℕ} (x v : ComplexEuclidean n) :
    fderiv ℝ (normEnergy n) x v = (2 * inner ℝ x v : ℝ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt (normEnergy n) _ x at hd
  rw [hd.fderiv]
  simp

lemma normEnergy_sphere_tangent {n : ℕ} (x : ComplexEuclidean n)
    (v : sphereTangent x) : fderiv ℝ (normEnergy n) x v = 0 := by
  rw [normEnergy_fderiv]
  have hv : inner ℝ x (v : ComplexEuclidean n) = 0 :=
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property)
  simp [hv]

/-- The reference logarithmic boundary form equals the actual squared-norm
boundary form on the unit sphere, in every exterior degree. -/
theorem reference_sphere_boundaryForm {n : ℕ} {z : ComplexEuclidean n}
    (hz : ‖z‖ = 1) (k : ℕ) :
    wedge (tangentForm z (oneForm (dcLinear (logTau (coordinateMap n))) z).toAlternatingMap)
      (wedgePower (tangentForm z
        (extDeriv (oneForm (dcLinear (logTau (coordinateMap n)))) z).toAlternatingMap) k) =
    wedge (tangentForm z (oneForm (dcLinear (normEnergy n)) z).toAlternatingMap)
      (wedgePower (tangentForm z
        (extDeriv (oneForm (dcLinear (normEnergy n))) z).toAlternatingMap) k) := by
  have hnz : z ≠ 0 := by intro h; simp [h] at hz
  have h := level_boundaryForm_scaling isOpen_univ (Set.mem_univ z)
    (fun j => (coordinateMap_differentiable n j).differentiableOn)
    (coordinateMap_tau_pos hnz) (sphereTangent z)
    (by rw [coordinateMap_energy]; exact normEnergy_sphere_tangent z) k
  simpa only [coordinateMap_energy, normEnergy, hz, one_pow, Complex.ofReal_one,
    inv_one, one_smul, tangentForm] using h

end Mahler

end OAI
