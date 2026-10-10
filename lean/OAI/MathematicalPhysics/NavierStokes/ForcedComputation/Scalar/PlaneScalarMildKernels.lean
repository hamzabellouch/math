import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatTimeContinuity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.WeaklySingularEquation

namespace OAI

/-! The three genuine heat kernels needed for the scalar mild equation on finite spatial jets. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Real Set ShearFlows
open scoped Topology

abbrev Jet (k : ℕ) := BoundedSpatialJets.Space Plane ℝ k
abbrev PositiveTime := {r : ℝ // 0 < r}

private def zeroExtension {E : Type*} [Zero E] (L : PositiveTime → E) (r : ℝ) : E :=
  if hr : 0 < r then L ⟨r,hr⟩ else 0

private theorem zeroExtension_continuous {E : Type*} [TopologicalSpace E] [Zero E]
    (L : PositiveTime → E) (hL : Continuous L) : ContinuousOn (zeroExtension L) (Ioi 0) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (Ioi (0 : ℝ)).domRestrict (zeroExtension L) = L := by
    funext r
    exact dite_eq_left r.property
  rw [he]
  exact hL

/-- The cutoff is one on the working interval and supplies a global square-root bound. -/
def heatCutoff (T : ℝ) (r : PositiveTime) : ℝ :=
  min 1 (Real.sqrt (T+1) / Real.sqrt (r : ℝ))

theorem heatCutoff_continuous (T : ℝ) : Continuous (heatCutoff T) := by
  exact continuous_const.min (continuous_const.div
    (Real.continuous_sqrt.comp continuous_subtype_val)
    (fun r => (Real.sqrt_pos.mpr r.property).ne'))

theorem heatCutoff_nonneg (T : ℝ) (r : PositiveTime) : 0 ≤ heatCutoff T r :=
  le_min zero_le_one (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem heatCutoff_le (T : ℝ) (r : PositiveTime) :
    heatCutoff T r ≤ Real.sqrt (T+1) * WeaklySingular.inverseSqrt (r : ℝ) := by
  simpa only [heatCutoff, div_eq_mul_inv, WeaklySingular.inverseSqrt] using
    (min_le_right (1 : ℝ) (Real.sqrt (T+1) / Real.sqrt (r : ℝ)))

theorem heatCutoff_eq_one {T : ℝ} (r : PositiveTime) (hr : (r : ℝ) ≤ T) :
    heatCutoff T r = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (Real.sqrt_pos.mpr r.property)).mpr
  simpa only [one_mul] using Real.sqrt_le_sqrt (show (r : ℝ) ≤ T+1 by linarith)

private def scaledTime {ν : ℝ} (hν : 0 < ν) (r : PositiveTime) : PositiveTime :=
  ⟨ν * (r : ℝ), mul_pos hν r.property⟩

private theorem scaledTime_continuous {ν : ℝ} (hν : 0 < ν) : Continuous (scaledTime hν) :=
  (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- The unmodified heat operator, set to zero only at nonpositive times. -/
def rawHeatKernel {ν : ℝ} (hν : 0 < ν) (k : ℕ) : ℝ → Jet k →L[ℝ] Jet k :=
  zeroExtension (fun r => PlaneHeat.heatOperator ℝ k (ν * r.val) (mul_pos hν r.property))

/-- The globally square-root-bounded heat kernel, unchanged on the working interval. -/
def heatKernel {ν : ℝ} (hν : 0 < ν) (k : ℕ) (T : ℝ) : ℝ → Jet k →L[ℝ] Jet k :=
  zeroExtension (fun r => heatCutoff T r •
    PlaneHeat.heatOperator ℝ k (ν * r.val) (mul_pos hν r.property))

/-- A Cartesian heat derivative needs no additional cutoff. -/
def gradientKernel {ν : ℝ} (hν : 0 < ν) (k : ℕ) (j : Fin 2) :
    ℝ → Jet k →L[ℝ] Jet k :=
  zeroExtension (fun r => PlaneHeat.gradientOperator ℝ k (ν * r.val) (mul_pos hν r.property) j)

theorem rawHeatKernel_pos {ν r : ℝ} (hν : 0 < ν) (k : ℕ) (hr : 0 < r) :
    rawHeatKernel hν k r = PlaneHeat.heatOperator ℝ k (ν*r) (mul_pos hν hr) :=
  dite_eq_left hr

theorem rawHeatKernel_nonpos {ν r : ℝ} (hν : 0 < ν) (k : ℕ) (hr : r ≤ 0) :
    rawHeatKernel hν k r = 0 := dite_eq_right (not_lt.mpr hr)

theorem gradientKernel_pos {ν r : ℝ} (hν : 0 < ν) (k : ℕ) (j : Fin 2) (hr : 0 < r) :
    gradientKernel hν k j r = PlaneHeat.gradientOperator ℝ k (ν*r) (mul_pos hν hr) j :=
  dite_eq_left hr

theorem gradientKernel_nonpos {ν r : ℝ} (hν : 0 < ν) (k : ℕ) (j : Fin 2) (hr : r ≤ 0) :
    gradientKernel hν k j r = 0 := dite_eq_right (not_lt.mpr hr)

theorem heatKernel_continuous {ν : ℝ} (hν : 0 < ν) (k : ℕ) (T : ℝ) :
    ContinuousOn (heatKernel hν k T) (Ioi 0) :=
  zeroExtension_continuous _ ((heatCutoff_continuous T).smul
    ((PlaneHeat.continuous_heatOperator ℝ k).comp (scaledTime_continuous hν)))

theorem gradientKernel_continuous {ν : ℝ} (hν : 0 < ν) (k : ℕ) (j : Fin 2) :
    ContinuousOn (gradientKernel hν k j) (Ioi 0) :=
  zeroExtension_continuous _
    ((PlaneHeat.continuous_gradientOperator ℝ k j).comp (scaledTime_continuous hν))

theorem heatKernel_eq_raw {ν T r : ℝ} (hν : 0 < ν) (k : ℕ) (hr : r ≤ T) :
    heatKernel hν k T r = rawHeatKernel hν k r := by
  by_cases hp : 0 < r
  · simp only [heatKernel, rawHeatKernel, zeroExtension, dite_eq_left hp,
      heatCutoff_eq_one ⟨r,hp⟩ hr, one_smul]
  · simp only [heatKernel, rawHeatKernel, zeroExtension, dite_eq_right hp]

theorem heatKernel_bound {ν : ℝ} (hν : 0 < ν) (k : ℕ) (T : ℝ) :
    ∀ r, 0 ≤ r → ‖heatKernel hν k T r‖ ≤
      Real.sqrt (T+1) * WeaklySingular.inverseSqrt r := by
  intro r _
  by_cases hr : 0 < r
  · rw [heatKernel, zeroExtension, dite_eq_left hr]
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs, abs_of_nonneg (heatCutoff_nonneg T ⟨r,hr⟩)]
    exact (mul_le_mul_of_nonneg_left
      (PlaneHeat.norm_heatOperator_le ℝ k (ν*r) (mul_pos hν hr))
      (heatCutoff_nonneg T ⟨r,hr⟩)).trans <| by
        rw [mul_one]
        exact heatCutoff_le T ⟨r,hr⟩
  · simp only [heatKernel, zeroExtension, dite_eq_right hr, ContinuousLinearMap.opNorm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (WeaklySingular.inverseSqrt_nonneg _)

theorem gradientKernel_bound {ν : ℝ} (hν : 0 < ν) (k : ℕ) (j : Fin 2) :
    ∀ r, 0 ≤ r → ‖gradientKernel hν k j r‖ ≤
      (2 / Real.sqrt ν) * WeaklySingular.inverseSqrt r := by
  intro r _
  by_cases hr : 0 < r
  · rw [gradientKernel, zeroExtension, dite_eq_left hr]
    apply (PlaneHeat.norm_gradientOperator_le ℝ k (ν*r) (mul_pos hν hr) j).trans_eq
    rw [Real.sqrt_mul hν.le]
    simp only [div_eq_mul_inv, mul_inv_rev, WeaklySingular.inverseSqrt]
    ring
  · simp only [gradientKernel, zeroExtension, dite_eq_right hr, ContinuousLinearMap.opNorm_zero]
    exact mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg ν))
      (WeaklySingular.inverseSqrt_nonneg r)

/-- Index zero is the heat term; the other two indices are Cartesian derivatives. -/
def kernels {ν : ℝ} (hν : 0 < ν) (k : ℕ) (T : ℝ) :
    Fin 3 → ℝ → Jet k →L[ℝ] Jet k :=
  Fin.cases (heatKernel hν k T) (gradientKernel hν k)

def rawKernels {ν : ℝ} (hν : 0 < ν) (k : ℕ) : Fin 3 → ℝ → Jet k →L[ℝ] Jet k :=
  Fin.cases (rawHeatKernel hν k) (gradientKernel hν k)

def kernelConstants (ν T : ℝ) : Fin 3 → ℝ :=
  Fin.cases (Real.sqrt (T+1)) (fun _ => 2 / Real.sqrt ν)

theorem kernelConstants_nonneg (ν T : ℝ) (i : Fin 3) : 0 ≤ kernelConstants ν T i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Real.sqrt_nonneg _
  · exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem kernels_continuous {ν : ℝ} (hν : 0 < ν) (k : ℕ) (T : ℝ) (i : Fin 3) :
    ContinuousOn (kernels hν k T i) (Ioi 0) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact heatKernel_continuous hν k T
  · exact gradientKernel_continuous hν k j

theorem kernels_bound {ν : ℝ} (hν : 0 < ν) (k : ℕ) (T : ℝ) (i : Fin 3) :
    ∀ r, 0 ≤ r → ‖kernels hν k T i r‖ ≤ kernelConstants ν T i * WeaklySingular.inverseSqrt r := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact heatKernel_bound hν k T
  · exact gradientKernel_bound hν k j

theorem kernels_eq_raw {ν T r : ℝ} (hν : 0 < ν) (k : ℕ) (hr : r ≤ T) (i : Fin 3) :
    kernels hν k T i r = rawKernels hν k i r := by
  refine Fin.cases ?_ (fun _ => rfl) i
  exact heatKernel_eq_raw hν k hr

end ForcedComputation.PlaneScalarMild

end

end OAI
