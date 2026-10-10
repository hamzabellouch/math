import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ConstantGeometricEnergy

namespace OAI


noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

lemma continuous_cutoff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set V} (hU : IsOpen U) {f : V → D} (hf : ContinuousOn f U)
    {x₀ : V} (φ : ContDiffBump x₀) (hφ : tsupport φ ⊆ U) :
    Continuous (fun x => φ x • f x) := by
  apply continuous_of_tsupport
  intro x hx
  exact φ.continuous.continuousAt.smul (hf.continuousAt
    (hU.mem_nhds (hφ (tsupport_smul_subset_left _ _ hx))))

lemma cutoff_bound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set V} {f : V → D} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x ∈ U, ‖f x‖ ≤ C)
    {x₀ : V} (φ : ContDiffBump x₀) (hφ : tsupport φ ⊆ U) (x : V) :
    ‖φ x • f x‖ ≤ C := by
  by_cases hx : φ x = 0
  · simpa only [hx,zero_smul,norm_zero] using hC
  have hxU : x ∈ U := hφ (subset_tsupport _ hx)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg φ.nonneg]
  calc
    φ x * ‖f x‖ ≤ φ x * C := mul_le_mul_of_nonneg_left (hf x hxU) φ.nonneg
    _ ≤ 1*C := mul_le_mul_of_nonneg_right φ.le_one hC
    _ = C := one_mul _

def patchPrincipal (c : Fin 4 → Pair →L[ℝ] V) (a : Fin 4 → V → Pair →L[ℝ] V)
    {x₀ : V} (φ : ContDiffBump x₀) : Fin 4 → V → Pair →L[ℝ] V :=
  fun i x => φ x • (a i x-c i) + c i

def patchLower (b : V → Pair →L[ℝ] V) {x₀ : V} (φ : ContDiffBump x₀) : V → Pair →L[ℝ] V :=
  fun x => φ x • b x

lemma patchPrincipal_continuous {U : Set V} (hU : IsOpen U)
    (c : Fin 4 → Pair →L[ℝ] V) (a : Fin 4 → V → Pair →L[ℝ] V)
    (ha : ∀ i, ContinuousOn (a i) U) {x₀ : V} (φ : ContDiffBump x₀)
    (hφ : tsupport φ ⊆ U) (i : Fin 4) : Continuous (patchPrincipal c a φ i) :=
  (continuous_cutoff hU ((ha i).sub continuousOn_const) φ hφ).add continuous_const

lemma patchPrincipal_bound {U : Set V} (c : Fin 4 → Pair →L[ℝ] V)
    (a : Fin 4 → V → Pair →L[ℝ] V) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ x ∈ U, ∀ i, ‖a i x-c i‖ ≤ δ) {x₀ : V} (φ : ContDiffBump x₀)
    (hφ : tsupport φ ⊆ U) (x : V) (i : Fin 4) : ‖patchPrincipal c a φ i x-c i‖ ≤ δ := by
  simpa only [patchPrincipal,add_sub_cancel_right] using
    cutoff_bound hδ (fun x hx => ha x hx i) φ hφ x

lemma system_patch_eq (c : Fin 4 → Pair →L[ℝ] V)
    (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    {x₀ : V} (φ : ContDiffBump x₀) (A B : S)
    (hA : tsupport A ⊆ Metric.closedBall x₀ φ.rIn)
    (hB : tsupport B ⊆ Metric.closedBall x₀ φ.rIn) (x : V) :
    system (patchPrincipal c a φ) (patchLower b φ) A B x = system a b A B x := by
  by_cases hx : x ∈ Metric.closedBall x₀ φ.rIn
  · simp only [system,patchPrincipal,patchLower,φ.one_of_mem_closedBall hx,
      one_smul,sub_add_cancel]
  · have ha : x ∉ tsupport A := fun h => hx (hA h)
    have hb : x ∉ tsupport B := fun h => hx (hB h)
    have hAa : A x = 0 := image_eq_zero_of_notMem_tsupport ha
    have hBb : B x = 0 := image_eq_zero_of_notMem_tsupport hb
    have hAd (i : Fin 4) : coordinateDeriv i A x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => ha (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
    have hBd (i : Fin 4) : coordinateDeriv i B x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hb (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
    simp only [system,hAa,hBb,hAd,hBd]
    have hp : pair 0 0 = 0 := by ext i; fin_cases i <;> rfl
    simp only [hp,map_zero,Finset.sum_const_zero,add_zero]

end TamingCompatibility.MatrixEnergy

end

end OAI
