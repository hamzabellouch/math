import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

namespace WeakHessianTransport
variable {Z : Type*} [MetricSpace Z]

def compactToBounded : C_c(Z,ℝ) →ₗ[ℝ] (Z →ᵇ ℝ) where
  toFun := CompactlySupportedContinuousMap.toBoundedContinuousFunction
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] lemma compactToBounded_apply (f : C_c(Z,ℝ)) (x : Z) : compactToBounded f x = f x := rfl

variable [ProperSpace Z]

lemma compact_thickenedIndicator {s : Set Z} (hs : IsCompact s) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun x => (thickenedIndicator hδ s x : ℝ)) := by
  have hc : IsCompact (Metric.cthickening δ s) := hs.cthickening
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  apply Metric.thickening_subset_cthickening δ s
  by_contra h
  exact hx (by simp only [thickenedIndicator_zero hδ s h, NNReal.coe_zero])

def ballCutoff (o : Z) (n : ℕ) : C_c(Z,ℝ) :=
  ⟨⟨fun x => (thickenedIndicator (by norm_num : (0:ℝ)<1) (Metric.closedBall o n) x : ℝ),
    NNReal.continuous_coe.comp (thickenedIndicator (by norm_num : (0:ℝ)<1) (Metric.closedBall o n)).continuous⟩,
    compact_thickenedIndicator (isCompact_closedBall o n) (by norm_num)⟩

lemma ballCutoff_nonneg (o : Z) (n : ℕ) (x : Z) : 0 ≤ ballCutoff o n x := NNReal.coe_nonneg _
lemma ballCutoff_le_one (o : Z) (n : ℕ) (x : Z) : ballCutoff o n x ≤ 1 :=
  NNReal.coe_le_coe.mpr (thickenedIndicator_le_one _ _ _)
lemma ballCutoff_eq_one (o : Z) (n : ℕ) {x : Z} (hx : x ∈ Metric.closedBall o n) :
    ballCutoff o n x = 1 := by
  change (thickenedIndicator _ _ x : ℝ) = 1
  rw [thickenedIndicator_one _ _ hx]
  rfl

lemma tendsto_ballCutoff (o : Z) (x : Z) : Tendsto (fun n => ballCutoff o n x) atTop (𝓝 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (dist x o)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (ballCutoff_eq_one o n (hN.le.trans (Nat.cast_le.mpr hn))).symm

def boundedMulCompact (f : Z →ᵇ ℝ) (η : C_c(Z,ℝ)) : C_c(Z,ℝ) :=
  ⟨⟨fun x => f x*η x, f.continuous.mul η.continuous⟩,
    η.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right⟩

variable [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]

lemma exists_finite_measure_le_positive_functional
    (g : (Z →ᵇ ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g) :
    ∃ q : Measure Z, IsFiniteMeasure q ∧
      (∀ f : C_c(Z,ℝ), (∫ x, f x ∂q) = g (compactToBounded f)) ∧
      (∀ f : Z →ᵇ ℝ, (∀ x, 0 ≤ f x) → (∫ x, f x ∂q) ≤ g f) := by
  let Λ : C_c(Z,ℝ) →ₚ[ℝ] ℝ :=
    { g.comp compactToBounded with monotone' := fun f h hfh => hg (fun x => hfh x) }
  let q := RealRMK.rieszMeasure Λ
  let o : Z := Classical.arbitrary Z
  have hCc (f : C_c(Z,ℝ)) : (∫ x, f x ∂q) = g (compactToBounded f) :=
    RealRMK.integral_rieszMeasure Λ f
  have hb (n : ℕ) : q (Metric.closedBall o n) ≤
      ENNReal.ofReal (g (BoundedContinuousFunction.const Z 1)) := by
    exact (RealRMK.rieszMeasure_le_of_eq_one Λ (ballCutoff_nonneg o n)
      (isCompact_closedBall o n) (fun x hx => ballCutoff_eq_one o n hx)).trans
      (ENNReal.ofReal_le_ofReal (hg (fun x => ballCutoff_le_one o n x)))
  have huniv : (⋃ n : ℕ, Metric.closedBall o (n:ℝ)) = univ := by
    ext x
    simp only [mem_iUnion,Metric.mem_closedBall,mem_univ,iff_true]
    obtain ⟨n,hn⟩ := exists_nat_gt (dist x o)
    exact ⟨n,hn.le⟩
  have hmon : Monotone (fun n : ℕ => Metric.closedBall o (n:ℝ)) :=
    fun n k hnk => Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hnk)
  have htotal : q univ ≤ ENNReal.ofReal (g (BoundedContinuousFunction.const Z 1)) := by
    rw [← huniv,hmon.directed_le.measure_iUnion]
    exact iSup_le hb
  have hfinite : IsFiniteMeasure q := ⟨htotal.trans_lt ENNReal.ofReal_lt_top⟩
  let := hfinite
  refine ⟨q,hfinite,hCc,?_⟩
  intro f hf
  have hi (n : ℕ) : (∫ x, boundedMulCompact f (ballCutoff o n) x ∂q) ≤ g f := by
    rw [hCc]
    apply hg
    intro x
    exact mul_le_of_le_one_right (hf x) (ballCutoff_le_one o n x)
  have hl : Tendsto (fun n => ∫ x, boundedMulCompact f (ballCutoff o n) x ∂q)
      atTop (𝓝 (∫ x, f x ∂q)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (boundedMulCompact f (ballCutoff o n)).continuous.aestronglyMeasurable
    · exact integrable_const ‖f‖
    · intro n
      exact ae_of_all _ fun x => by
        change ‖f x*ballCutoff o n x‖ ≤ ‖f‖
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg o n x)]
        exact (mul_le_of_le_one_right (norm_nonneg _) (ballCutoff_le_one o n x)).trans
          (f.norm_coe_le_norm x)
    · exact ae_of_all _ fun x => by
        change Tendsto (fun n => f x*ballCutoff o n x) atTop (𝓝 (f x))
        simpa only [mul_one] using (tendsto_const_nhds.mul (tendsto_ballCutoff o x))
  exact le_of_tendsto' hl hi
end WeakHessianTransport

end

end OAI
