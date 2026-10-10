import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CutExpectedOut

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
namespace CoulombAtom

lemma cutOutNumber_eq_sum {L : ℕ} (b : Fin L → Fin 2) :
    (cutOutNumber b : ℝ) = ∑ i : Fin L, if b i ≠ 0 then 1 else 0 := by
  classical
  rw [Finset.sum_boole, cutOutNumber, Fintype.card_subtype]

lemma binary_product_count {L : ℕ} (q : Fin L → Fin 2 → ℝ)
    (hq : ∀ k, ∑ a, q k a ^ 2 = 1) :
    (∑ b : Fin L → Fin 2, (cutOutNumber b : ℝ) * (∏ k, q k (b k))^2) =
      ∑ k, q k 1 ^ 2 := by
  classical
  simp_rw [cutOutNumber_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  have hh (b : Fin L → Fin 2) :
      (if b i ≠ 0 then (1:ℝ) else 0) * (∏ k, q k (b k))^2 =
        ((∏ k ∈ Finset.univ.erase i, q k (b k)) *
          (if b i ≠ 0 then q i (b i) else 0)) ^ 2 := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    split_ifs <;> simp
  simp_rw [hh]
  rw [binary_product_square_sum q hq i (fun a => if a ≠ 0 then q i a else 0)]
  norm_num [Fin.sum_univ_two]

lemma cutExpectedOut_eq_count {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevVector ψ) :
    cutExpectedOut p hp ψ = weightedParticleCount ψ (fun x => (p 1).value x ^ 2) := by
  have hb (b : Fin L → Fin 2) (s : Spins L) :
      Integrable (fun x => (cutOutNumber b : ℝ) *
        ‖(multiplyForm (spatialProduct p hp b) ψ).value s x‖^2) :=
    ((hψ.multiply _).1 s).norm.integrable_sq.const_mul _
  have hi (s : Spins L) (i : Fin L) :
      Integrable (fun x => (p 1).value (x i) ^ 2 * ‖ψ.value s x‖^2) := by
    have hc : Continuous (fun x : Configuration L => (p 1).value (x i)) :=
      (p 1).regular.continuous.comp (continuous_apply i)
    have hm := (memLp_bounded_mul hc ⟨1,fun x => spatial_factor_bound p hp 1 (x i)⟩ (hψ.1 s)).norm.integrable_sq
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] using hm
  unfold cutExpectedOut formMass weightedParticleCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun b _ => hb b s), ← integral_finsetSum _ (fun i _ => hi s i)]
  apply integral_congr_ae (Eventually.of_forall _)
  intro x
  simp only [multiplyForm,spatialProduct,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    mul_pow,sq_abs,← mul_assoc,← Finset.sum_mul]
  congr 1
  exact binary_product_count (fun i a => (p a).value (x i)) (fun i => hp (x i))

lemma weightedParticleCount_integrable {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) {w : Space → ℝ} (hw : Measurable w)
    {B : ℝ} (hb : ∀ x, ‖w x‖ ≤ B) (s : Spins L) (i : Fin L) :
    Integrable (fun x => w (x i) * ‖ψ.value s x‖^2) :=
  ((hψ.1 s).norm.integrable_sq).bdd_mul
    (hw.comp (measurable_pi_apply i)).aestronglyMeasurable
    (Eventually.of_forall fun x => hb (x i))

lemma weightedParticleCount_mono {L : ℕ} {ψ : FormVector L}
    {v w : Space → ℝ}
    (hv : ∀ s i, Integrable (fun x => v (x i) * ‖ψ.value s x‖^2))
    (hw : ∀ s i, Integrable (fun x => w (x i) * ‖ψ.value s x‖^2))
    (hvw : ∀ x, v x ≤ w x) :
    weightedParticleCount ψ v ≤ weightedParticleCount ψ w := by
  apply Finset.sum_le_sum; intro s _
  apply Finset.sum_le_sum; intro i _
  apply integral_mono (hv s i) (hw s i)
  intro x
  exact mul_le_mul_of_nonneg_right (hvw (x i)) (sq_nonneg _)

def tailParticleCount {L : ℕ} (ψ : FormVector L) (R : ℝ) : ℝ :=
  weightedParticleCount ψ (fun x => if R ≤ ‖x‖ then 1 else 0)

lemma tailParticleCount_le_cut {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) {R : ℝ} (hR : 0 < R) :
    tailParticleCount ψ (2*R) ≤
      cutExpectedOut (radialCut 0 hR.le hR) (radialCut_partition 0 hR.le hR) ψ := by
  rw [cutExpectedOut_eq_count _ _ hψ]
  apply weightedParticleCount_mono
  · intro s i
    apply weightedParticleCount_integrable hψ (w := fun x => if 2*R ≤ ‖x‖ then 1 else 0) (B := 1)
    · exact measurable_const.ite (isClosed_le continuous_const continuous_norm).measurableSet measurable_const
    · intro x; split_ifs <;> norm_num
  · intro s i
    apply weightedParticleCount_integrable hψ
      (((radialCut 0 hR.le hR 1).regular.continuous.pow 2).measurable)
      (B := 1)
    intro x
    change ‖(radialCut 0 hR.le hR 1).value x ^ 2‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hh := spatial_factor_bound (radialCut 0 hR.le hR) (radialCut_partition 0 hR.le hR) 1 x
    nlinarith [le_abs_self ((radialCut 0 hR.le hR 1).value x),neg_abs_le ((radialCut 0 hR.le hR 1).value x)]
  · intro x; split_ifs with hx
    · rw [(radialCut_outer hR.le hR (by simpa only [sub_zero,two_mul] using hx)).2,one_pow]
    · positivity

theorem quantum_priced_tail_bound {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) {Z lam ε R : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hR : 0 < R) (hc : Z/R ≤ lam)
    (hm : formMass ψ = 1)
    (he : formEnergy Z ψ + lam * L ≤ priceEnergy (energy Z) lam + ε) :
    (lam-Z/R) * tailParticleCount ψ (2*R) ≤
      ε + (3/2:ℝ) * (Real.pi * smoothTransitionBound / R)^2 * L :=
  (mul_le_mul_of_nonneg_left (tailParticleCount_le_cut hψ.sobolevVector hR)
    (sub_nonneg.mpr hc)).trans (radial_priced_exterior_bound hψ hZ hlam hR hm he)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
