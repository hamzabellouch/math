import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketInsert
import OAI.Analysis.CoulombIonization.Localization.PacketDensityRadius

namespace OAI

noncomputable section

namespace CoulombAtom

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
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
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
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

lemma rotation_core_kernel_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y p : Space) {B : ℝ} (hp : ‖p‖ < B) (hc : FormAvoids ψ (ball y B))
    (s : Spins N) (i : Fin N) :
    Integrable (fun q : SpatialRotation × Configuration N =>
      ‖ψ.value s q.2‖^2/‖q.2 i-(y+rotate q.1 p)‖) (rotationMeasure.prod volume) := by
  have hm1 : AEStronglyMeasurable (fun q : SpatialRotation × Configuration N =>
      ‖ψ.value s q.2‖^2) (rotationMeasure.prod volume) :=
    ((hψ.1 s).aestronglyMeasurable.norm.pow 2).comp_snd
  have ha : Continuous (fun q : SpatialRotation × Configuration N => rotate q.1 p) :=
    (continuous_subtype_val.comp continuous_fst).clm_apply continuous_const
  have hm2 : AEStronglyMeasurable (fun q : SpatialRotation × Configuration N =>
      ‖q.2 i-(y+rotate q.1 p)‖⁻¹) (rotationMeasure.prod volume) :=
    ((((continuous_apply i).comp continuous_snd).sub (continuous_const.add ha)).norm.measurable.inv).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun q : SpatialRotation × Configuration N =>
      ‖ψ.value s q.2‖^2/‖q.2 i-(y+rotate q.1 p)‖) (rotationMeasure.prod volume) := by
    simpa only [div_eq_mul_inv] using hm1.fun_mul hm2
  apply ((((hψ.1 s).integrable_norm_pow (by norm_num)).comp_snd rotationMeasure).div_const
    (B-‖p‖)).mono' hm
  apply Eventually.of_forall
  intro q
  change ‖‖ψ.value s q.2‖^2/‖q.2 i-(y+rotate q.1 p)‖‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (norm_nonneg _))]
  by_cases hz : ψ.value s q.2 = 0
  · simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,le_refl]
  · have hd : B ≤ ‖q.2 i-y‖ := by
      by_contra hh
      exact hz (hc q.2 i (mem_ball.mpr (not_le.mp hh)) s).1
    have ht := norm_add_le (q.2 i-(y+rotate q.1 p)) (rotate q.1 p)
    rw [show q.2 i-(y+rotate q.1 p)+rotate q.1 p = q.2 i-y by abel,
      (rotate q.1).norm_map] at ht
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr hp) (by linarith)

lemma rotation_core_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y p : Space) {B : ℝ} (hp : ‖p‖ < B) (hc : FormAvoids ψ (ball y B)) :
    Integrable (fun g : SpatialRotation => coreCoulombAt ψ (y+rotate g p)) rotationMeasure := by
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  exact (rotation_core_kernel_integrable hψ y p hp hc s i).integral_prod_left

theorem rotation_core_newton {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y p : Space) {B : ℝ} (hp : ‖p‖ < B) (hc : FormAvoids ψ (ball y B)) :
    (∫ g : SpatialRotation, coreCoulombAt ψ (y+rotate g p) ∂rotationMeasure) =
      coreCoulombAt ψ y := by
  unfold coreCoulombAt
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_integral_swap (rotation_core_kernel_integrable hψ y p hp hc s i)]
      apply integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hz : ψ.value s x = 0
      · simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,integral_zero]
      · have hd : B ≤ ‖x i-y‖ := by
          by_contra hh
          exact hz (hc x i (mem_ball.mpr (not_le.mp hh)) s).1
        have he : ∀ g : SpatialRotation, x i-(y+rotate g p) = (x i-y)-rotate g p := by
          intro g; abel
        simp_rw [he,div_eq_mul_inv,integral_const_mul]
        have hn := rotation_kernel_newton p (x i-y) (hp.trans_le hd)
        simpa only [one_div] using congrArg (fun a => ‖ψ.value s x‖^2*a) hn
    · intro i _
      exact (rotation_core_kernel_integrable hψ y p hp hc s i).integral_prod_left
  · intro s _
    apply integrable_finsetSum
    intro i _
    exact (rotation_core_kernel_integrable hψ y p hp hc s i).integral_prod_left

lemma rotation_nuclear_integrable (y p : Space) (hp : ‖p‖ < ‖y‖) :
    Integrable (fun g : SpatialRotation => 1/‖y+rotate g p‖) rotationMeasure := by
  have hh := rotation_kernel_integrable p (-y) (by simpa only [norm_neg] using hp)
  have he (g : SpatialRotation) : ‖-y-rotate g p‖ = ‖y+rotate g p‖ := by
    rw [show -y-rotate g p = -(y+rotate g p) by abel,norm_neg]
  simpa only [he] using hh

lemma rotation_nuclear_newton (y p : Space) (hp : ‖p‖ < ‖y‖) :
    (∫ g : SpatialRotation, 1/‖y+rotate g p‖ ∂rotationMeasure) = 1/‖y‖ := by
  have hh := rotation_kernel_newton p (-y) (by simpa only [norm_neg] using hp)
  have he (g : SpatialRotation) : ‖-y-rotate g p‖ = ‖y+rotate g p‖ := by
    rw [show -y-rotate g p = -(y+rotate g p) by abel,norm_neg]
  simpa only [he,norm_neg] using hh


open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators


def rotatedCenters (y : Space) (p : ℕ → Space) (g : SpatialRotation) (i : ℕ) : Space :=
  y+rotate g (p i)

lemma rotatedCenters_distance (y : Space) (p : ℕ → Space) (g : SpatialRotation) (i j : ℕ) :
    ‖rotatedCenters y p g i-rotatedCenters y p g j‖ = ‖p i-p j‖ := by
  simp only [rotatedCenters,add_sub_add_left_eq_sub,← (rotate g).map_sub,(rotate g).norm_map]

lemma rotatedCenters_pair (y : Space) (p : ℕ → Space) (g : SpatialRotation) (k : ℕ) :
    packetPairEnergy (rotatedCenters y p g) k = packetPairEnergy p k := by
  simp only [packetPairEnergy,rotatedCenters_distance]

lemma rotatedCenters_avoids {N : ℕ} {ψ : FormVector N} (y : Space) (p : ℕ → Space)
    (g : SpatialRotation) {B r : ℝ} (hc : FormAvoids ψ (ball y B))
    {i : ℕ} (hi : ‖p i‖+2*r ≤ B) :
    FormAvoids ψ (ball (rotatedCenters y p g i) (2*r)) := by
  apply hc.mono
  intro x hx
  apply mem_ball.mpr
  change ‖x-y‖ < B
  have ht := norm_add_le (x-rotatedCenters y p g i) (rotate g (p i))
  rw [show x-rotatedCenters y p g i+rotate g (p i) = x-y by dsimp [rotatedCenters]; abel,
    (rotate g).norm_map] at ht
  have hh := mem_ball.mp hx
  change ‖x-rotatedCenters y p g i‖ < 2*r at hh
  linarith

lemma rotatedCenters_nuclear (y : Space) (p : ℕ → Space) (g : SpatialRotation)
    {r : ℝ} {i : ℕ} (hi : ‖p i‖+r < ‖y‖) : r < ‖rotatedCenters y p g i‖ := by
  have ht := norm_sub_le (y+rotate g (p i)) (rotate g (p i))
  rw [add_sub_cancel_right,(rotate g).norm_map] at ht
  dsimp only [rotatedCenters]
  linarith

lemma rotatedScreened_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (p : ℕ → Space) {B : ℝ} (hc : FormAvoids ψ (ball y B)) (k : ℕ)
    (hp : ∀ i < k, ‖p i‖ < B) (hn : ∀ i < k, ‖p i‖ < ‖y‖) (Z : ℝ) :
    Integrable (fun g : SpatialRotation => packetScreenedSum ψ Z (rotatedCenters y p g) k)
      rotationMeasure := by
  apply integrable_finsetSum
  intro i hi
  have hik := Finset.mem_range.mp hi
  have hh := ((rotation_nuclear_integrable y (p i) (hn i hik)).const_mul (Z*formMass ψ)).sub
    (rotation_core_integrable hψ y (p i) (hp i hik) hc)
  change Integrable (fun g : SpatialRotation => (Z*formMass ψ)*(1/‖y+rotate g (p i)‖) -
    coreCoulombAt ψ (y+rotate g (p i))) rotationMeasure at hh
  simpa only [mul_one_div,rotatedCenters] using hh

lemma rotatedScreened_average {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (p : ℕ → Space) {B : ℝ} (hc : FormAvoids ψ (ball y B)) (k : ℕ)
    (hp : ∀ i < k, ‖p i‖ < B) (hn : ∀ i < k, ‖p i‖ < ‖y‖) (Z : ℝ) :
    (∫ g : SpatialRotation, packetScreenedSum ψ Z (rotatedCenters y p g) k ∂rotationMeasure) =
      (k:ℝ)*(Z*formMass ψ/‖y‖-coreCoulombAt ψ y) := by
  unfold packetScreenedSum
  rw [integral_finsetSum]
  · have he (i : ℕ) (hi : i ∈ Finset.range k) :
        (∫ g : SpatialRotation, (Z*formMass ψ/‖rotatedCenters y p g i‖ -
          coreCoulombAt ψ (rotatedCenters y p g i)) ∂rotationMeasure) =
          Z*formMass ψ/‖y‖-coreCoulombAt ψ y := by
      have hik := Finset.mem_range.mp hi
      have h1 : Integrable (fun g : SpatialRotation => Z*formMass ψ/‖rotatedCenters y p g i‖)
          rotationMeasure := by
        simpa only [mul_one_div,rotatedCenters] using
          (rotation_nuclear_integrable y (p i) (hn i hik)).const_mul (Z*formMass ψ)
      have h2 : Integrable (fun g : SpatialRotation => coreCoulombAt ψ (rotatedCenters y p g i))
          rotationMeasure := rotation_core_integrable hψ y (p i) (hp i hik) hc
      rw [integral_sub h1 h2]
      rw [show (fun g : SpatialRotation => Z*formMass ψ/‖rotatedCenters y p g i‖) =
        (fun g : SpatialRotation => (Z*formMass ψ)*(1/‖y+rotate g (p i)‖)) by
          funext g; simp only [rotatedCenters,mul_one_div],integral_const_mul,
        rotation_nuclear_newton y (p i) (hn i hik),mul_one_div]
      simp only [rotatedCenters]
      rw [rotation_core_newton hψ y (p i) (hp i hik) hc]
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  · intro i hi
    have hik := Finset.mem_range.mp hi
    have hh := ((rotation_nuclear_integrable y (p i) (hn i hik)).const_mul (Z*formMass ψ)).sub
      (rotation_core_integrable hψ y (p i) (hp i hik) hc)
    change Integrable (fun g : SpatialRotation => (Z*formMass ψ)*(1/‖y+rotate g (p i)‖) -
      coreCoulombAt ψ (y+rotate g (p i))) rotationMeasure at hh
    simpa only [mul_one_div,rotatedCenters] using hh

theorem averaged_many_packet_screening {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : Space) (p : ℕ → Space) {B r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : FormAvoids ψ (ball y B)) (hp : ∀ i < k, ‖p i‖+2*r ≤ B)
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖p i-p j‖)
    (hn : ∀ i < k, ‖p i‖+r < ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (k:ℝ)*(Z*formMass ψ/‖y‖-coreCoulombAt ψ y) ≤
      (formEnergy Z ψ + lam*N*formMass ψ - priceEnergy (energy Z) lam*formMass ψ) +
      formMass ψ * ((k:ℝ)*(radialPacketKinetic/r^2+lam) + packetPairEnergy p k) := by
  have hp' : ∀ i < k, ‖p i‖ < B := fun i hi => by have := hp i hi; linarith
  have hn' : ∀ i < k, ‖p i‖ < ‖y‖ := fun i hi => by have := hn i hi; linarith
  have hbound (g : SpatialRotation) := many_packet_screening hψ (rotatedCenters y p g) hr k
    (fun i hi => rotatedCenters_avoids y p g hc (hp i hi))
    (fun i j hij hj => by rw [rotatedCenters_distance]; exact hsep i j hij hj)
    (fun i hi => rotatedCenters_nuclear y p g (hn i hi)) hZ hlam
  simp_rw [rotatedCenters_pair] at hbound
  have hh := integral_mono
    (rotatedScreened_integrable hψ.sobolevVector y p hc k hp' hn' Z)
    (integrable_const _) hbound
  rw [rotatedScreened_average hψ.sobolevVector y p hc k hp' hn' Z] at hh
  simpa only [integral_const,probReal_univ,one_smul] using hh


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
