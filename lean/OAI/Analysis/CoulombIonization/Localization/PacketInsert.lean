import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FormBody

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
namespace CoulombAtom

def packetInsert {N : ℕ} (ψ : FormVector N) (y : ℕ → Space) (r : ℝ) :
    (k : ℕ) → FormVector (N+k)
  | 0 => ψ
  | k+1 => insertOrbital (packetInsert ψ y r k) (radialLocalOrbital (y k) r)

lemma packetInsert_sobolev {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ) : SobolevFermion (packetInsert ψ y r k) := by
  induction k with
  | zero => exact hψ
  | succ k ih => exact insertOrbital_sobolev ih (radialLocalOrbital_admissible (y k) hr).sobolevFermion

lemma packetInsert_avoids {N : ℕ} {ψ : FormVector N} (y : ℕ → Space) {r : ℝ}
    (hr : 0 < r) (k : ℕ) (z : Space)
    (hc : FormAvoids ψ (Metric.ball z (2*r)))
    (hsep : ∀ i < k, 3*r ≤ ‖y i-z‖) : FormAvoids (packetInsert ψ y r k) (Metric.ball z (2*r)) := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    exact (ih (fun i hi => hsep i (by omega))).insertOrbital
      (radialLocalOrbital_avoids (y k) z hr (by have := hsep k (by omega); linarith))

lemma packetInsert_disjoint {N : ℕ} {ψ : FormVector N} (y : ℕ → Space) {r : ℝ}
    (hr : 0 < r) (k : ℕ)
    (hc : FormAvoids ψ (Metric.ball (y k) (2*r)))
    (hsep : ∀ i < k, 3*r ≤ ‖y i-y k‖) :
    FormsDisjoint (insertionTerm (tensorForm (packetInsert ψ y r k) (radialLocalOrbital (y k) r))) := by
  apply tensor_insertion_disjoint_set _ _ (Metric.ball (y k) (2*r))
  · exact packetInsert_avoids y hr k (y k) hc hsep
  · intro x hx
    have hh : 2*r ≤ ‖x 0-y k‖ := le_of_not_gt (fun h => hx (Metric.mem_ball.mpr h))
    exact radialLocalOrbital_zero (y k) hr (by linarith)

lemma packetInsert_mass {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)))
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖) :
    formMass (packetInsert ψ y r k) = formMass ψ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [packetInsert,formMass_insertOrbital (packetInsert_sobolev hψ y hr k).sobolevVector
      (radialLocalOrbital_admissible (y k) hr).sobolevFermion.sobolevVector
      (packetInsert_disjoint y hr k (hc k (by omega)) (fun i hi => hsep i k hi (by omega)))]
    have hm : formMass (radialLocalOrbital (y k) r) = 1 :=
      (radialLocalOrbital_admissible (y k) hr).2.2.2.2.1
    rw [hm,mul_one]
    exact ih (fun i hi => hc i (by omega)) (fun i j hij hj => hsep i j hij (by omega))

lemma packetInsert_field {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)))
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖)
    (z : Space) (hz : FormAvoids ψ (Metric.ball z (2*r)))
    (hzsep : ∀ i < k, 3*r ≤ ‖y i-z‖) :
    coreCoulombAt (packetInsert ψ y r k) z = coreCoulombAt ψ z +
      formMass ψ * ∑ i ∈ Finset.range k, 1/‖y i-z‖ := by
  induction k with
  | zero => simp [packetInsert]
  | succ k ih =>
    have hck : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)) := fun i hi => hc i (by omega)
    have hsk : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖ := fun i j hij hj => hsep i j hij (by omega)
    have hzsk : ∀ i < k, 3*r ≤ ‖y i-z‖ := fun i hi => hzsep i (by omega)
    have hzk : 3*r ≤ ‖y k-z‖ := hzsep k (by omega)
    have hm : formMass (radialLocalOrbital (y k) r) = 1 :=
      (radialLocalOrbital_admissible (y k) hr).2.2.2.2.1
    rw [packetInsert,coreCoulombAt_insertOrbital
      (packetInsert_sobolev hψ y hr k).sobolevVector
      (radialLocalOrbital_admissible (y k) hr).sobolevFermion.sobolevVector
      (packetInsert_disjoint y hr k (hc k (by omega)) (fun i hi => hsep i k hi (by omega)))
      z (by positivity : 0 < 2*r) (packetInsert_avoids y hr k z hz hzsk)
      (radialLocalOrbital_avoids (y k) z hr (by linarith)),hm,mul_one,
      packetInsert_mass hψ y hr k hck hsk,coreCoulombAt_packet (y k) z hr (by linarith),
      ih hck hsk hzsk,Finset.sum_range_succ]
    ring

def packetPairEnergy (y : ℕ → Space) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range j, 1/‖y i-y j‖

def packetScreenedSum {N : ℕ} (ψ : FormVector N) (Z : ℝ) (y : ℕ → Space) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (Z*formMass ψ/‖y j‖-coreCoulombAt ψ (y j))

lemma packetInsert_energy {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)))
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖)
    (hnuc : ∀ i < k, r < ‖y i‖) (Z : ℝ) :
    formEnergy Z (packetInsert ψ y r k) = formEnergy Z ψ - packetScreenedSum ψ Z y k +
      formMass ψ * ((k:ℝ)*radialPacketKinetic/r^2 + packetPairEnergy y k) := by
  induction k with
  | zero => simp [packetInsert,packetScreenedSum,packetPairEnergy]
  | succ k ih =>
    have hck : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)) := fun i hi => hc i (by omega)
    have hsk : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖ := fun i j hij hj => hsep i j hij (by omega)
    have hnk : ∀ i < k, r < ‖y i‖ := fun i hi => hnuc i (by omega)
    have hsk' : ∀ i < k, 3*r ≤ ‖y i-y k‖ := fun i hi => hsep i k hi (by omega)
    have hT := (packetInsert_sobolev hψ y hr k).sobolevVector
    have hφ := radialLocalOrbital_admissible (y k) hr
    have hm : formMass (radialLocalOrbital (y k) r) = 1 := hφ.2.2.2.2.1
    rw [packetInsert,formEnergy_insertOrbital hT hφ.sobolevFermion.sobolevVector
      (packetInsert_disjoint y hr k (hc k (by omega)) hsk'),formEnergy_tensor_one,hm,mul_one,
      radialLocalOrbital_kinetic _ hr,radialLocalOrbital_nuclear _ hr (hnuc k (by omega)),
      tensorCross_packet hT (y k) hr (by linarith : r < 2*r)
        (packetInsert_avoids y hr k (y k) (hc k (by omega)) hsk'),
      packetInsert_mass hψ y hr k hck hsk,
      packetInsert_field hψ y hr k hck hsk (y k) (hc k (by omega)) hsk',
      ih hck hsk hnk]
    simp only [packetScreenedSum,packetPairEnergy,Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    ring

theorem many_packet_screening {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)))
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖)
    (hnuc : ∀ i < k, r < ‖y i‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    packetScreenedSum ψ Z y k ≤
      (formEnergy Z ψ + lam*N*formMass ψ - priceEnergy (energy Z) lam*formMass ψ) +
      formMass ψ * ((k:ℝ)*(radialPacketKinetic/r^2+lam) + packetPairEnergy y k) := by
  have hh := (packetInsert_sobolev hψ y hr k).priced_lower_bound hZ hlam
  rw [packetInsert_energy hψ y hr k hc hsep hnuc Z,packetInsert_mass hψ y hr k hc hsep,
    Nat.cast_add] at hh
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
