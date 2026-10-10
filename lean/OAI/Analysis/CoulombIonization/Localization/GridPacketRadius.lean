import Mathlib
import OAI.Analysis.CoulombIonization.Variational.RotationCoreKernelIntegrable
import OAI.Analysis.CoulombIonization.Localization.PacketCloud

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
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

def gridPacketRadius (B : ℝ) (n : ℕ) : ℝ := B/(20*(n:ℝ))
def packetKineticConstant : ℝ := 400*radialPacketKinetic
def packetRepulsionConstant : ℝ := 128000*packetDensityConstant*unitCoulombIntegral

lemma packetKineticConstant_nonneg : 0 ≤ packetKineticConstant := by
  unfold packetKineticConstant
  exact mul_nonneg (by norm_num) radialPacketKinetic_nonneg

lemma packetRepulsionConstant_nonneg : 0 ≤ packetRepulsionConstant := by
  unfold packetRepulsionConstant
  positivity [packetDensityConstant_pos,unitCoulombIntegral_nonneg]

lemma gridPacketRadius_pos {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) :
    0 < gridPacketRadius B n := div_pos hB (by positivity)

lemma gridPacketRadius_mul {B : ℝ} {n : ℕ} (hn : 0 < n) :
    gridPacketRadius B n * n = B/20 := by
  have hn' : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  unfold gridPacketRadius
  field_simp

lemma gridPacketRadius_le {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) :
    gridPacketRadius B n ≤ B/20 := by
  have hn' : (1:ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hr := gridPacketRadius_pos hB hn
  have he := gridPacketRadius_mul (B := B) hn
  nlinarith

lemma packetGrid_ball {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    ‖packetGrid n (gridPacketRadius B n) i‖ ≤ 9*B/20 := by
  calc
    _ ≤ 9*gridPacketRadius B n*n := packetGrid_norm n (gridPacketRadius_pos hB hn) i
    _ = _ := by rw [mul_assoc,gridPacketRadius_mul hn]; ring

lemma packetGrid_repulsion {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) :
    packetPairEnergy (packetGrid n (gridPacketRadius B n)) (n^3) ≤
      packetRepulsionConstant*(n:ℝ)^6/B := by
  let r := gridPacketRadius B n
  have hr : 0 < r := gridPacketRadius_pos hB hn
  have hrB : r ≤ B := by have := gridPacketRadius_le hB hn; dsimp [r]; linarith
  have hp (i : ℕ) (_hi : i < n^3) : ‖packetGrid n r i‖ ≤ B := by
    have := packetGrid_ball hB hn i
    dsimp only [r]
    linarith
  have hb := packetPairEnergy_bound (packetGrid n r) hr hB.le (n^3)
    (packetGrid_separated n hr) hp
  have hs : (2*B+2*r)^2 ≤ 16*B^2 := by nlinarith
  have hn' : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  calc
    _ ≤ (n^3:ℕ)*(packetDensityConstant/r^3*(2*B+2*r)^2*unitCoulombIntegral) := hb
    _ ≤ (n^3:ℕ)*(packetDensityConstant/r^3*(16*B^2)*unitCoulombIntegral) := by
      gcongr
      exact unitCoulombIntegral_nonneg
      exact div_nonneg packetDensityConstant_pos.le (pow_nonneg hr.le _)
    _ = _ := by
      dsimp [r,gridPacketRadius,packetRepulsionConstant]
      push_cast
      field_simp
      ring

theorem grid_packet_screening {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : B ≤ ‖y‖)
    (hc : FormAvoids ψ (ball y B)) {n : ℕ} (hn : 0 < n)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (n:ℝ)^3*(Z*formMass ψ/‖y‖-coreCoulombAt ψ y-lam*formMass ψ) ≤
      (formEnergy Z ψ + lam*N*formMass ψ-priceEnergy (energy Z) lam*formMass ψ) +
      formMass ψ*(packetKineticConstant*(n:ℝ)^5/B^2+packetRepulsionConstant*(n:ℝ)^6/B) := by
  let r := gridPacketRadius B n
  have hr : 0 < r := gridPacketRadius_pos hB hn
  have hrB : r ≤ B/20 := gridPacketRadius_le hB hn
  have hp (i : ℕ) (_hi : i < n^3) : ‖packetGrid n r i‖+2*r ≤ B := by
    have := packetGrid_ball hB hn i
    dsimp only [r] at *
    linarith
  have hnp (i : ℕ) (_hi : i < n^3) : ‖packetGrid n r i‖+r < ‖y‖ := by
    have := packetGrid_ball hB hn i
    dsimp only [r] at *
    linarith
  have hh := averaged_many_packet_screening hψ y (packetGrid n r) hr (n^3) hc hp
    (packetGrid_separated n hr) hnp hZ hlam
  have hpair := packetGrid_repulsion hB hn
  have hm := formMass_nonneg ψ
  have hh' := mul_le_mul_of_nonneg_left hpair hm
  have he : (n:ℝ)^3*(radialPacketKinetic/r^2) = packetKineticConstant*(n:ℝ)^5/B^2 := by
    dsimp [r,gridPacketRadius,packetKineticConstant]
    field_simp
    ring
  push_cast at hh hh'
  simp only [r] at hh hh' he
  nlinarith

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
