import OAI.NumberTheory.DukePrimeDegree.Geometry.RegularLusinSets
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPairSourceSet
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafClosedRadius
import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereFreeness

namespace OAI

/-!
# The actual sets used for the low-entropy shearing argument

The constants are fixed for this application. The two maximal estimates,
Lusin continuity, small central leaf mass, arithmetic freeness and leaf
regularity are all supplied by proved results. In particular the source
set has positive measure, so the neutral return theorem applies to it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

structure RootPairSelectionData (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (N : Set (X (d + 1))) where
  K : Set (X (d + 1))
  G : Set (X (d + 1))
  H : Set (X (d + 1))
  Z : Set (X (d + 1))
  ρ : ℝ
  rho_pos : 0 < ρ
  rho_small : ρ < 1 / 2
  compact : IsCompact K
  outside : K ⊆ Nᶜ
  continuous : ContinuousOn (intrinsicLeafData hij μ hfree) K
  compact_regular : ∀ x ∈ K, RootLeafRegular hij μ hfree x
  coordinates : ∀ x ∈ K, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0
  good_regular : ∀ x ∈ G, RootLeafRegular hij μ hfree x
  good_returns : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
    intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
      ENNReal.ofReal (1 / 8) * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r)
  small_ball : ∀ x ∈ H, intrinsicRootKernel hij μ hfree x (Metric.closedBall 0 ρ) < 1 / 2
  source_measurable : MeasurableSet Z
  source_positive : μ Z ≠ 0
  source_regular : ∀ z ∈ Z, RootLeafRegular hij μ hfree z
  source_covariance : ∀ z ∈ Z, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree z t
  source_returns : ∀ z ∈ Z, ∀ T : ℝ, 1 ≤ T →
    volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ G}) ≤ (1 / 100) * T ∧
    volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ H}) ≤ (1 / 100) * T

theorem nonempty_rootPairSelectionData
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    Nonempty (RootPairSelectionData d hij μ hfree N) := by
  obtain ⟨L, hbadL, hL, hLzero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp (ae_no_coordinate_zero d μ hA))
  have hcoords (x : X (d + 1)) (hx : x ∉ L) :
      ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0 := by
    by_contra h
    exact hx (hbadL h)
  obtain ⟨K, G, hK, hKN, _, hcont, hKreg, hG, hGsmall, hGreg, hreturn⟩ :=
    exists_regular_lusin_rootLeaf_good_set d hij μ hA hfree
      (N ∪ L) (hN.union hL) (measure_union_null hNzero hLzero)
      (1 / 8) (1 / 10000) (by norm_num) (by norm_num)
  obtain ⟨M, hM, hMzero, hMreg⟩ := exists_rootLeaf_regular_nullset hij μ hfree
  obtain ⟨ρ, hρ, hρsmall, H₀, hH₀, hH₀small, hsmall⟩ :=
    exists_rootLeaf_closedBall_good_set d hij μ hA hnontrivial (1 / 2)
      (ENNReal.ofReal (1 / 10000)) (by norm_num) (by norm_num)
  let H := H₀ \ M
  have hH : MeasurableSet H := hH₀.diff hM
  have hHsmall : μ Hᶜ < ENNReal.ofReal (1 / 10000) := by
    rw [show Hᶜ = M ∪ H₀ᶜ from compl_sdiff]
    have hle : μ (M ∪ H₀ᶜ) ≤ μ H₀ᶜ := by
      simpa only [hMzero, zero_add] using measure_union_le (μ := μ) M H₀ᶜ
    exact hle.trans_lt hH₀small
  have hGreal : μ.real Gᶜ < (1 / 10000 : ℝ) := by
    simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 10000)] using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ Gᶜ) ENNReal.ofReal_ne_top).mpr hGsmall
  have hHreal : μ.real Hᶜ < (1 / 10000 : ℝ) := by
    simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 10000)] using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ Hᶜ) ENNReal.ofReal_ne_top).mpr hHsmall
  have hbudget : ENNReal.ofReal (2 * μ.real Gᶜ / (1 / 100)) +
      ENNReal.ofReal (2 * μ.real Hᶜ / (1 / 100)) < 1 := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_one]
    norm_num [div_eq_mul_inv] at ⊢
    linarith
  obtain ⟨Z, hZ, hZpos, hZM, hZgood⟩ := exists_positive_rootPair_source_set d hij μ hA hfree
    G H M hG hH hM hMzero (1 / 100) (by norm_num) hbudget
  refine ⟨{
    K := K, G := G, H := H, Z := Z, ρ := ρ
    rho_pos := hρ, rho_small := hρsmall
    compact := hK
    outside := fun x hx hn => hKN hx (Or.inl hn)
    continuous := hcont
    compact_regular := hKreg
    coordinates := fun x hx => hcoords x (fun hl => hKN hx (Or.inr hl))
    good_regular := hGreg
    good_returns := hreturn
    small_ball := ?_
    source_measurable := hZ
    source_positive := hZpos
    source_regular := fun z hz => hMreg z (hZM hz)
    source_covariance := fun z hz => (hZgood z hz).1
    source_returns := fun z hz => (hZgood z hz).2
  }⟩
  intro x hx
  rw [(hMreg x hx.2).1]
  exact hsmall x hx.1

end DukePrimeDegree

end

end OAI
