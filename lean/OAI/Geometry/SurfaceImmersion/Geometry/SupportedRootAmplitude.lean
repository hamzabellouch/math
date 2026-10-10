import OAI.Geometry.SurfaceImmersion.Geometry.NormalizedPerturbedDifference
import OAI.Geometry.Immersion.ClosedSurface.RootMean

namespace OAI

/-! The actual cutoff square-root amplitudes as supported smooth fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates RootMean
open JetPolynomial (SupportedField supportedWeightedSeminorm weightedBound_of_supportedSeminorm
  supportedSeminorm_le_of_weightedBound)

lemma phaseAmplitude_tsupport (ψ u : Base → ℝ) :
    tsupport (phaseAmplitude ψ u) ⊆ tsupport ψ := by
  apply closure_mono
  intro p hp
  by_contra hn
  have hψ : ψ p = 0 := by simpa only [Function.mem_support, not_not] using hn
  exact hp (by simp only [phaseAmplitude, hψ, zero_mul])

def supportedRootAmplitude {U : Set Base} (hU : IsOpen U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (ψ : SupportedField (F := ℝ) K)
    (u : Base → ℝ) (hu : ContDiffOn ℝ ∞ u U) (hpos : ∀ p ∈ U, 0 < u p) :
    SupportedField (F := ℝ) K :=
  let hs := (phaseAmplitude_tsupport ψ u).trans ψ.tsupport_subset
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset hU (hs.trans hKU)
      (contDiffOn_phaseAmplitude ψ.contDiff.contDiffOn hu hpos))
    (subset_closure.trans hs)

theorem supportedRootAmplitude_bounds {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {r R C P : ℝ}
    (hr : 0 < r) (hC : 1 ≤ C) (hP : 0 ≤ P) (m : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (s : ℝ≥0) (ψ : SupportedField (F := ℝ) K)
      (u v : Base → ℝ) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
      (hru : Set.MapsTo u U (Set.Icc r R)) (hrv : Set.MapsTo v U (Set.Icc r R)) (D : ℝ),
      0 < (s : ℝ) → 0 ≤ D → supportedWeightedSeminorm K s m ψ ≤ P →
      WeightedBound U s m C u → WeightedBound U s m C v →
      WeightedBound U s m D (fun p => u p - v p) →
      let bu := supportedRootAmplitude hU K hKU ψ u hu (fun _ hp => hr.trans_le (hru hp).1)
      let bv := supportedRootAmplitude hU K hKU ψ v hv (fun _ hp => hr.trans_le (hrv hp).1)
      supportedWeightedSeminorm K s m bu ≤ A ∧ supportedWeightedSeminorm K s m bv ≤ A ∧
        supportedWeightedSeminorm K s m (bu - bv) ≤ A * D := by
  obtain ⟨A, hA, ha⟩ := compact_amplitude_bounds (R := R) hU.uniqueDiffOn hr hC hP m
  refine ⟨A, hA, ?_⟩
  intro s ψ u v hu hv hru hrv D hs hD hψ hbu hbv hd
  have hψ' := ((weightedBound_of_supportedSeminorm s m ψ).mono_const hψ).restrict_open hU
  obtain ⟨haU, haV, haD⟩ := ha s D ψ u v hs hD ψ.contDiff.contDiffOn hu hv hru hrv hψ' hbu hbv hd
  let bu := supportedRootAmplitude hU K hKU ψ u hu (fun _ hp => hr.trans_le (hru hp).1)
  let bv := supportedRootAmplitude hU K hKU ψ v hv (fun _ hp => hr.trans_le (hrv hp).1)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  refine ⟨?_, ?_, ?_⟩
  · exact supportedSeminorm_le_of_weightedBound hs hA0 bu
      (haU.extend_support hU (bu.tsupport_subset.trans hKU) hA0)
  · exact supportedSeminorm_le_of_weightedBound hs hA0 bv
      (haV.extend_support hU (bv.tsupport_subset.trans hKU) hA0)
  · have hd' : WeightedBound U s m (A * D) (bu - bv) := haD
    exact supportedSeminorm_le_of_weightedBound hs (mul_nonneg hA0 hD) (bu - bv)
      (hd'.extend_support hU ((bu - bv).tsupport_subset.trans hKU) (mul_nonneg hA0 hD))

end ClosedSurfaceR4.RealModes

end

end OAI
