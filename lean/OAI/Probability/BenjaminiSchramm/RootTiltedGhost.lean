import OAI.Probability.BenjaminiSchramm.TiltedGhostSusceptibility

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E ι : Type*} (G : BondGraph V E)
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (root : ι → V)

def rootQuarterMass (z : ι × Set E) : ℝ≥0∞ := G.quarterTiltedMass z.2 (root z.1)

def rootQuarterGhostMagnetization (p : unitInterval) (h : ℝ) : ℝ :=
  Percolation.BenjaminiSchramm.ghostMagnetization (Measure.count.prod (G.law p))
    (fun z => (G.rootQuarterMass root z).toReal) h

def rootQuarterGhostDerivative (p : unitInterval) (h : ℝ) : ℝ :=
  Percolation.BenjaminiSchramm.ghostMagnetizationDerivative (Measure.count.prod (G.law p))
    (fun z => (G.rootQuarterMass root z).toReal) h

lemma measurable_rootQuarterMass [Countable V] [Countable E] :
    Measurable (G.rootQuarterMass root) :=
  measurable_from_prod_countable_right fun i => G.measurable_quarterTiltedMass (root i)

lemma lintegral_rootQuarterMass [Countable V] [Countable E] (p : unitInterval) :
    (∫⁻ z, G.rootQuarterMass root z ∂Measure.count.prod (G.law p)) =
      ∑ i, G.tiltedSusceptibility p (1 / 4) (root i) := by
  rw [lintegral_prod _ (G.measurable_rootQuarterMass root).aemeasurable, lintegral_count,
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact G.lintegral_quarterTiltedMass p (root i)

theorem root_quarterTiltedSusceptibility_lt_top_of_moment_and_differential
    [Countable V] [Countable E] (p : unitInterval)
    (hmoment : ∀ i, (∫⁻ ω, G.quarterTiltedMass ω (root i) ^ (3 / 4 : ℝ) ∂G.law p) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ t, 0 < t → t ≤ 1 →
      G.rootQuarterGhostMagnetization root p (t ^ 4) ≤
        C * G.rootQuarterGhostMagnetization root p (t ^ 4) ^ 2 +
        t ^ 4 * G.rootQuarterGhostDerivative root p (t ^ 4) +
        C * t ^ 6 * G.rootQuarterGhostDerivative root p (t ^ 4)) :
    ∀ i, G.tiltedSusceptibility p (1 / 4) (root i) < ⊤ := by
  let μ : Measure (ι × Set E) := (Measure.count : Measure ι).prod (G.law p)
  have hmeas := G.measurable_rootQuarterMass root
  have hpow : Measurable (fun z => G.rootQuarterMass root z ^ (3 / 4 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp hmeas
  have hmom : (∫⁻ z, G.rootQuarterMass root z ^ (3 / 4 : ℝ) ∂μ) < ⊤ := by
    rw [lintegral_prod _ hpow.aemeasurable, lintegral_count, tsum_fintype]
    exact ENNReal.sum_lt_top.mpr fun i _ => hmoment i
  have hfinite : ∀ᵐ z ∂μ, G.rootQuarterMass root z < ⊤ := by
    filter_upwards [ae_lt_top hpow hmom.ne] with z hz
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 3 / 4)).mp hz
  have hXi : Integrable (fun z => (G.rootQuarterMass root z).toReal ^ (3 / 4 : ℝ)) μ := by
    simpa only [ENNReal.toReal_rpow] using
      integrable_toReal_of_lintegral_ne_top hpow.aemeasurable hmom.ne
  have hfin : (∫⁻ z, G.rootQuarterMass root z ∂μ) < ⊤ := by
    have heq : (fun z => ENNReal.ofReal (G.rootQuarterMass root z).toReal) =ᵐ[μ]
        G.rootQuarterMass root :=
      hfinite.mono fun _ hz => ENNReal.ofReal_toReal hz.ne
    rw [← lintegral_congr_ae heq]
    exact Percolation.BenjaminiSchramm.firstMoment_lt_top_of_threeQuarter_and_differential
      μ (fun z => (G.rootQuarterMass root z).toReal) hmeas.ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) hXi C hC hdiff
  rw [G.lintegral_rootQuarterMass root p] at hfin
  intro i
  exact lt_of_le_of_lt (Finset.single_le_sum
    (f := fun j : ι => G.tiltedSusceptibility p (1 / 4) (root j))
    (fun _ _ => bot_le) (Finset.mem_univ i)) hfin

end CriticalPercolation.BondGraph

end

end OAI
