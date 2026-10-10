import OAI.Probability.BenjaminiSchramm.TiltedGhost
import OAI.Probability.BenjaminiSchramm.TiltedSusceptibility

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

def quarterTiltedMass (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if (G.openGraph ω).Reachable x y then G.stabilizerWeight x y ^ (1 / 4 : ℝ) else 0

lemma measurable_quarterTiltedMass [Countable V] [Countable E] (x : V) :
    Measurable (fun ω => G.quarterTiltedMass ω x) := by
  apply Measurable.tsum
  intro y
  exact measurable_const.ite (G.measurable_reachable x y).setOf measurable_const

lemma quarterTiltedMass_aut (φ : G.Aut) (ω : Set E) (x : V) :
    G.quarterTiltedMass (φ.edge '' ω) (φ.vertex x) = G.quarterTiltedMass ω x := by
  unfold quarterTiltedMass
  rw [← φ.vertex.tsum_eq]
  apply tsum_congr
  intro y
  rw [Aut.stabilizerWeight]
  congr 1
  exact propext (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω))

lemma quarterTiltedMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (hxy : (G.openGraph ω).Reachable x y) :
    G.quarterTiltedMass ω y =
      G.stabilizerWeight y x ^ (1 / 4 : ℝ) * G.quarterTiltedMass ω x := by
  unfold quarterTiltedMass
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  have hr : (G.openGraph ω).Reachable y z ↔ (G.openGraph ω).Reachable x z :=
    ⟨fun h => hxy.trans h,fun h => hxy.symm.trans h⟩
  rw [hr]
  split_ifs
  · rw [G.stabilizerWeight_change_base hc hl y x z, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  · simp

lemma lintegral_quarterTiltedMass [Countable V] [Countable E] (p : unitInterval) (x : V) :
    (∫⁻ ω, G.quarterTiltedMass ω x ∂G.law p) = G.tiltedSusceptibility p (1 / 4) x := by
  unfold quarterTiltedMass tiltedSusceptibility
  rw [lintegral_tsum]
  · apply tsum_congr
    intro y
    simpa only [Set.indicator, Set.mem_ofPred_eq, connectionMeasure, mul_comm] using
      lintegral_indicator_const (μ := G.law p) (G.measurable_reachable x y).setOf
        (G.stabilizerWeight x y ^ (1 / 4 : ℝ))
  · intro y
    exact (measurable_const.ite (G.measurable_reachable x y).setOf measurable_const).aemeasurable

def quarterGhostMagnetization (p : unitInterval) (x : V) (h : ℝ) : ℝ :=
  Percolation.BenjaminiSchramm.ghostMagnetization (G.law p)
    (fun ω => (G.quarterTiltedMass ω x).toReal) h

def quarterGhostDerivative (p : unitInterval) (x : V) (h : ℝ) : ℝ :=
  Percolation.BenjaminiSchramm.ghostMagnetizationDerivative (G.law p)
    (fun ω => (G.quarterTiltedMass ω x).toReal) h

theorem quarterTiltedSusceptibility_lt_top_of_moment_and_differential
    [Countable V] [Countable E] (p : unitInterval) (x : V)
    (hmoment : (∫⁻ ω, G.quarterTiltedMass ω x ^ (3 / 4 : ℝ) ∂G.law p) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ t, 0 < t → t ≤ 1 →
      G.quarterGhostMagnetization p x (t ^ 4) ≤
        C * G.quarterGhostMagnetization p x (t ^ 4) ^ 2 +
        t ^ 4 * G.quarterGhostDerivative p x (t ^ 4) +
        C * t ^ 6 * G.quarterGhostDerivative p x (t ^ 4)) :
    G.tiltedSusceptibility p (1 / 4) x < ⊤ := by
  have hmeas := G.measurable_quarterTiltedMass x
  have hpow : Measurable (fun ω => G.quarterTiltedMass ω x ^ (3 / 4 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp hmeas
  have hfinite : ∀ᵐ ω ∂G.law p, G.quarterTiltedMass ω x < ⊤ := by
    filter_upwards [ae_lt_top hpow hmoment.ne] with ω hω
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 3 / 4)).mp hω
  have hXi : Integrable (fun ω => (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ))
      (G.law p) := by
    simpa only [ENNReal.toReal_rpow] using
      integrable_toReal_of_lintegral_ne_top hpow.aemeasurable hmoment.ne
  rw [← G.lintegral_quarterTiltedMass p x]
  have heq : (fun ω => ENNReal.ofReal (G.quarterTiltedMass ω x).toReal) =ᵐ[G.law p]
      (fun ω => G.quarterTiltedMass ω x) :=
    hfinite.mono fun _ hω => ENNReal.ofReal_toReal hω.ne
  rw [← lintegral_congr_ae heq]
  exact Percolation.BenjaminiSchramm.firstMoment_lt_top_of_threeQuarter_and_differential
    (G.law p) (fun ω => (G.quarterTiltedMass ω x).toReal) hmeas.ennreal_toReal
    (fun _ => ENNReal.toReal_nonneg) hXi C hC hdiff

end CriticalPercolation.BondGraph

end

end OAI
