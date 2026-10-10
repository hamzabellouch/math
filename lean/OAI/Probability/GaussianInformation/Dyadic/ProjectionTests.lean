import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.MixtureBounds

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def weightedProjectionMoment (n k m : ℕ) (B : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(k*(m-1))) *
    (1 + tubeWeightConstant n B * ENNReal.ofReal ((2:ℝ)^(k+1)))^(m-1)

lemma weightedProjectionMoment_ne_top (n k m : ℕ) (B : ℝ) :
    weightedProjectionMoment n k m B ≠ ∞ := by
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.pow_ne_top
  exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (tubeWeightConstant_ne_top _ _) ENNReal.ofReal_ne_top⟩

lemma actual_smoothedProjection_moment {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (hm : 1 < m)
    (hdim : m-2+2*(k+1) ≤ n/2) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    (∫⁻ x, smoothedProjection (k := k) (μ.withDensity (fun z => ENNReal.ofReal |h z|))
      (normalizedChart Q) η x ^ m ∂(gaussianRows k (n+1)).prod volume) ≤
      weightedProjectionMoment n k m B := by
  let ν := μ.withDensity (fun z => ENNReal.ofReal |h z|)
  have hν : ν univ ≤ 1 := weightedMeasure_mass_le_one μ h hh hnorm
  have : IsFiniteMeasure ν := ⟨hν.trans_lt (by simp)⟩
  have he : m-1+1 = m := by omega
  unfold weightedProjectionMoment
  rw [← he]
  have hm1 : m-1+1-1 = m-1 := by omega
  simp only [hm1]
  apply smoothedProjection_moment_le ν hν (normalizedChart Q) (normalizedChart_measurable Q)
    hk (m-2) _ _ (m-1) (by omega) η hη
  intro V hV hd
  exact weighted_affine_inverseMoment_ennreal hn Q μ hsupport hB hspread h hh hnorm V hV k hk
    (by omega)

lemma actual_projection_borel_test {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (hm : 1 < m)
    (hdim : m-2+2*(k+1) ≤ n/2) (Q : Cell n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ]
    (hsupport : μ (cellSet Q)ᶜ = 0) {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (h : Coordinate n → ℝ) (hh : Measurable h) (hnorm : eLpNorm h 2 μ ≤ 1)
    (g : (Fin k → Fin (n+1) → ℝ) × (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    (∫⁻ q, ENNReal.ofReal (g (q.1,projectVector q.1 (normalizedChart Q q.2)))
      ∂(gaussianRows k (n+1)).prod (μ.withDensity (fun z => ENNReal.ofReal |h z|))) ≤
      (weightedProjectionMoment n k m B)^(1/(m:ℝ)) *
        (∫⁻ p, ENNReal.ofReal (g p) ∂(gaussianRows k (n+1)).prod volume)^(1-1/(m:ℝ)) := by
  let ν := μ.withDensity (fun z => ENNReal.ofReal |h z|)
  have hν : ν univ ≤ 1 := weightedMeasure_mass_le_one μ h hh hnorm
  have : IsFiniteMeasure ν := ⟨hν.trans_lt (by simp)⟩
  have : IsProbabilityMeasure (gaussianRows k (n+1)) := by unfold gaussianRows; infer_instance
  have hb : Measurable (fun q : (Fin k → Fin (n+1) → ℝ) × Coordinate n =>
      projectVector q.1 (normalizedChart Q q.2)) :=
    continuous_projectVector.measurable.comp (measurable_fst.prodMk
      ((normalizedChart_measurable Q).comp measurable_snd))
  have : IsLocallyFiniteMeasure ((gaussianRows k (n+1)).prod (volume : Measure (Fin k → ℝ))) :=
    Measure.prod.instIsLocallyFiniteMeasure
  have H := exactMixtureLaw_borel_test (gaussianRows k (n+1)) ν _ hb hm
    (weightedProjectionMoment n k m B) (weightedProjectionMoment_ne_top _ _ _ _)
    (actual_smoothedProjection_moment hn hk hm hdim Q μ hsupport hB hspread h hh hnorm)
    g hg hg0 hg1
  simpa only [exactMixtureLaw, lintegral_map hg.ennreal_ofReal (measurable_fst.prodMk hb)] using H

end RepeatedLocalization

end OAI
