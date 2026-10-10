import OAI.Analysis.PlanarEndpoint.Extension
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.Representative

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
namespace PlanarEndpoint

def LocalMaximalBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : L2) (hb : BoundedFourierSupport f), InHThird f →
    ∀ x : Plane, ∫ y in ball x 1, ‖evolutionPath f hb.integrable y‖ ≤ C * hThirdNorm f

lemma integrableOn_evolutionPath_ball (f : L2) (hf : Integrable (fourier f) volume)
    (x : Plane) : IntegrableOn (evolutionPath f hf) (ball x 1) volume :=
  ((continuous_evolutionPath f hf).locallyIntegrable.integrableOn_isCompact
    (isCompact_closedBall x 1)).mono_set ball_subset_closedBall

lemma hThirdNorm_approx_le {f g : L2} (hf : InHThird f) (hg : InHThird g) :
    hThirdNorm g ≤ hThirdNorm f + hThirdNorm (f-g) := by
  have h := hThirdNorm_sub_le hf (inHThird_sub hf hg)
  simpa only [sub_sub_cancel] using h

lemma ae_summable_paths_of_unit_ball (F : ℕ → Plane → TimePath)
    (_hF : ∀ n, StronglyMeasurable (F n))
    (hb : ∀ x : Plane, (∑' n, eLpNorm (fun y => F (n+1) y - F n y) 1
      (volume.restrict (ball x 1))) ≠ ⊤) :
    ∀ᵐ x : Plane ∂volume, Summable (fun n => ‖F (n+1) x-F n x‖) := by
  obtain ⟨D, hc, hd⟩ := TopologicalSpace.exists_countable_dense Plane
  have hu := (dense_iff_iUnion_ball D).1 hd 1 (by norm_num)
  have hh : ∀ᵐ x ∂volume.restrict (⋃ c ∈ D, ball c 1),
      Summable (fun n => ‖F (n+1) x-F n x‖) := by
    apply (ae_restrict_biUnion_iff _ hc _).2
    intro c _
    exact summable_norm_of_tsum_eLpNorm_ne_top le_rfl (hb c)
  simpa only [hu, Measure.restrict_univ] using hh

lemma paths_tsum_finite_of_maximal {C : ℝ} (_hC : 0 < C)
    (hmax : ∀ (f : L2) (hb : BoundedFourierSupport f), InHThird f →
      ∀ x : Plane, ∫ y in ball x 1, ‖evolutionPath f hb.integrable y‖ ≤ C * hThirdNorm f)
    (F : ℕ → L2) (hb : ∀ n, BoundedFourierSupport (F n)) (hH : ∀ n, InHThird (F n))
    (hs : Summable (fun n => hThirdNorm (F (n+1)-F n))) (x : Plane) :
    (∑' n, eLpNorm (fun y => evolutionPath (F (n+1)) (hb (n+1)).integrable y -
      evolutionPath (F n) (hb n).integrable y) 1 (volume.restrict (ball x 1))) ≠ ⊤ := by
  have hle (n : ℕ) : eLpNorm (fun y => evolutionPath (F (n+1)) (hb (n+1)).integrable y -
      evolutionPath (F n) (hb n).integrable y) 1 (volume.restrict (ball x 1)) ≤
      ENNReal.ofReal (C * hThirdNorm (F (n+1)-F n)) := by
    have hbn := (hb (n+1)).sub (hb n)
    have he : (fun y => evolutionPath (F (n+1)) (hb (n+1)).integrable y -
        evolutionPath (F n) (hb n).integrable y) = evolutionPath (F (n+1)-F n) hbn.integrable := by
      funext y
      exact (evolutionPath_sub (hb (n+1)) (hb n) y).symm
    rw [he, eLpNorm_one_eq_lintegral_enorm
      (integrableOn_evolutionPath_ball _ _ x).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_evolutionPath_ball _ _ x)]
    exact ENNReal.ofReal_le_ofReal (hmax _ hbn (inHThird_sub (hH _) (hH _)) x)
  exact ne_of_lt ((ENNReal.tsum_le_tsum hle).trans_lt (hs.mul_left C).tsum_ofReal_lt_top)

lemma pathLimit_integrable_of_uniform_bounds (F : ℕ → Plane → TimePath)
    (hF : ∀ n, Continuous (F n)) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ (n : ℕ) (x : Plane), ∫ y in ball x 1, ‖F n y‖ ≤ A)
    (hl : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (pathLimit F x))) :
    LocallyIntegrable (pathLimit F) volume ∧
      ∀ x : Plane, ∫ y in ball x 1, ‖pathLimit F y‖ ≤ A := by
  have hm := stronglyMeasurable_pathLimit F (fun n => (hF n).stronglyMeasurable)
  have hbound (x : Plane) : eLpNorm (pathLimit F) 1 (volume.restrict (ball x 1)) ≤
      ENNReal.ofReal A := by
    apply Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall ?_)
      (fun n => (hF n).aestronglyMeasurable) hm.aestronglyMeasurable (ae_restrict_of_ae hl)
    intro n
    have hi : IntegrableOn (F n) (ball x 1) volume :=
      ((hF n).locallyIntegrable.integrableOn_isCompact
        (isCompact_closedBall x 1)).mono_set ball_subset_closedBall
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    exact ENNReal.ofReal_le_ofReal (hb n x)
  have hi (x : Plane) : IntegrableOn (pathLimit F) (ball x 1) volume :=
    memLp_one_iff_integrable.1 ((hbound x).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num), hi x⟩, ?_⟩
  intro x
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound x)
  rw [ENNReal.toReal_ofReal hA, eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hm.aestronglyMeasurable] at hb'
  exact hb'

lemma mainConclusion_of_localMaximalBound (hmax : LocalMaximalBound)
    {f : L2} (hf : InHThird f) : MainConclusion f := by
  obtain ⟨C, hC, hmax⟩ := hmax
  obtain ⟨F, hb, hH, herr, hlim, hs⟩ := exists_fast_bounded_approximation hf
  let P : ℕ → Plane → TimePath := fun n => evolutionPath (F n) (hb n).integrable
  have hP (n : ℕ) : Continuous (P n) := continuous_evolutionPath _ _
  have hsum := ae_summable_paths_of_unit_ball P (fun n => (hP n).stronglyMeasurable)
    (paths_tsum_finite_of_maximal hC hmax F hb hH hs)
  have hp : ∀ᵐ x ∂volume, Tendsto (fun n => P n x) atTop (𝓝 (pathLimit P x)) := by
    filter_upwards [hsum] with x hx
    obtain ⟨g, hg⟩ := exists_timePath_limit_of_summable (fun n => P n x) hx
    simpa only [pathLimit, hg.limUnder_eq] using hg
  let A : ℝ≥0 := ⟨C * (hThirdNorm f+1), mul_nonneg hC.le (add_nonneg (hThirdNorm_nonneg f) (by norm_num))⟩
  have hbound (n : ℕ) (x : Plane) : ∫ y in ball x 1, ‖P n y‖ ≤ A := by
    apply (hmax (F n) (hb n) (hH n) x).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hn : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (hThirdNorm_approx_le hf (hH n)).trans (add_le_add_right ((herr n).trans hn) _)
  have hpath := pathLimit_integrable_of_uniform_bounds P hP A A.coe_nonneg hbound hp
  exact mainConclusion_of_integrable_paths f (pathLimit P) hpath.1 A hpath.2
    (pathLimit_ae_l2Evolution F hb hlim hp)

end PlanarEndpoint
end

end OAI
