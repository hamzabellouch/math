import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphTree

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace PlanarEndpoint

def BoundedFourierSupport (f : L2) : Prop :=
  ∃ R : ℝ, ∀ᵐ ξ : Plane ∂volume, R < ‖ξ‖ → fourier f ξ = 0

lemma BoundedFourierSupport.integrable {f : L2} (hf : BoundedFourierSupport f) :
    Integrable (fourier f) volume := by
  obtain ⟨R, hR⟩ := hf
  exact fourier_integrable_of_bounded_support hR

lemma BoundedFourierSupport.sub {f g : L2}
    (hf : BoundedFourierSupport f) (hg : BoundedFourierSupport g) :
    BoundedFourierSupport (f - g) := by
  obtain ⟨R, hR⟩ := hf
  obtain ⟨S, hS⟩ := hg
  refine ⟨max R S, ?_⟩
  filter_upwards [hR, hS, fourier_sub_ae f g] with ξ hr hs hsub hξ
  rw [hsub, hr ((le_max_left _ _).trans_lt hξ),
    hs ((le_max_right _ _).trans_lt hξ), sub_self]

lemma inverseCompactFourier_boundedSupport (g : Plane → ℂ) (hc : HasCompactSupport g)
    (hd : ContDiff ℝ ∞ g) :
    BoundedFourierSupport ((inverseCompactFourier g hc hd).toLp 2 volume) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Plane)
  refine ⟨R, ?_⟩
  filter_upwards [fourier_inverseCompactFourier_ae g hc hd] with ξ hξ hnorm
  rw [hξ]
  by_contra hn
  have ht : ξ ∈ tsupport g := subset_closure hn
  have := hR ht
  simp only [Metric.mem_closedBall, dist_zero_right, not_le.mpr hnorm] at this

lemma inHThird_sub {f g : L2} (hf : InHThird f) (hg : InHThird g) :
    InHThird (f - g) := by
  apply inHThird_of_fourier_memLp_sobolev
  have he : fourier (f - g) =ᵐ[sobolevMeasure] (fun ξ => fourier f ξ - fourier g ξ) :=
    (withDensity_absolutelyContinuous _ _).ae_le (fourier_sub_ae f g)
  exact (memLp_congr_ae he).2 ((fourier_memLp_sobolev hf).sub (fourier_memLp_sobolev hg))

lemma hThirdNorm_nonneg (f : L2) : 0 ≤ hThirdNorm f := Real.sqrt_nonneg _

lemma hThirdNorm_sub_le {f g : L2} (hf : InHThird f) (hg : InHThird g) :
    hThirdNorm (f - g) ≤ hThirdNorm f + hThirdNorm g := by
  have he : fourier (f - g) =ᵐ[sobolevMeasure] (fun ξ => fourier f ξ - fourier g ξ) :=
    (withDensity_absolutelyContinuous _ _).ae_le (fourier_sub_ae f g)
  have hfm := fourier_memLp_sobolev hf
  have hgm := fourier_memLp_sobolev hg
  have hle := eLpNorm_sub_le (f := fourier f) (g := fourier g) (μ := sobolevMeasure)
    (show (1 : ENNReal) ≤ 2 by norm_num)
  have hle' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfm.eLpNorm_ne_top,
    hgm.eLpNorm_ne_top⟩) hle
  rw [ENNReal.toReal_add hfm.eLpNorm_ne_top hgm.eLpNorm_ne_top] at hle'
  rw [hThirdNorm_eq_weighted_eLpNorm (inHThird_sub hf hg),
    hThirdNorm_eq_weighted_eLpNorm hf, hThirdNorm_eq_weighted_eLpNorm hg,
    eLpNorm_congr_ae he, ← mul_add]
  exact mul_le_mul_of_nonneg_left hle' (by positivity)

lemma hThirdNorm_sub_comm (f g : L2) : hThirdNorm (f - g) = hThirdNorm (g - f) := by
  unfold hThirdNorm
  congr 2
  apply integral_congr_ae
  filter_upwards [fourier_sub_ae f g, fourier_sub_ae g f] with ξ hfg hgf
  rw [hfg, hgf, norm_sub_rev]

lemma evolution_sub {f g : L2} (hf : Integrable (fourier f) volume)
    (hg : Integrable (fourier g) volume) (x : Plane) (t : ℝ) :
    evolution (f - g) x t = evolution f x t - evolution g x t := by
  have he : (fun ξ => phase x t ξ * fourier (f - g) ξ) =ᵐ[volume]
      (fun ξ => phase x t ξ * fourier f ξ - phase x t ξ * fourier g ξ) := by
    filter_upwards [fourier_sub_ae f g] with ξ hξ
    rw [hξ, mul_sub]
  simp only [evolution]
  rw [integral_congr_ae he, integral_sub (evolution_integrable hf x t)
    (evolution_integrable hg x t), smul_sub]

lemma evolutionPath_sub {f g : L2} (hf : BoundedFourierSupport f)
    (hg : BoundedFourierSupport g) (x : Plane) :
    evolutionPath (f - g) (hf.sub hg).integrable x =
      evolutionPath f hf.integrable x - evolutionPath g hg.integrable x := by
  ext t
  exact evolution_sub hf.integrable hg.integrable x t

lemma exists_schwartz_bounded_hThird_approx {f : L2} (hf : InHThird f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SchwartzMap Plane ℂ, BoundedFourierSupport (φ.toLp 2 volume) ∧ InHThird (φ.toLp 2 volume) ∧
      InHThird (f - φ.toLp 2 volume) ∧ hThirdNorm (f - φ.toLp 2 volume) ≤ ε := by
  have hc : 0 < 2 * Real.pi := by positivity
  obtain ⟨g, hgcompact, hgsmooth, hgap⟩ :=
    exists_smooth_compact_fourier_approx hf (mul_pos hc hε)
  let φ := inverseCompactFourier g hgcompact hgsmooth
  have hφ : fourier (φ.toLp 2 volume) =ᵐ[volume] g :=
    fourier_inverseCompactFourier_ae g hgcompact hgsmooth
  have hφw : fourier (φ.toLp 2 volume) =ᵐ[sobolevMeasure] g :=
    (withDensity_absolutelyContinuous _ _).ae_le hφ
  have hgw : MemLp g 2 sobolevMeasure :=
    hgsmooth.continuous.memLp_of_hasCompactSupport hgcompact
  have hφmem : MemLp (fourier (φ.toLp 2 volume)) 2 sobolevMeasure :=
    (memLp_congr_ae hφw).2 hgw
  have hsub : fourier (f - φ.toLp 2 volume) =ᵐ[volume] fun ξ => fourier f ξ - g ξ := by
    filter_upwards [fourier_sub_ae f (φ.toLp 2 volume), hφ] with ξ hξ hφξ
    rw [hξ, hφξ]
  have hsubw : fourier (f - φ.toLp 2 volume) =ᵐ[sobolevMeasure] fun ξ => fourier f ξ - g ξ :=
    (withDensity_absolutelyContinuous _ _).ae_le hsub
  have hsubmem : MemLp (fourier (f - φ.toLp 2 volume)) 2 sobolevMeasure :=
    (memLp_congr_ae hsubw).2 ((fourier_memLp_sobolev hf).sub hgw)
  have hH := inHThird_of_fourier_memLp_sobolev hsubmem
  refine ⟨φ, inverseCompactFourier_boundedSupport g hgcompact hgsmooth, inHThird_of_fourier_memLp_sobolev hφmem, hH, ?_⟩
  rw [hThirdNorm_eq_weighted_eLpNorm hH, eLpNorm_congr_ae hsubw]
  have hgap' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgap
  rw [ENNReal.toReal_ofReal (mul_pos hc hε).le] at hgap'
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * ε) :=
      mul_le_mul_of_nonneg_left hgap' (inv_nonneg.mpr hc.le)
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

lemma exists_fast_bounded_approximation {f : L2} (hf : InHThird f) :
    ∃ F : ℕ → L2, (∀ n, BoundedFourierSupport (F n)) ∧
      (∀ n, InHThird (F n)) ∧
      (∀ n, hThirdNorm (f - F n) ≤ (1 / 2 : ℝ)^n) ∧
      Tendsto F atTop (𝓝 f) ∧
      Summable (fun n => hThirdNorm (F (n + 1) - F n)) := by
  have hx (n : ℕ) := exists_schwartz_bounded_hThird_approx hf
    (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  choose φ hφb hφh hφsub hφerr using hx
  let F : ℕ → L2 := fun n => (φ n).toLp 2 volume
  have he (n : ℕ) : hThirdNorm (f - F n) ≤ (1 / 2 : ℝ)^n := hφerr n
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hinc (n : ℕ) : hThirdNorm (F (n + 1) - F n) ≤
      (1 / 2 : ℝ)^(n + 1) + (1 / 2 : ℝ)^n := by
    have hineq := hThirdNorm_sub_le (hφsub n) (hφsub (n + 1))
    have hsub : (f - F n) - (f - F (n + 1)) = F (n + 1) - F n := by abel
    change hThirdNorm ((f - F n) - (f - F (n + 1))) ≤ _ at hineq
    rw [hsub] at hineq
    exact hineq.trans (by linarith [he n, he (n + 1)])
  refine ⟨F, hφb, hφh, he, ?_, ?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero (fun _ => norm_nonneg _) ?_
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num))
    intro n
    rw [norm_sub_rev]
    exact (norm_le_hThirdNorm (hφsub n)).trans (he n)
  · exact Summable.of_nonneg_of_le (fun _ => hThirdNorm_nonneg _) hinc
      (((summable_nat_add_iff 1).2 hgeom).add hgeom)

lemma exists_timePath_limit_of_summable (F : ℕ → TimePath)
    (hF : Summable (fun n => ‖F (n + 1) - F n‖)) :
    ∃ g : TimePath, Tendsto F atTop (𝓝 g) := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_summable_dist
  simpa only [dist_eq_norm, norm_sub_rev] using hF

lemma ae_summable_path_increments (F : ℕ → Plane → TimePath)
    (_hF : ∀ n, StronglyMeasurable (F n))
    (hlocal : ∀ k : ℕ, (∑' n, eLpNorm (fun x => F (n + 1) x - F n x) 1
      (volume.restrict (Metric.ball (0 : Plane) (k : ℝ)))) ≠ ⊤) :
    ∀ᵐ x : Plane ∂volume, Summable (fun n => ‖F (n + 1) x - F n x‖) := by
  have hball (k : ℕ) : ∀ᵐ x : Plane ∂volume,
      x ∈ Metric.ball (0 : Plane) (k : ℝ) →
        Summable (fun n => ‖F (n + 1) x - F n x‖) := by
    apply (ae_restrict_iff' measurableSet_ball).1
    exact summable_norm_of_tsum_eLpNorm_ne_top le_rfl (hlocal k)
  filter_upwards [ae_all_iff.2 hball] with x hx
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  exact hx k (by simpa only [Metric.mem_ball, dist_zero_right] using hk)

def pathLimit (F : ℕ → Plane → TimePath) (x : Plane) : TimePath :=
  limUnder atTop (fun n => F n x)

lemma stronglyMeasurable_pathLimit (F : ℕ → Plane → TimePath)
    (hF : ∀ n, StronglyMeasurable (F n)) : StronglyMeasurable (pathLimit F) :=
  StronglyMeasurable.limUnder hF

lemma ae_tendsto_pathLimit_of_local_summable (F : ℕ → Plane → TimePath)
    (hF : ∀ n, StronglyMeasurable (F n))
    (hlocal : ∀ k : ℕ, (∑' n, eLpNorm (fun x => F (n + 1) x - F n x) 1
      (volume.restrict (Metric.ball (0 : Plane) (k : ℝ)))) ≠ ⊤) :
    ∀ᵐ x : Plane ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (pathLimit F x)) := by
  filter_upwards [ae_summable_path_increments F hF hlocal] with x hx
  obtain ⟨g, hg⟩ := exists_timePath_limit_of_summable (fun n => F n x) hx
  simpa only [pathLimit, hg.limUnder_eq] using hg

lemma isometry_l2Evolution (t : ℝ) : Isometry (fun f : L2 => l2Evolution f t) :=
  isometry_iff_dist_eq.2 (fun f g => dist_l2Evolution f g t)

lemma pathLimit_ae_l2Evolution (F : ℕ → L2) (hF : ∀ n, BoundedFourierSupport (F n))
    {f : L2} (hlim : Tendsto F atTop (𝓝 f))
    (hpath : ∀ᵐ x : Plane ∂volume,
      Tendsto (fun n => evolutionPath (F n) (hF n).integrable x) atTop
        (𝓝 (pathLimit (fun n => evolutionPath (F n) (hF n).integrable) x)))
    (t : Time) :
    (fun x => pathLimit (fun n => evolutionPath (F n) (hF n).integrable) x t)
      =ᵐ[volume] (l2Evolution f (t : ℝ) : Plane → ℂ) := by
  have hL2 : Tendsto (fun n => l2Evolution (F n) (t : ℝ)) atTop
      (𝓝 (l2Evolution f (t : ℝ))) :=
    ((isometry_l2Evolution (t : ℝ)).continuous.tendsto f).comp hlim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hid : ∀ᵐ x : Plane ∂volume, ∀ n : ℕ,
      l2Evolution (F n) (t : ℝ) x = evolution (F n) x (t : ℝ) :=
    ae_all_iff.2 (fun n => l2Evolution_ae_evolution (hF n).integrable _)
  filter_upwards [hpath, hae, hid] with x hp hl hi
  have he : Tendsto (fun n => evolution (F n) x (t : ℝ)) atTop
      (𝓝 (pathLimit (fun n => evolutionPath (F n) (hF n).integrable) x t)) :=
    (continuous_eval_const t).continuousAt.tendsto.comp hp
  have he' := he.comp hns.tendsto_atTop
  have hl' : Tendsto (fun n => evolution (F (ns n)) x (t : ℝ))
      atTop (𝓝 (l2Evolution f (t : ℝ) x)) := by
    simpa only [hi] using hl
  exact tendsto_nhds_unique he' hl'

end PlanarEndpoint
end

end OAI
