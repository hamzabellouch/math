import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoherentHilbert

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoherentSchwartz_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

lemma coherentOverlap_continuous_schwartz {g : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) :
    Continuous (fun q : Space × Space => coherentOverlap g u q.1 q.2) := by
  obtain ⟨C,hC⟩ := hg.norm.exists_forall_ge_of_hasCompactSupport hcg.norm
  apply continuous_of_dominated (bound := fun x => ‖g C‖ * ‖u x‖)
  · intro q
    unfold coherentPacket
    have hu := u.continuous
    fun_prop
  · intro q
    filter_upwards [] with x
    rw [norm_mul,Complex.norm_conj,coherentPacket_norm]
    exact mul_le_mul_of_nonneg_right (hC (x-q.1)) (norm_nonneg _)
  · exact u.integrable.norm.const_mul ‖g C‖
  · filter_upwards [] with x
    unfold coherentPacket
    fun_prop

lemma coherentWindow_compact {g u : Space → ℂ} (hcg : HasCompactSupport g) (z : Space) :
    HasCompactSupport (fun x : Space => conj (g (x-z))*u x) := by
  have hct : HasCompactSupport (fun x : Space => g (x-z)) :=
    hcg.comp_homeomorph (Homeomorph.subRight z)
  have hcj : HasCompactSupport (fun x : Space => conj (g (x-z))) :=
    hct.comp_left (map_zero (starRingEnd ℂ))
  exact hcj.mul_right

lemma coherentOverlap_momentum_schwartz {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) (z : Space) :
    ((2*Real.pi)^3)⁻¹ * (∫ p : Space, ‖coherentOverlap g u z p‖^2) =
      ∫ x : Space, ‖g (x-z)‖^2 * ‖u x‖^2 := by
  have hc := coherentWindow_compact (u := u) hcg z
  have hd : ContDiff ℝ ∞ (fun x : Space => conj (g (x-z))*u x) :=
    (Complex.conjCLE.contDiff.comp (hg.comp (contDiff_id.sub contDiff_const))).mul (u.smooth ⊤)
  have hp := SchwartzMap.integral_norm_sq_fourier (hc.toSchwartzMap hd)
  change (∫ ξ : Space, ‖𝓕 (fun x : Space => conj (g (x-z))*u x) ξ‖^2) =
    ∫ x : Space, ‖conj (g (x-z))*u x‖^2 at hp
  simp_rw [← coherentOverlap_fourier,norm_mul,Complex.norm_conj,mul_pow] at hp
  rw [Measure.integral_comp_smul_of_nonneg volume (fun p : Space => ‖coherentOverlap g u z p‖^2)
    (2*Real.pi) (hR := by positivity),space_finrank] at hp
  simpa only [zpow_neg,zpow_natCast,smul_eq_mul] using hp

lemma coherentOverlap_momentum_integrable_schwartz {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) (z : Space) :
    Integrable (fun p : Space => ‖coherentOverlap g u z p‖^2) := by
  rw [← integrable_comp_smul_iff volume (fun p : Space => ‖coherentOverlap g u z p‖^2)
    (show 2*Real.pi ≠ 0 by positivity)]
  simp_rw [coherentOverlap_fourier]
  have hc := coherentWindow_compact (u := u) hcg z
  have hd : ContDiff ℝ ∞ (fun x : Space => conj (g (x-z))*u x) :=
    (Complex.conjCLE.contDiff.comp (hg.comp (contDiff_id.sub contDiff_const))).mul (u.smooth ⊤)
  have hi := ((𝓕 (hc.toSchwartzMap hd)).memLp 2 volume).norm.integrable_sq
  change Integrable (fun x : Space => ‖𝓕 (fun x : Space => conj (g (x-z))*u x) x‖^2) at hi
  exact hi

lemma coherent_position_integrable_schwartz {g : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) :
    Integrable (fun q : Space × Space => ‖g (q.2-q.1)‖^2 * ‖u q.2‖^2) := by
  have hgs : Integrable (fun z : Space => ‖g z‖^2) :=
    (hg.memLp_of_hasCompactSupport hcg (p := 2)).norm.integrable_sq
  have hus : Integrable (fun z : Space => ‖u z‖^2) := (u.memLp 2 volume).norm.integrable_sq
  have hu := u.continuous
  apply (integrable_prod_iff' (by fun_prop)).mpr
  constructor
  · filter_upwards [] with x
    exact (hgs.comp_sub_left x).mul_const _
  · have he (x : Space) :
        (∫ z : Space, ‖‖g (x-z)‖^2 * ‖u x‖^2‖) = (∫ z : Space, ‖g z‖^2) * ‖u x‖^2 := by
      simp_rw [norm_mul,norm_pow,Real.norm_of_nonneg (norm_nonneg _)]
      rw [integral_mul_const,integral_sub_left_eq_self (fun t : Space => ‖g t‖^2) volume x]
    change Integrable (fun x : Space => ∫ z : Space, ‖‖g (x-z)‖^2 * ‖u x‖^2‖)
    simp_rw [he]
    exact hus.const_mul _

lemma coherentOverlap_integrable_schwartz {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) :
    Integrable (fun q : Space × Space => ‖coherentOverlap g u q.1 q.2‖^2) := by
  apply (integrable_prod_iff ((coherentOverlap_continuous_schwartz hg.continuous hcg u).norm.pow 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (coherentOverlap_momentum_integrable_schwartz hg hcg u)
  · have he (z : Space) : (∫ p : Space, ‖‖coherentOverlap g u z p‖^2‖) =
        (2*Real.pi)^3 * (∫ x : Space, ‖g (x-z)‖^2 * ‖u x‖^2) := by
      simp_rw [norm_pow,Real.norm_of_nonneg (norm_nonneg _)]
      have h := coherentOverlap_momentum_schwartz hg hcg u z
      have hn : (2*Real.pi)^3 ≠ 0 := by positivity
      calc
        _ = (2*Real.pi)^3 * (((2*Real.pi)^3)⁻¹ * _) := by field_simp
        _ = _ := by rw [h]
    change Integrable (fun z : Space => ∫ p : Space, ‖‖coherentOverlap g u z p‖^2‖)
    simp_rw [he]
    exact (coherent_position_integrable_schwartz hg.continuous hcg u).integral_prod_left.const_mul _

lemma coherentOverlap_resolution_schwartz {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) :
    ((2*Real.pi)^3)⁻¹ * (∫ q : Space × Space, ‖coherentOverlap g u q.1 q.2‖^2) =
      (∫ z : Space, ‖g z‖^2) * (∫ x : Space, ‖u x‖^2) := by
  change ((2*Real.pi)^3)⁻¹ * (∫ q : Space × Space, ‖coherentOverlap g u q.1 q.2‖^2 ∂volume.prod volume) = _
  rw [integral_prod _ (coherentOverlap_integrable_schwartz hg hcg u),← integral_const_mul]
  simp_rw [coherentOverlap_momentum_schwartz hg hcg u]
  rw [integral_integral_swap (coherent_position_integrable_schwartz hg.continuous hcg u)]
  simp_rw [integral_mul_const,integral_sub_left_eq_self (fun t : Space => ‖g t‖^2) volume]
  rw [integral_const_mul]

end Work_CoherentSchwartz_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

lemma coherentVector_inner_schwartz {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (q : Space × Space) (u : SchwartzMap Space ℂ) :
    inner ℂ (coherentVector hg hcg q) (u.toLp 2) = coherentOverlap g u q.1 q.2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coherentVector_coe hg hcg q,u.coeFn_toLp 2 volume] with x hq hu
  rw [hq,hu]
  simp only [RCLike.inner_apply,mul_comm]

lemma schwartz_toLp_norm_sq (u : SchwartzMap Space ℂ) :
    ‖u.toLp 2‖^2 = ∫ x : Space, ‖u x‖^2 := by
  rw [lp_norm_sq]
  exact integral_congr_ae ((u.coeFn_toLp 2 volume).fun_comp (fun t : ℂ => ‖t‖^2))

lemma coherentOverlap_measure_le_schwartz {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) (hμ : μ ≤ volume) (v : SchwartzMap Space ℂ) :
    ((2*Real.pi)^3)⁻¹ * (∫ q, ‖coherentOverlap g v q.1 q.2‖^2 ∂μ) ≤ ∫ x : Space, ‖v x‖^2 := by
  have hi : Integrable (fun q : Space × Space => ‖coherentOverlap g v q.1 q.2‖^2) :=
    coherentOverlap_integrable_schwartz hg hcg v
  have hl : (∫ q, ‖coherentOverlap g v q.1 q.2‖^2 ∂μ) ≤
      ∫ q : Space × Space, ‖coherentOverlap g v q.1 q.2‖^2 :=
    integral_mono_measure hμ (Eventually.of_forall (fun q => sq_nonneg _)) hi
  calc
    _ ≤ ((2*Real.pi)^3)⁻¹ * (∫ q : Space × Space, ‖coherentOverlap g v q.1 q.2‖^2) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by rw [coherentOverlap_resolution_schwartz hg hcg v,hgn,one_mul]

lemma coherentOperator_schwartz_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume)
    (v : SchwartzMap Space ℂ) :
    (inner ℂ (v.toLp 2) (coherentOperator hg.continuous hcg μ (v.toLp 2))).re ≤ ‖v.toLp 2‖^2 := by
  rw [coherentOperator_inner,Complex.ofReal_re,schwartz_toLp_norm_sq]
  simp_rw [coherentVector_inner_schwartz]
  exact coherentOverlap_measure_le_schwartz hg hcg hgn μ hμ v

lemma coherentOperator_quadratic_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume)
    (u : OrbitalHilbert) :
    (inner ℂ u (coherentOperator hg.continuous hcg μ u)).re ≤ ‖u‖^2 := by
  refine (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (μ := (volume : Measure Space))
    ENNReal.ofNat_ne_top).induction_on u ?_ ?_
  · apply isClosed_le
    · exact Complex.continuous_re.comp (continuous_id.inner
        (coherentOperator hg.continuous hcg μ).continuous)
    · exact continuous_id.norm.pow 2
  · intro v
    exact coherentOperator_schwartz_le hg hcg hgn μ hμ v

lemma coherentOperator_one_sub_positive {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume) :
    (1 - coherentOperator hg.continuous hcg μ).IsPositive := by
  refine ⟨(ContinuousLinearMap.isPositive_one (𝕜 := ℂ) (E := OrbitalHilbert)).isSymmetric.sub
    (coherentOperator_positive hg.continuous hcg μ).isSymmetric, ?_⟩
  intro u
  change 0 ≤ (inner ℂ ((1-coherentOperator hg.continuous hcg μ) u) u).re
  rw [sub_apply,one_apply_eq_self,inner_sub_left]
  change 0 ≤ RCLike.re (inner ℂ u u) - RCLike.re (inner ℂ (coherentOperator hg.continuous hcg μ u) u)
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [inner_re_symm (coherentOperator hg.continuous hcg μ u) u]
  exact sub_nonneg.mpr (coherentOperator_quadratic_le hg hcg hgn μ hμ u)

end CoulombAtom

end

end OAI
