import Mathlib
import OAI.Analysis.CoulombIonization.Variational.RootCoulomb
import OAI.Analysis.CoulombIonization.Variational.CoherentResolution

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoherentHilbert_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff FourierTransform Topology

abbrev OrbitalHilbert := Lp ℂ 2 (volume : Measure Space)

lemma coherentPacket_memLp {g : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g) (z p : Space) :
    MemLp (coherentPacket g z p) 2 := by
  have hc : Continuous (coherentPacket g z p) := by unfold coherentPacket; fun_prop
  exact hc.memLp_of_hasCompactSupport (coherentPacket_compact hcg z p)

def coherentVector {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q : Space × Space) : OrbitalHilbert :=
  (coherentPacket_memLp hg hcg q.1 q.2).toLp _

lemma coherentVector_coe {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q : Space × Space) : coherentVector hg hcg q =ᵐ[volume] coherentPacket g q.1 q.2 :=
  MemLp.coeFn_toLp _

lemma coherentVector_norm_sq {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q : Space × Space) : ‖coherentVector hg hcg q‖^2 = ∫ x : Space, ‖g x‖^2 := by
  rw [lp_norm_sq]
  calc
    _ = ∫ x : Space, ‖coherentPacket g q.1 q.2 x‖^2 :=
      integral_congr_ae ((coherentVector_coe hg hcg q).fun_comp (fun t : ℂ => ‖t‖^2))
    _ = ∫ x : Space, ‖g (x-q.1)‖^2 := by simp only [coherentPacket_norm]
    _ = _ := integral_sub_right_eq_self (fun x : Space => ‖g x‖^2) q.1

lemma coherentVector_inner {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q r : Space × Space) :
    inner ℂ (coherentVector hg hcg q) (coherentVector hg hcg r) =
      coherentOverlap g (coherentPacket g r.1 r.2) q.1 q.2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coherentVector_coe hg hcg q,coherentVector_coe hg hcg r] with x hq hr
  rw [hq,hr]
  simp only [RCLike.inner_apply,mul_comm]

lemma coherentVector_continuous {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    Continuous (coherentVector hg hcg) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have he : (fun q : Space × Space => ‖coherentVector hg hcg q - coherentVector hg hcg r‖) =
      (fun q : Space × Space => Real.sqrt ((∫ x : Space, ‖g x‖^2) - 2 *
      (coherentOverlap g (coherentPacket g r.1 r.2) q.1 q.2).re + (∫ x : Space, ‖g x‖^2))) := by
    funext q
    have hs : (∫ x : Space, ‖g x‖^2) - 2 *
        (coherentOverlap g (coherentPacket g r.1 r.2) q.1 q.2).re + (∫ x : Space, ‖g x‖^2) =
        ‖coherentVector hg hcg q - coherentVector hg hcg r‖^2 := by
      rw [norm_sub_sq (𝕜 := ℂ),coherentVector_norm_sq,coherentVector_norm_sq,coherentVector_inner]
      rfl
    rw [hs,Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  have hu : Continuous (coherentPacket g r.1 r.2) := by unfold coherentPacket; fun_prop
  have hc := coherentOverlap_continuous hg hcg hu (coherentPacket_compact hcg r.1 r.2)
  have hcont : Continuous (fun q : Space × Space => Real.sqrt ((∫ x : Space, ‖g x‖^2) - 2 *
      (coherentOverlap g (coherentPacket g r.1 r.2) q.1 q.2).re + (∫ x : Space, ‖g x‖^2))) :=
    (((continuous_const.sub ((Complex.continuous_re.comp hc).const_mul 2)).add continuous_const).sqrt)
  have hi : (∫ x : Space, ‖g x‖^2) - 2 *
      (coherentOverlap g (coherentPacket g r.1 r.2) r.1 r.2).re + (∫ x : Space, ‖g x‖^2) = 0 := by
    rw [← coherentVector_inner hg hcg r r]
    have hn : (inner ℂ (coherentVector hg hcg r) (coherentVector hg hcg r)).re =
        ∫ x : Space, ‖g x‖^2 := by
      calc
        _ = ‖coherentVector hg hcg r‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
        _ = _ := coherentVector_norm_sq hg hcg r
    rw [hn]
    ring
  simpa only [ContinuousAt,hi,Real.sqrt_zero] using hcont.continuousAt (x := r)

end Work_CoherentHilbert_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

def coherentOperator {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) : OrbitalHilbert →L[ℂ] OrbitalHilbert :=
  (((2*Real.pi)^3)⁻¹ : ℝ) • ∫ q, InnerProductSpace.rankOne ℂ
    (coherentVector hg hcg q) (coherentVector hg hcg q) ∂μ

lemma coherentRankOne_continuous {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) : Continuous (fun q => InnerProductSpace.rankOne ℂ
    (coherentVector hg hcg q) (coherentVector hg hcg q)) := by
  simp only [InnerProductSpace.rankOne_def]
  exact ((ContinuousLinearMap.smulRightL ℂ OrbitalHilbert OrbitalHilbert).continuous.comp
    ((innerSL ℂ).continuous.comp (coherentVector_continuous hg hcg))).clm_apply
      (coherentVector_continuous hg hcg)

lemma coherentRankOne_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Integrable (fun q => InnerProductSpace.rankOne ℂ
      (coherentVector hg hcg q) (coherentVector hg hcg q)) μ := by
  apply Integrable.of_bound (coherentRankOne_continuous hg hcg).aestronglyMeasurable
    (∫ x : Space, ‖g x‖^2)
  filter_upwards [] with q
  rw [InnerProductSpace.norm_rankOne,← pow_two,coherentVector_norm_sq]

lemma inner_integral_rankOne {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    (μ : Measure α) (v : α → H)
    (hi : Integrable (fun q => InnerProductSpace.rankOne ℂ (v q) (v q)) μ) (u : H) :
    inner ℂ u ((∫ q, InnerProductSpace.rankOne ℂ (v q) (v q) ∂μ) u) =
      (∫ q, ‖inner ℂ (v q) u‖^2 ∂μ : ℝ) := by
  rw [ContinuousLinearMap.integral_apply hi]
  have ha : Integrable (fun q => InnerProductSpace.rankOne ℂ (v q) (v q) u) μ :=
    (ContinuousLinearMap.apply ℂ H u).integrable_comp hi
  rw [← integral_inner (𝕜 := ℂ) ha u]
  have he (q : α) : inner ℂ u (InnerProductSpace.rankOne ℂ (v q) (v q) u) =
      (‖inner ℂ (v q) u‖^2 : ℝ) := by
    rw [InnerProductSpace.rankOne_apply,inner_smul_right,
      ← inner_conj_symm u (v q),RCLike.mul_conj,Complex.ofReal_pow]
    rfl
  simp_rw [he]
  exact integral_ofReal

lemma coherentOperator_inner {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (u : OrbitalHilbert) :
    inner ℂ u (coherentOperator hg hcg μ u) =
      (((2*Real.pi)^3)⁻¹ * ∫ q, ‖inner ℂ (coherentVector hg hcg q) u‖^2 ∂μ : ℝ) := by
  change inner ℂ u ((((2*Real.pi)^3)⁻¹ : ℝ) • ((∫ q,
    InnerProductSpace.rankOne ℂ (coherentVector hg hcg q) (coherentVector hg hcg q) ∂μ) u)) = _
  rw [inner_smul_right_eq_smul,inner_integral_rankOne μ _ (coherentRankOne_integrable hg hcg μ),
    Complex.real_smul,Complex.ofReal_mul]

lemma coherentOperator_inner_left {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (u : OrbitalHilbert) :
    inner ℂ (coherentOperator hg hcg μ u) u =
      (((2*Real.pi)^3)⁻¹ * ∫ q, ‖inner ℂ (coherentVector hg hcg q) u‖^2 ∂μ : ℝ) := by
  rw [← inner_conj_symm (coherentOperator hg hcg μ u) u,coherentOperator_inner]
  exact Complex.conj_ofReal _

lemma coherentOperator_positive {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    (coherentOperator hg hcg μ).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro u
  rw [coherentOperator_inner_left]
  simp only [RCLike.re_to_complex,Complex.ofReal_re]
  exact ⟨trivial,mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))⟩

lemma coherentOperator_compact {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    IsCompactOperator (coherentOperator hg hcg μ) := by
  let K := (compactOperator (RingHom.id ℂ) OrbitalHilbert OrbitalHilbert).restrictScalars ℝ
  have hm (q : Space × Space) : InnerProductSpace.rankOne ℂ
      (coherentVector hg hcg q) (coherentVector hg hcg q) ∈ K := by
    change IsCompactOperator (InnerProductSpace.rankOne ℂ _ _)
    rw [InnerProductSpace.rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ _)).comp_clm _
  by_cases hμ : μ = 0
  · subst μ
    simp [coherentOperator,isCompactOperator_zero]
  let : NeZero μ := ⟨hμ⟩
  have hclosed : IsClosed (K : Set (OrbitalHilbert →L[ℂ] OrbitalHilbert)) := by
    change IsClosed { f : OrbitalHilbert →L[ℂ] OrbitalHilbert | IsCompactOperator f }
    exact isClosed_setOfPred_isCompactOperator
  have ha : (⨍ q, InnerProductSpace.rankOne ℂ (coherentVector hg hcg q)
      (coherentVector hg hcg q) ∂μ) ∈ K :=
    K.convex.average_mem hclosed (Eventually.of_forall hm)
      (coherentRankOne_integrable hg hcg μ)
  have hb := K.smul_mem (μ.real Set.univ) ha
  rw [measure_smul_average] at hb
  exact K.smul_mem (((2*Real.pi)^3)⁻¹ : ℝ) hb

end CoulombAtom

end

end OAI
