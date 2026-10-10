import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear
import OAI.Geometry.CAT0Fillings.Gradient.Multiplier
import OAI.Geometry.CAT0Fillings.Calculus.ClosedChain

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mulLp_tendsto_smul {b : ℕ → α → ℝ} {c : α → ℝ}
    (hb : ∀ j, AEStronglyMeasurable (b j) μ) (hc : AEStronglyMeasurable c μ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hbC : ∀ j, ∀ᵐ x ∂μ, |b j x| ≤ C) (hcC : ∀ᵐ x ∂μ, |c x| ≤ C)
    (h : Lp E 2 μ)
    (hbc : ∀ᵐ x ∂μ, Tendsto (fun j => b j x • h x) atTop (𝓝 (c x • h x))) :
    Tendsto (fun j => mulLp (hb j) (hbC j) h) atTop (𝓝 (mulLp hc hcC h)) := by
  have hfixed : Tendsto (fun j => mulLp (hb j) (hbC j) h-mulLp hc hcC h) atTop (𝓝 0) := by
    apply l2_tendsto_zero_of_bound _ (fun x => 2*C*‖h x‖)
    · have hi := (Lp.memLp h).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
      convert hi.const_mul ((2*C)^2) using 1
      funext x
      ring
    · intro j
      filter_upwards [Lp.coeFn_sub (mulLp (hb j) (hbC j) h) (mulLp hc hcC h),
        mulLp_ae (hb j) (hbC j) h,mulLp_ae hc hcC h,hbC j,hcC] with x hs hb hc hbC hcC
      rw [hs,Pi.sub_apply,hb,hc,←sub_smul,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((abs_sub (b j x) (c x)).trans (by linarith)) (norm_nonneg _)
    · have hall : ∀ᵐ x ∂μ, ∀ j, (mulLp (hb j) (hbC j) h-mulLp hc hcC h) x =
          (b j x-c x) • h x := by
        apply ae_all_iff.mpr
        intro j
        filter_upwards [Lp.coeFn_sub (mulLp (hb j) (hbC j) h) (mulLp hc hcC h),
          mulLp_ae (hb j) (hbC j) h,mulLp_ae hc hcC h] with x hs hb hc
        rw [hs,Pi.sub_apply,hb,hc,sub_smul]
      filter_upwards [hall,hbc] with x he hx
      simp_rw [he,sub_smul]
      simpa only [sub_self] using hx.sub_const (c x • h x)
  have hf := hfixed.add_const (mulLp hc hcC h)
  simpa only [sub_add_cancel,zero_add] using hf

end CAT0Fillings.ClosedCalculus
namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_chain_uniform_smul {F D : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hD : Measurable D) {C : ℝ} (hC : 0 ≤ C) (hbD : ∀ t, |D t| ≤ C)
    (Fj Dj : ℕ → ℝ → ℝ) (K : ℕ → ℝ≥0)
    (hFj : ∀ j, LipschitzWith (K j) (Fj j))
    (hdj : ∀ j t, HasDerivAt (Fj j) (Dj j t) t)
    (hcj : ∀ j, Continuous (Dj j)) (hbj : ∀ j t, |Dj j t| ≤ C)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (he : ∀ j t, |Fj j t-F t| ≤ a j) (P : q.Sobolev)
    (hdlim : ∀ᵐ w ∂q.atlasMeasure, Tendsto
      (fun j => Dj j ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) atTop
      (𝓝 (D ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w))) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => D ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  choose Q hQ hG using (fun j => q.closed_chain (hFj j) (hdj j) (hcj j) hC (hbj j) P)
  let b (j : ℕ) (w : ℕ × Euc (k+1)) := Dj j ((q.inclusion P) (q.atlasParam w))
  let c (w : ℕ × Euc (k+1)) := D ((q.inclusion P) (q.atlasParam w))
  have hpm := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hb (j : ℕ) : AEStronglyMeasurable (b j) q.atlasMeasure := (hcj j).comp_aestronglyMeasurable hpm
  have hc : AEStronglyMeasurable c q.atlasMeasure := (hD.comp_aemeasurable hpm.aemeasurable).aestronglyMeasurable
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C := Eventually.of_forall fun _ => hbj j _
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C := Eventually.of_forall fun _ => hbD _
  have hgl := ClosedCalculus.mulLp_tendsto_smul hb hc hC hbC hcC (q.closedGradient P) hdlim
  have heG (j : ℕ) : ClosedCalculus.mulLp (hb j) (hbC j) (q.closedGradient P) = q.closedGradient (Q j) := by
    apply Lp.ext
    exact (ClosedCalculus.mulLp_ae (hb j) (hbC j) _).trans (hG j).symm
  simp only [heG] at hgl
  let V := q.composeValue hF (q.inclusion P)
  have hv : Tendsto (fun j => q.inclusion (Q j)) atTop (𝓝 V) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (g := fun j => a j*‖value (hT := hT) (LipschitzWith.const (1:ℝ))‖)
    · intro j
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (q.inclusion (Q j)) V,hQ j,q.composeValue_ae hF (q.inclusion P),
        ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const (1:ℝ))).memLp
          (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x hs hq hv h1
      change (value (hT := hT) (LipschitzWith.const (1:ℝ)) : X → ℝ) x = 1 at h1
      rw [hs,Pi.sub_apply,hq,hv,h1,Real.norm_eq_abs,norm_one,mul_one]
      exact he j _
    · simpa only [zero_mul] using ha.mul_const ‖value (hT := hT) (LipschitzWith.const (1:ℝ))‖
  obtain ⟨R,hR,hRG⟩ := q.closedGradient_closed V (ClosedCalculus.mulLp hc hcC (q.closedGradient P)) Q hv hgl
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hRG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

end OAI
