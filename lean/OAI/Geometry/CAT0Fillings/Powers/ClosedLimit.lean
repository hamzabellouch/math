import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.Multiplier
import OAI.Geometry.CAT0Fillings.Powers.Slope

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E]

lemma memLp_of_ae_tendsto_bounded [InnerProductSpace ℝ E] (f : ℕ → Lp E 2 μ) {g : α → E}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} (hC : ∀ j, ‖f j‖ ≤ C)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x))) : MemLp g 2 μ := by
  refine lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto (C := ENNReal.ofReal C) ?_ (fun j => Lp.aestronglyMeasurable (f j)) hg hl) ENNReal.ofReal_lt_top
  apply Eventually.of_forall
  intro j
  rw [←ENNReal.ofReal_toReal (Lp.memLp (f j)).eLpNorm_ne_top]
  change ENNReal.ofReal ‖f j‖ ≤ ENNReal.ofReal C
  exact ENNReal.ofReal_le_ofReal (hC j)

variable [InnerProductSpace ℝ E]

lemma l2_tendsto_of_domination (f : ℕ → Lp E 2 μ) (g : Lp E 2 μ)
    (b : α → ℝ) (hb : Integrable (fun x => b x^2) μ)
    (hf : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ b x) (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ b x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  have hh : Tendsto (fun j => f j-g) atTop (𝓝 0) := by
    apply l2_tendsto_zero_of_bound _ (fun x => 2*b x)
    · convert hb.const_mul (4:ℝ) using 1
      funext x
      ring
    · intro j
      filter_upwards [Lp.coeFn_sub (f j) g,hf j,hg] with x hs hf hg
      rw [hs,Pi.sub_apply]
      exact (norm_sub_le _ _).trans (by linarith)
    · have ha : ∀ᵐ x ∂μ, ∀ j, (f j-g) x = f j x-g x :=
        ae_all_iff.mpr (fun j => Lp.coeFn_sub (f j) g)
      filter_upwards [ha,hl] with x hx hl
      simp_rw [hx]
      simpa only [sub_self] using hl.sub_const (g x)
  simpa only [sub_add_cancel,zero_add] using hh.add_const g

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_power_of_truncated_bound (P : q.Sobolev) {γ : ℝ} (hγ : 1 < γ)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hv : MemLp (fun x => (q.inclusion P x)^γ) 2 (MassMeasure.currentMassMeasure hT))
    (Q : ℕ → q.Sobolev)
    (hQv : ∀ j, (q.inclusion (Q j) : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => truncatedPower γ ((j:ℝ)+1) (q.inclusion P x)))
    (hQG : ∀ j, (q.closedGradient (Q j) : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope γ ((j:ℝ)+1) (q.inclusion P (q.atlasParam w)) • q.closedGradient P w))
    {B : ℝ} (hB : ∀ j, ‖q.closedGradient (Q j)‖ ≤ B) :
    ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion P x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w) := by
  let g (w : ℕ × Euc (k+1)) := (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w
  have hp : ∀ᵐ w ∂q.atlasMeasure, 0 ≤ q.inclusion P (q.atlasParam w) :=
    q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => 0 ≤ q.inclusion P x) hP
  have hpm := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hgm : AEStronglyMeasurable g q.atlasMeasure :=
    (aestronglyMeasurable_const.mul ((Real.continuous_rpow_const (by linarith : 0 ≤ γ-1)).comp_aestronglyMeasurable hpm)).smul
      (Lp.aestronglyMeasurable (q.closedGradient P))
  have hGl : ∀ᵐ w ∂q.atlasMeasure, Tendsto (fun j => q.closedGradient (Q j) w) atTop (𝓝 (g w)) := by
    filter_upwards [ae_all_iff.mpr hQG] with w hw
    simp_rw [hw]
    exact truncatedPowerSlope_tendsto.smul_const _
  have hg : MemLp g 2 q.atlasMeasure := memLp_of_ae_tendsto_bounded _ hgm hB hGl
  let G := hg.toLp g
  have hGa : (G : _ → _) =ᵐ[q.atlasMeasure] g := hg.coeFn_toLp
  have hGt : Tendsto (fun j => q.closedGradient (Q j)) atTop (𝓝 G) := by
    apply l2_tendsto_of_domination _ G (fun w => ‖g w‖)
      (hg.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
    · intro j
      filter_upwards [hQG j,hp] with w hw hp
      rw [hw,norm_smul,Real.norm_eq_abs,abs_of_nonneg (truncatedPowerSlope_nonneg hγ (by positivity) hp)]
      dsimp [g]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hp _))]
      exact mul_le_mul_of_nonneg_right (truncatedPowerSlope_le hγ (by positivity) hp) (norm_nonneg _)
    · filter_upwards [hGa] with w hw
      rw [hw]
    · filter_upwards [hGa,hGl] with w hw hl
      rw [hw]
      exact hl
  let V := hv.toLp (fun x => (q.inclusion P x)^γ)
  have hVa : (V : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion P x)^γ) := hv.coeFn_toLp
  have hVt : Tendsto (fun j => q.inclusion (Q j)) atTop (𝓝 V) := by
    apply l2_tendsto_of_domination _ V (fun x => (q.inclusion P x)^γ)
    · simpa only [Real.norm_eq_abs,sq_abs] using hv.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
    · intro j
      filter_upwards [hQv j,hP] with x hx hp
      rw [hx,Real.norm_eq_abs,abs_of_nonneg (truncatedPower_nonneg (by positivity))]
      exact truncatedPower_le_power hγ (by positivity) hp
    · filter_upwards [hVa,hP] with x hx hp
      rw [hx,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp _)]
    · filter_upwards [ae_all_iff.mpr hQv,hVa,hP] with x hx hv hp
      simp_rw [hx,hv]
      exact truncatedPower_tendsto hγ hp
  obtain ⟨R,hR,hRG⟩ := q.closedGradient_closed V G Q hVt hGt
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact hVa
  · rw [hRG]
    exact hGa

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_of_ae_domination (Q : ℕ → q.Sobolev) (f : X → ℝ)
    (g : (ℕ × Euc (k+1)) → Euc (k+1))
    (hf : AEStronglyMeasurable f (MassMeasure.currentMassMeasure hT))
    (hg : AEStronglyMeasurable g q.atlasMeasure)
    (b : X → ℝ) (c : (ℕ × Euc (k+1)) → ℝ)
    (hb : MemLp b 2 (MassMeasure.currentMassMeasure hT)) (hc : MemLp c 2 q.atlasMeasure)
    (hfb : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ‖f x‖ ≤ ‖b x‖)
    (hgc : ∀ᵐ w ∂q.atlasMeasure, ‖g w‖ ≤ ‖c w‖)
    (hQb : ∀ j, ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ‖q.inclusion (Q j) x‖ ≤ ‖b x‖)
    (hQc : ∀ j, ∀ᵐ w ∂q.atlasMeasure, ‖q.closedGradient (Q j) w‖ ≤ ‖c w‖)
    (hQf : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT,
      Tendsto (fun j => q.inclusion (Q j) x) atTop (𝓝 (f x)))
    (hQg : ∀ᵐ w ∂q.atlasMeasure,
      Tendsto (fun j => q.closedGradient (Q j) w) atTop (𝓝 (g w))) :
    ∃ R : q.Sobolev, (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] f ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure] g := by
  have hf' := hb.of_le hf hfb
  have hg' := hc.of_le hg hgc
  let V := hf'.toLp f
  let G := hg'.toLp g
  have hv : Tendsto (fun j => q.inclusion (Q j)) atTop (𝓝 V) := by
    apply l2_tendsto_of_domination _ V (fun x => ‖b x‖)
      (hb.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)) hQb
    · filter_upwards [hf'.coeFn_toLp,hfb] with x hx hb
      rw [hx]
      exact hb
    · filter_upwards [hf'.coeFn_toLp,hQf] with x hx hl
      rw [hx]
      exact hl
  have hgT : Tendsto (fun j => q.closedGradient (Q j)) atTop (𝓝 G) := by
    apply l2_tendsto_of_domination _ G (fun w => ‖c w‖)
      (hc.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)) hQc
    · filter_upwards [hg'.coeFn_toLp,hgc] with w hw hc
      rw [hw]
      exact hc
    · filter_upwards [hg'.coeFn_toLp,hQg] with w hw hl
      rw [hw]
      exact hl
  obtain ⟨R,hR,hRG⟩ := q.closedGradient_closed V G Q hv hgT
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact hf'.coeFn_toLp
  · rw [hRG]
    exact hg'.coeFn_toLp
end CAT0Fillings.ChartGeometry
end

end OAI
