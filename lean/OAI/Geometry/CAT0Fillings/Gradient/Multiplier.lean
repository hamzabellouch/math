import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.Chart
import OAI.Geometry.CAT0Fillings.Gradient.HilbertAtlas
import OAI.Geometry.CAT0Fillings.Tangent.Coordinates

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradientFunction_chain {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) :
    q.gradientFunction (F ∘ u) =ᵐ[q.atlasMeasure]
      (fun w => F' (u (q.atlasParam w)) • q.gradientFunction u w) := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  let C := q.chart i
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨f,hf,hef⟩ := (C.scalar_lipschitzOn hL hu).extend_real
  have hecomp : EqOn (C.scalar (F ∘ u)) (F ∘ f) C.domain := by
    intro z hz
    simp only [IntegerChart.scalar,dite_eq_left hz,Function.comp_apply]
    rw [←hef hz]
    simp only [IntegerChart.scalar,dite_eq_left hz]
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hf hef,
    ae_fderivWithin_eq_fderiv_extension volume C.borel (hF.comp hf) hecomp,
    hf.ae_differentiableAt.filter_mono ae_restrict_le,ae_restrict_mem C.borel] with z hu hcomp hdz hz
  change z ∈ C.domain at hz
  change q.normalizedCovector i (F ∘ u) z =
    F' (u (C.paramExtended z)) • q.normalizedCovector i u z
  have hname : f z = u (C.paramExtended z) := by
    rw [←hef hz]
    simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz]
  have hd := (hdF (f z)).comp_hasFDerivAt z hdz.hasFDerivAt
  dsimp only [normalizedCovector,covector]
  rw [hcomp,hd.fderiv,hu,hname]
  have he : differentialRow (F' (u (C.paramExtended z)) • fderiv ℝ f z) =
      F' (u (C.paramExtended z)) • differentialRow (fderiv ℝ f z) := rfl
  rw [he,Matrix.mulVec_smul,WithLp.toLp_smul]

lemma gradient_chain_ae {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) :
    q.gradient (hF.comp hu) =ᵐ[q.atlasMeasure]
      (fun w => F' (u (q.atlasParam w)) • q.gradient hu w) := by
  filter_upwards [(q.memLp_gradientFunction (hF.comp hu)).coeFn_toLp,
    (q.memLp_gradientFunction hu).coeFn_toLp,q.gradientFunction_chain hu hF hdF] with w h1 h2 h3
  exact h1.trans (h3.trans (congrArg (F' (u (q.atlasParam w)) • ·) h2.symm))

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma l2_norm_sq (g : Lp E 2 μ) : ‖g‖^2 = ∫ x, ‖g x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma l2_tendsto_zero_of_bound (f : ℕ → Lp E 2 μ) (g : α → ℝ)
    (hg : Integrable (fun x => (g x)^2) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ g x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hh : Tendsto (fun j => ∫ x, ‖f j x‖^2 ∂μ) atTop (𝓝 (∫ _ : α, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => g x^2)
      (fun j => (Lp.aestronglyMeasurable (f j)).norm.pow 2) hg
    · intro j
      filter_upwards [hb j] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hx)).mpr hx
    · filter_upwards [hl] with x hx
      simpa only [Pi.pow_apply,norm_zero,zero_pow (by decide : 2 ≠ 0)] using hx.norm.pow 2
  simp only [integral_zero,←l2_norm_sq] at hh
  have hn := hh.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

lemma memLp_smul_bounded {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g : Lp E 2 μ) :
    MemLp (fun x => b x • g x) 2 μ := by
  apply (Lp.memLp g).of_le_mul (c := C) (hb.smul (Lp.aestronglyMeasurable g))
  filter_upwards [hC] with x hx
  change ‖b x • g x‖ ≤ C*‖g x‖
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

noncomputable def mulLp {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g : Lp E 2 μ) : Lp E 2 μ :=
  (memLp_smul_bounded hb hC g).toLp _

lemma mulLp_ae {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g : Lp E 2 μ) :
    mulLp hb hC g =ᵐ[μ] (fun x => b x • g x) := (memLp_smul_bounded hb hC g).coeFn_toLp

lemma mulLp_sub_bound {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g h : Lp E 2 μ) :
    ‖mulLp hb hC g-mulLp hb hC h‖ ≤ C*‖g-h‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (mulLp hb hC g) (mulLp hb hC h),mulLp_ae hb hC g,
    mulLp_ae hb hC h,Lp.coeFn_sub g h,hC] with x hs hg hh hd hCx
  rw [hs,hd,Pi.sub_apply,hg,hh,←smul_sub,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hCx (norm_nonneg _)

lemma mulLp_tendsto {b : ℕ → α → ℝ} {c : α → ℝ}
    (hb : ∀ j, AEStronglyMeasurable (b j) μ) (hc : AEStronglyMeasurable c μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ j, ∀ᵐ x ∂μ, |b j x| ≤ C) (hcC : ∀ᵐ x ∂μ, |c x| ≤ C)
    (hbc : ∀ᵐ x ∂μ, Tendsto (fun j => b j x) atTop (𝓝 (c x)))
    {g : ℕ → Lp E 2 μ} {h : Lp E 2 μ} (hgh : Tendsto g atTop (𝓝 h)) :
    Tendsto (fun j => mulLp (hb j) (hbC j) (g j)) atTop (𝓝 (mulLp hc hcC h)) := by
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
      simp_rw [he]
      simpa only [sub_self,zero_smul] using (hx.sub_const (c x)).smul_const (h x)
  have hpert : Tendsto (fun j => mulLp (hb j) (hbC j) (g j)-mulLp (hb j) (hbC j) h)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun j => mulLp_sub_bound (hb j) (hbC j) (g j) h)
    simpa only [Real.norm_of_nonneg hC,sub_self,norm_zero,mul_zero] using
      ((hgh.sub_const h).norm).const_mul ‖C‖
  have hh := hpert.add hfixed
  simp only [sub_add_sub_cancel,add_zero] at hh
  have hf := hh.add_const (mulLp hc hcC h)
  simpa only [sub_add_cancel,zero_add] using hf

end CAT0Fillings.ClosedCalculus
end

end OAI
