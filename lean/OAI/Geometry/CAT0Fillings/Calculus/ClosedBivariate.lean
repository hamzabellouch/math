import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.Multiplier
import OAI.Geometry.CAT0Fillings.Calculus.Bivariate
import OAI.Geometry.CAT0Fillings.Calculus.ClosedChain

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F F₁ F₂ : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (hdF : ∀ t, HasFDerivAt F (binaryDerivative (F₁ t) (F₂ t)) t)
    (hc₁ : Continuous F₁) (hc₂ : Continuous F₂) {C : ℝ} (hC : 0 ≤ C)
    (hb₁ : ∀ t, |F₁ t| ≤ C) (hb₂ : ∀ t, |F₂ t| ≤ C) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => F₁ (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) • q.gradient hr w +
          F₂ (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) • q.closedGradient P w) := by
  obtain ⟨u,J,hu,hl⟩ := q.exists_lipschitz_approximants P
  have hv := (q.valueProjection.continuous.tendsto (P : q.GraphAmbient)).comp hl
  have hg := (q.gradientProjection.continuous.tendsto (P : q.GraphAmbient)).comp hl
  change Tendsto (fun j => value (hu j)) atTop (𝓝 (q.inclusion P)) at hv
  change Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 (q.closedGradient P)) at hg
  obtain ⟨s,hs,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hnames : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ∀ j,
      (value (hT := hT) (hu (s j))) x = u (s j) x := by
    apply ae_all_iff.mpr
    intro j
    exact ((Foundations.boundedLip_of_lipschitz (hu (s j))).memLp 2).coeFn_toLp
  have hae' : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT,
      Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x)) := by
    filter_upwards [hae,hnames] with x hx he
    simpa only [he] using hx
  have ha : ∀ᵐ w ∂q.atlasMeasure,
      Tendsto (fun j => u (s j) (q.atlasParam w)) atTop (𝓝 ((q.inclusion P) (q.atlasParam w))) :=
    q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X =>
      Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x))) hae'
  let b (D : ℝ × ℝ → ℝ) (j : ℕ) (w : ℕ × Euc (k+1)) := D (r (q.atlasParam w),u (s j) (q.atlasParam w))
  let c (D : ℝ × ℝ → ℝ) (w : ℕ × Euc (k+1)) := D (r (q.atlasParam w),q.inclusion P (q.atlasParam w))
  have hb (D : ℝ × ℝ → ℝ) (hD : Continuous D) (j : ℕ) : AEStronglyMeasurable (b D j) q.atlasMeasure :=
    (hD.measurable.comp ((hr.continuous.measurable.comp q.measurable_atlasParam).prodMk
      ((hu (s j)).continuous.measurable.comp q.measurable_atlasParam))).aestronglyMeasurable
  have hc (D : ℝ × ℝ → ℝ) (hD : Continuous D) : AEStronglyMeasurable (c D) q.atlasMeasure :=
    hD.comp_aestronglyMeasurable (((hr.continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable).prodMk
      ((Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving))
  have hbC (D : ℝ × ℝ → ℝ) (hD : ∀ t, |D t| ≤ C) (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b D j w| ≤ C :=
    Eventually.of_forall fun _ => hD _
  have hcC (D : ℝ × ℝ → ℝ) (hD : ∀ t, |D t| ≤ C) : ∀ᵐ w ∂q.atlasMeasure, |c D w| ≤ C :=
    Eventually.of_forall fun _ => hD _
  have hbc (D : ℝ × ℝ → ℝ) (hD : Continuous D) :
      ∀ᵐ w ∂q.atlasMeasure, Tendsto (fun j => b D j w) atTop (𝓝 (c D w)) := by
    filter_upwards [ha] with w hw
    exact (hD.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hw)
  have hgl₁ := mulLp_tendsto (hb F₁ hc₁) (hc F₁ hc₁) hC (hbC F₁ hb₁) (hcC F₁ hb₁)
    (hbc F₁ hc₁) (tendsto_const_nhds (x := q.gradient hr))
  have hgl₂ := mulLp_tendsto (hb F₂ hc₂) (hc F₂ hc₂) hC (hbC F₂ hb₂) (hcC F₂ hb₂)
    (hbc F₂ hc₂) (hg.comp hs.tendsto_atTop)
  have he (j : ℕ) : mulLp (hb F₁ hc₁ j) (hbC F₁ hb₁ j) (q.gradient hr) +
      mulLp (hb F₂ hc₂ j) (hbC F₂ hb₂ j) (q.gradient (hu (s j))) =
      q.gradient (hF.comp (hr.prodMk (hu (s j)))) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (mulLp (hb F₁ hc₁ j) (hbC F₁ hb₁ j) (q.gradient hr))
      (mulLp (hb F₂ hc₂ j) (hbC F₂ hb₂ j) (q.gradient (hu (s j)))),
      mulLp_ae (hb F₁ hc₁ j) (hbC F₁ hb₁ j) (q.gradient hr),
      mulLp_ae (hb F₂ hc₂ j) (hbC F₂ hb₂ j) (q.gradient (hu (s j))),
      q.gradient_bivariate_ae hr (hu (s j)) hF hdF] with w h1 h2 h3 h4
    rw [h1,Pi.add_apply,h2,h3,h4]
  have hgl := hgl₁.add hgl₂
  simp only [Function.comp_def,he] at hgl
  have hvl := (q.lipschitz_bivariateValue hr hF).continuous.tendsto (q.inclusion P) |>.comp (hv.comp hs.tendsto_atTop)
  simp only [Function.comp_def,q.bivariateValue_value] at hvl
  obtain ⟨Q,hQ,hG⟩ := q.closedGradient_closed (q.bivariateValue hr hF (q.inclusion P))
    (mulLp (hc F₁ hc₁) (hcC F₁ hb₁) (q.gradient hr) + mulLp (hc F₂ hc₂) (hcC F₂ hb₂) (q.closedGradient P))
    (fun j => q.lipSobolev (hF.comp (hr.prodMk (hu (s j))))) hvl hgl
  refine ⟨Q,?_,?_⟩
  · rw [hQ]
    exact q.bivariateValue_ae hr hF _
  · rw [hG]
    filter_upwards [Lp.coeFn_add (mulLp (hc F₁ hc₁) (hcC F₁ hb₁) (q.gradient hr))
      (mulLp (hc F₂ hc₂) (hcC F₂ hb₂) (q.closedGradient P)),
      mulLp_ae (hc F₁ hc₁) (hcC F₁ hb₁) (q.gradient hr),
      mulLp_ae (hc F₂ hc₂) (hcC F₂ hb₂) (q.closedGradient P)] with w h1 h2 h3
    rw [h1,Pi.add_apply,h2,h3]

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
lemma binaryDerivative_eq (L : (ℝ × ℝ) →L[ℝ] ℝ) :
    binaryDerivative (L (1,0)) (L (0,1)) = L := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = z.1 • ((1:ℝ),0)+z.2 • ((0:ℝ),1) := by ext <;> simp
  calc
    _ = z.1*L (1,0)+z.2*L (0,1) := by simp [binaryDerivative,mul_comm]
    _ = L (z.1 • ((1:ℝ),0)+z.2 • ((0:ℝ),1)) := by rw [map_add,map_smul,map_smul]; rfl
    _ = L z := congrArg L hz.symm

lemma binary_coeff_bound {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (t : ℝ × ℝ) :
    |fderiv ℝ F t (1,0)| ≤ B ∧ |fderiv ℝ F t (0,1)| ≤ B := by
  have hb := norm_fderiv_le_of_lipschitz ℝ hF (x₀ := t)
  constructor
  · calc
      |fderiv ℝ F t (1,0)| ≤ ‖fderiv ℝ F t‖*‖((1:ℝ),0)‖ := (fderiv ℝ F t).le_opNorm _
      _ ≤ B := by simpa using hb
  · calc
      |fderiv ℝ F t (0,1)| ≤ ‖fderiv ℝ F t‖*‖((0:ℝ),1)‖ := (fderiv ℝ F t).le_opNorm _
      _ ≤ B := by simpa using hb

lemma hasFDerivAt_binary {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (t : ℝ × ℝ) :
    HasFDerivAt F (binaryDerivative (fderiv ℝ F t (1,0)) (fderiv ℝ F t (0,1))) t := by
  rw [binaryDerivative_eq]
  exact (hF t).hasFDerivAt

end CAT0Fillings.ClosedCalculus
end

end OAI
