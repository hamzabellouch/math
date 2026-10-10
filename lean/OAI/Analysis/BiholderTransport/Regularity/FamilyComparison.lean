import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.PoleLipschitz
import OAI.Analysis.BiholderTransport.Geodesics.ChartLipschitz
import OAI.Analysis.BiholderTransport.CostGeometry.ActualPole
import OAI.Analysis.BiholderTransport.Convexity.ModifiedEnvelopeRegularity
import OAI.Analysis.BiholderTransport.Convexity.JensenPackage
import OAI.Analysis.BiholderTransport.Convexity.FamilyShortEnvelope

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma WeakMTW.family_comparison_local_data (hmtw : WeakMTW (n := n) (M := M))
    {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {Kp : Set P} (hKp : IsCompact Kp)
    (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) {Lφ : ℝ≥0}
    (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ R>0,∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ ψ:ℝ → ℝ,Continuous ψ → ∀ τ:ℝ,0<τ → τ<1/2 → τ<δ →
      ∀ c:M,extChartAt 𝓘(ℝ,Model n) a c∈ball (extChartAt 𝓘(ℝ,Model n) a a) R →
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let w := fun y=>ψ (cTransform u y)
      let g := fun y=>Φ (p,cTransform u y)
      let F := chartOuterEnvelope w (1-τ) a
      let G := chartCenterEnvelope g (1-τ) a
      let pole : Model n → M := chartActualPole w (1-τ) a
      let χP := extChartAt 𝓘(ℝ,Model n) (pole (χ c))
      ∃ r>0,∃ JF JG JY JP:ℝ≥0,∃ Y:Model n → M,
        (∀ z∈ball (χ c) r,DifferentiableAt ℝ F z) ∧
        (∀ z∈ball (χ c) r,DifferentiableAt ℝ G z) ∧
        LipschitzOnWith JF (fderiv ℝ F) (ball (χ c) r) ∧
        LipschitzOnWith JG (fderiv ℝ G) (ball (χ c) r) ∧
        LipschitzOnWith JY (fun z=>χ (Y z)) (ball (χ c) r) ∧
        LipschitzOnWith JP (fun z=>χP (pole z)) (ball (χ c) r) ∧
        ∀ z∈ball (χ c) r,
          Y z∈χ.source ∧ pole z∈χP.source ∧
          (∀ y:M,G z=g y+cost y (χ.symm z)/(1-(1-τ)) ↔ y=Y z) ∧
          F z=cTransform w (pole z)+cost (pole z) (χ.symm z)/(1-τ) := by
  obtain ⟨J,JY,Rg,hRg,δ,hδ,HG⟩ :=
    uniform_family_short_envelope_data (n := n) hΦ hKp hmono hφL A B a
  obtain ⟨BF,hBF,Rf,hRf,hTf,HF⟩ := hmtw.uniform_hopfLax_C11 a
  obtain ⟨CP,hCP,Rp,hRp,hTp,HP⟩ := hmtw.uniform_hopfPole_lipschitz a
  let R := min (Rg/8) (min (Rf/8) (Rp/2))
  have hR : 0<R := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨R,hR,δ,hδ,?_⟩
  intro p hp u hu hb ψ hψ τ hτ hτhalf hτδ c hc
  dsimp only
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let w : M → ℝ := fun y=>ψ (cTransform u y)
  have hw : Continuous w := hψ.comp (continuous_cTransform hu)
  have hdual : IsCostDualPair (cTransform w) (cTransform (cTransform w)) :=
    ⟨(cTransform_triple hw).symm,rfl⟩
  have ht : 0<1-τ := by linarith
  have ht1 : 1-τ<1 := by linarith
  obtain ⟨hgdiff,hgl,Y,hY,hy⟩ := HG p hp u hu hb τ hτ hτδ
  let G : Model n → ℝ := fun z=>hopfLax τ (fun y=>Φ (p,cTransform u y)) (χ.symm z)
  have hsmall : ball (χ a) (Rg/4)⊆ball (χ a) Rg := ball_subset_ball (by linarith)
  obtain ⟨hgD,hgL⟩ := C11_const_mul_cancel (f := G) hτ.ne'
    (fun z hz=>hgdiff z (hsmall hz)) hgl
  obtain ⟨hfD,hfL⟩ := HF (1-τ) ht ht1 (cTransform w) (cTransform (cTransform w))
    (continuous_cTransform hw) (continuous_cTransform (continuous_cTransform hw)) hdual
  let pole : Model n → M := chartActualPole w (1-τ) a
  have hpL : LipschitzOnWith (Real.toNNReal (CP/(1-(1-τ)))) pole (ball (χ a) Rp) :=
    HP (1-τ) (by linarith) ht1 (cTransform w) (cTransform (cTransform w))
      (continuous_cTransform hw) (continuous_cTransform (continuous_cTransform hw)) hdual
  have hrg : R≤Rg/8 := min_le_left _ _
  have hrf : R≤Rf/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hrp : R≤Rp/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hcRp : χ c∈ball (χ a) Rp := (ball_subset_ball (by linarith : R≤Rp)) hc
  have hpC : ContinuousAt pole (χ c) := hpL.continuousOn.continuousAt (isOpen_ball.mem_nhds hcRp)
  obtain ⟨AP,rP,hrP,hpsrc,hpchart⟩ := exists_lipschitzOn_chart (n := n) (pole (χ c))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (isOpen_ball.mem_nhds hc) (hpC.preimage_mem_nhds (ball_mem_nhds (pole (χ c)) hrP)))
  have hsub : ball (χ c) r⊆ball (χ a) R := fun z hz=>(hrsub hz).1
  have himage : ∀ z∈ball (χ c) r,pole z∈ball (pole (χ c)) rP := fun z hz=>(hrsub hz).2
  have hrg4 : ball (χ c) r⊆ball (χ a) (Rg/4) := hsub.trans (ball_subset_ball (by linarith))
  have hrf4 : ball (χ c) r⊆ball (χ a) (Rf/4) := hsub.trans (ball_subset_ball (by linarith))
  have hrp' : ball (χ c) r⊆ball (χ a) Rp := hsub.trans (ball_subset_ball (by linarith))
  have htau : 1-(1-τ)=τ := by ring
  have heq : chartCenterEnvelope (n := n) (fun y=>Φ (p,cTransform u y)) (1-τ) a=G := by
    funext z
    change hopfLax (1-(1-τ)) _ _=hopfLax τ _ _
    rw [htau]
  refine ⟨r,hr,Real.toNNReal (6*(BF/(1-τ)+BF/(1-(1-τ)))),‖τ⁻¹‖₊*J,JY,
    AP*Real.toNNReal (CP/(1-(1-τ))),Y,?_,?_,hfL.mono hrf4,?_,
    hY.mono (hrg4.trans hsmall),hpchart.comp (hpL.mono hrp') himage,?_⟩
  · exact fun z hz=>hfD z ((hsub.trans (ball_subset_ball (by linarith : R≤Rf))) hz)
  · rw [heq]
    exact fun z hz=>hgD z (hrg4 hz)
  · rw [heq]
    exact hgL.mono hrg4
  · intro z hz
    have hyz := hy z (hsmall (hrg4 hz))
    refine ⟨hyz.1,hpsrc (himage z hz),?_,hmtw.hopfPole_minimizer
      (continuous_cTransform hw) (continuous_cTransform (continuous_cTransform hw)) hdual ht ht1 _⟩
    simpa only [chartCenterEnvelope,htau,G,χ] using hyz.2
end WeakMTWTransport

end

end OAI
