import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ShortEnvelopeJetTest
import OAI.Analysis.BiholderTransport.Regularity.ParametricLowerSequence

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section ShortPullbackSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parametric_short_pullback_semibound {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (ht : Tendsto tj atTop (𝓝 0)) (htpos : ∀ᶠ i in atTop,0<tj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) a).symm (xj i))=ψ (pj i,xj i))
    {g : ℕ → E → Model n} {y : ℕ → E}
    (hgxy : ∀ᶠ i in atTop,g i (y i)=parametricShortForward a ψ ((pj i,tj i),xj i))
    (hjet : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (g i (y i)),DifferentiableAt ℝ
        (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z))) (g i (y i)) ∧
      ContDiffAt ℝ 2 (g i) (y i))
    {m : E →L[ℝ] Model n} {r : E →L[ℝ] E →L[ℝ] Model n}
    (hm : Tendsto (fun i=>fderiv ℝ (g i) (y i)) atTop (𝓝 m))
    (hr : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (g i)) (y i)) atTop (𝓝 r))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in atTop,∀ d:E,
      secondJetPullback (fderiv ℝ (fun w=>ψ (p,w)) x)
        (fderiv ℝ (fderiv ℝ (fun w=>ψ (p,w))) x) m r d d-ε*‖d‖^2≤
        fderiv ℝ (fderiv ℝ (fun w=>hopfLax (tj i) (f i)
          ((extChartAt 𝓘(ℝ,Model n) a).symm (g i w)))) (y i) d d := by
  obtain ⟨U,hU,hD,hH⟩ := exists_parametric_short_lower_sequence L hx hψ hp hxx ht htpos hlip hbelow htouch
  have hj : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (g i (y i)),DifferentiableAt ℝ
        (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z))) (g i (y i)) ∧
      ContDiffAt ℝ 2 (U i) (g i (y i)) ∧ ContDiffAt ℝ 2 (g i) (y i) ∧
      U i (g i (y i))=hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm (g i (y i))) ∧
      U i≤ᶠ[𝓝 (g i (y i))] (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z)) := by
    filter_upwards [hU,hjet,hgxy] with i hUi hji he
    rw [←he] at hUi
    exact ⟨hji.1,hji.2.1,hUi.1,hji.2.2,hUi.2.1,hUi.2.2⟩
  apply rough_smooth_pullback_limit_semibound hj ?_ ?_ hm hr hε
  · exact hD.congr' (hgxy.mono (fun i hi=>congrArg (fderiv ℝ (U i)) hi.symm))
  · exact hH.congr' (hgxy.mono (fun i hi=>congrArg (fderiv ℝ (fderiv ℝ (U i))) hi.symm))

end ShortPullbackSemibound
end WeakMTWTransport

end
end

end OAI
