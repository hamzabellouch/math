import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.TrueCenterGain
import OAI.Analysis.BiholderTransport.Coordinates.ChartTrueCenter

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartCenterGain
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance chartCenterGainFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_chart_true_center_gain : ∃δ>0,∀ᶠ l:ℝ in 𝓝 1,l<1 → 0<l →
    ∀(u:M → ℝ) (a c y:M) (b q:Model n),
    b∈(extChartAt 𝓘(ℝ,Model n) a).target →
    chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b) →
    movingPrefix a 1 b q=y → y∈(extChartAt 𝓘(ℝ,Model n) c).source →
    ∀p:TangentSpace 𝓘(ℝ,Model n) y,
    ∀A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y,
    NormalAlexandrovContact (n:=n) u y p A →
    (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d) →
    riemannianExp y (l • p)=(extChartAt 𝓘(ℝ,Model n) a).symm b →
    ∀φ:ℝ → ℝ,ContDiffAt ℝ 2 φ (cTransform u y) → deriv φ (cTransform u y)=l →
    ∀s:Model n,∀S:Model n →L[ℝ] Model n,
    (∀d e,inner ℝ (S d) e=inner ℝ d (S e)) →
    HasQuadraticExpansion (fun h=>φ (cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
      (extChartAt 𝓘(ℝ,Model n) c y+h)))) s S →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (bilinearOperator V).det=(chartFiberInverse a b).toLinearMap.normDet^2*l^n*
        (expJacobian ((extChartAt 𝓘(ℝ,Model n) a).symm b) (chartFiberInverse a b q))^2*
        (normalHessianOperator y p+A).det ∧
      ∀d,V d d+δ*(1-l)*frameMetric a b d d+
        (iteratedDeriv 2 φ (cTransform u y)/l^2)*(frameMetric a b q d)^2≤
          chartJetMatrix a c b q (innerSL ℝ s) ((innerSL ℝ).comp S) d d := by
  obtain ⟨δ,hδ,Hδ⟩:=exists_uniform_true_center_gain (n:=n) (M:=M)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [Hδ] with l hl
  intro hl1 hl0 u a c y b q hb hq hy hc p A hA hp hpx φ hφ hφd s S hS hSe
  obtain ⟨R,V,hR,hR0,hRe,hVs,hVp,hVdet,hmat⟩:=
    chart_true_center_matrix hb hq hy hc hA hp hl0 hl1 hpx hφ hφd hS hSe
  let VB:Model n →L[ℝ] Model n →L[ℝ] ℝ:=(innerSL ℝ).comp V
  have hVB:bilinearOperator VB=V:=by
    apply ContinuousLinearMap.ext
    intro d
    apply ext_inner_right ℝ
    intro e
    rw [bilinearOperator_inner]
    rfl
  refine ⟨VB,?_,?_,?_,?_⟩
  · intro d e
    change inner ℝ (V d) e=inner ℝ (V e) d
    rw [hVs,real_inner_comm]
  · exact hVp
  · rwa [hVB]
  · intro d
    have he:riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) (chartFiberInverse a b q)=y:=by
      simpa only [movingPrefix_eq hb,one_smul,chartFiberInverse] using hy
    have HG:=hl hl1 ((extChartAt 𝓘(ℝ,Model n) a).symm b) (chartFiberInverse a b q)
    rw [he] at HG
    have HH:=HG p hA.2.1 hq hpx R hR hR0 hRe (chartFiberInverse a b d)
    rw [hmat,frameMetric_apply hb,frameMetric_apply hb,real_inner_self_eq_norm_sq]
    dsimp only [VB,ContinuousLinearMap.comp_apply,innerSL_apply_apply]
    linarith only [HH]
end ChartCenterGain
end WeakMTWTransport

end
end

end OAI
