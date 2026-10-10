import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2
import OAI.Analysis.BiholderTransport.Contact.CoordinateSupportGradient
import OAI.Analysis.BiholderTransport.Calculus.ShortGradientLimit

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterPoleLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [Nonempty M] in
lemma coordinateBackward_negative_support_center {c : M} {v s l : ℝ}
    {r : Model n} {φ : ℝ → ℝ} (hs : s≠0)
    (hr : s • (show TangentSpace 𝓘(ℝ,Model n) c from r)∈injectivityDomain c)
    (hφ : HasDerivAt φ l v) :
    coordinateBackward c (1, extChartAt 𝓘(ℝ,Model n) c c,
      -fderiv ℝ (fun w=>coordinateScalarSupport c φ
        (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),w))
          (extChartAt 𝓘(ℝ,Model n) c c))=riemannianExp c (l • r) := by
  let x := extChartAt 𝓘(ℝ,Model n) c c
  have hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target :=
    (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hb := (extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)
  have hL (d:Model n) : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).symmL ℝ c d=d := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) c)]
    exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source c)
  have hr' : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) c).symm x) r∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) c).symm x) := by
    dsimp only [x]
    rw [hb]
    simpa only [hL] using hr
  rw [(coordinateScalarSupport_hasFDerivAt hx hs hr' hφ).fderiv]
  simp only [coordinateBackward,map_neg,map_smul,neg_smul,one_smul,neg_neg]
  rw [movingNormal_eq hx,hb,hL]
  change riemannianExp c (l • (riemannianCoordinateMetric c x).inverse ((riemannianCoordinateMetric c x) r))=_
  rw [(riemannianCoordinateMetric_isInvertible hx).inverse_apply_self]

lemma parametric_short_center_pole_limit {a c : M} {ψ : P×Model n → ℝ}
    {p : P} (L : ℝ≥0)
    (hψ : ContDiffAt ℝ ∞ ψ (p,extChartAt 𝓘(ℝ,Model n) c c))
    {r : Model n} {v s l : ℝ} {φ : ℝ → ℝ} (hs : s≠0)
    (hr : s • (show TangentSpace 𝓘(ℝ,Model n) c from r)∈injectivityDomain c)
    (hφ : HasDerivAt φ l v)
    (heq : (fun w=>ψ (p,w))=fun w=>coordinateScalarSupport c φ
      (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),w))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj τj : ℕ → ℝ}
    {f : ℕ → M → ℝ} {F : ℕ → Model n → ℝ} {aj : ℕ → M}
    (hp : Tendsto pj atTop (𝓝 p))
    (hxx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (ht : Tendsto tj atTop (𝓝 1)) (hτ : Tendsto τj atTop (𝓝 0))
    (ha : Tendsto aj atTop (𝓝 a)) (hτpos : ∀ᶠ i in atTop,0<τj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i))=ψ (pj i,xj i))
    (hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
      (fun w=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i)))
    (herr : Tendsto (fun i=>fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i))+
      fderiv ℝ (fun w=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i))) atTop (𝓝 0))
    (hback : ∀ᶠ i in atTop,coordinateBackward c (tj i,
      parametricShortForward c ψ ((pj i,τj i),xj i),
      fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i)))=aj i) :
    a=riemannianExp c (l • r) := by
  let x := extChartAt 𝓘(ℝ,Model n) c c
  let z := fun i=>parametricShortForward c ψ ((pj i,τj i),xj i)
  let j := fderiv ℝ (fun w=>ψ (p,w)) x
  have hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target :=
    (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hG := parametric_short_gradient_tendsto L hx hψ hp hxx hτ hτpos hlip hbelow htouch hd
  have hF : Tendsto (fun i=>fderiv ℝ (F i) (z i)) atTop (𝓝 (-j)) := by
    convert herr.sub hG using 1 <;> simp only [add_sub_cancel_right,zero_sub,j,z,x]
  have hz : Tendsto z atTop (𝓝 x) := by
    have HH := (parametricShortForward_contDiffAt hx hψ).continuousAt.tendsto.comp
      ((hp.prodMk_nhds hτ).prodMk_nhds hxx)
    change Tendsto z atTop (𝓝 (parametricShortForward c ψ ((p,0),x))) at HH
    convert HH using 1
    simp only [parametricShortForward,shortForward_zero hx]
  have HB := (coordinateBackward_contMDiffAt (q := (1,x,-j)) hx).continuousAt.tendsto.comp
    (ht.prodMk_nhds (hz.prodMk_nhds hF))
  have HE : coordinateBackward c (1,x,-j)=a := tendsto_nhds_unique (HB.congr' hback) ha
  rw [←HE]
  dsimp only [j,x]
  rw [heq]
  exact coordinateBackward_negative_support_center hs hr hφ

omit [Nonempty M] in
lemma reverse_minimizer_regular {a c : M}
    {r : TangentSpace 𝓘(ℝ,Model n) c} {q : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈injectivityDomain c) (hq : q∈minimizingVectors a)
    (ha : riemannianExp c r=a) (hc : riemannianExp a q=c) : q∈injectivityDomain a := by
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨c,r⟩
  have hb : (reverseRay z).1=a := (reverseRay_base z).trans ha
  have hR := reverseRay_regular (z := z) hr
  have hE := reverseRay_endpoint z
  generalize hw : reverseRay z=w
  rw [hw] at hb hR hE
  rcases w with ⟨b,p⟩
  change b=a at hb
  subst b
  have he := riemannianExp_interior_unique hR hq (hE.trans hc.symm)
  exact he ▸ hR

end CenterPoleLimit
end WeakMTWTransport

end
end

end OAI
