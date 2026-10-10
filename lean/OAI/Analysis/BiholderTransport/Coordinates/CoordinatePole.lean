import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.LowerTaylorComposition
import OAI.Analysis.BiholderTransport.Calculus.SampleJetData
import OAI.Analysis.BiholderTransport.Regularity.MovingPrefix
import OAI.Analysis.BiholderTransport.Regularity.RoughLinear

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinatePoleMatrix (a : M) (t : ℝ) (v : M → ℝ) (b p : Model n) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p-
    fderiv ℝ (fderiv ℝ (fun q=>hopfLax t (cTransform v) (movingPrefix a t b q))) p

omit [Nonempty M] in
lemma movingPrefix_chart_pullback {a c : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) (f : M → ℝ) :
    (fun q=>f ((extChartAt 𝓘(ℝ,Model n) c).symm (movingPrefixChart a c t b q)))=ᶠ[𝓝 p]
      (fun q=>f (movingPrefix a t b q)) := by
  have hN : ContinuousAt (movingPrefix a t b) p :=
    ((movingPrefix_contMDiffAt (p := p) hb).continuousAt).comp
      (show ContinuousAt (fun q:Model n=>(b,q)) p from by fun_prop)
  filter_upwards [hN.eventually ((isOpen_extChartAt_source (I := 𝓘(ℝ,Model n)) c).mem_nhds hc)]
    with q hq
  exact congrArg f ((extChartAt 𝓘(ℝ,Model n) c).left_inv hq)

lemma WeakMTW.coordinate_sample_pole_matrix (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {a c d : M} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈normalSubdifferential (n := n)
        (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hz : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hx : (extChartAt 𝓘(ℝ,Model n) a).symm b∈(extChartAt 𝓘(ℝ,Model n) d).source)
    (hD : DifferentiableAt ℝ
      (fun w : Model n => extChartAt 𝓘(ℝ,Model n) d
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
      (extChartAt 𝓘(ℝ,Model n) c (movingPrefix a t b p))) :
    let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
    let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
    let L := coordinatePoleMatrix a t v b p
    (∀ r:Model n,0≤L r r) ∧ (∀ r s:Model n,L r s=L s r) ∧
    (∀ q:Model n,A q∈activeLogs v x → ∀ r:Model n,L (q-p) r=0) ∧
    (∀ (ι:Type) [Fintype ι] (pj:ι → Model n) (w:ι → ℝ),
      (∀ j,0≤w j) → (∑ j,w j=1) → (∑ j,w j • pj j=p) →
      (∀ j,A (pj j)∈activeLogs v x) → ∀ i,0<w i →
      HasLowerSecondTaylor (fun r:Model n=>v (movingNormal a (b,pj i+r))+
        ‖A (pj i+r)‖^2/2) 0 (w i • L)) := by
  dsimp only
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let I : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  let f : V → ℝ := fun q=>hopfLax t (cTransform v) (riemannianExp x (t • q))
  let L₀ : V →L[ℝ] V →L[ℝ] ℝ := t • I-fderiv ℝ (fderiv ℝ f) (A p)
  have hz' : riemannianExp x (t • A p)∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simpa only [movingPrefix_eq hb] using hz
  have hD' : DifferentiableAt ℝ
      (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) d
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
      (extChartAt 𝓘(ℝ,Model n) c (riemannianExp x (t • A p))) := by
    simpa only [movingPrefix_eq hb] using hD
  obtain ⟨hfd,hpos,hsym,hker,hjet⟩ := hmtw.actual_sample_pole_matrix hv ht ht1 hp hz' hx hD'
  have hpre := hmtw.active_hull_precut hv ht ht1 x (A p)
    (normalSubdifferential_subset_active_hull hv x hp)
  have hnear : ∀ᶠ q in 𝓝 (A p),DifferentiableAt ℝ f q :=
    Filter.Eventually.of_forall (fun q=>hmtw.prefix_hopfLax_differentiable
      (continuous_cTransform hv) (continuous_cTransform (continuous_cTransform hv))
      ⟨(cTransform_triple hv).symm,rfl⟩ ht ht1 x q)
  have he : coordinatePoleMatrix a t v b p=pullBilinear L₀ A := by
    ext r s
    have hf : (fun q=>hopfLax t (cTransform v) (movingPrefix a t b q))=(fun q=>f (A q)) := by
      funext q
      exact congrArg (hopfLax t (cTransform v)) (movingPrefix_eq hb t q)
    rw [coordinatePoleMatrix,sub_apply,sub_apply,movingPrefixEnergy_hessian hb hpre,hf,
      second_fderiv_comp_linear_at A hnear hfd,pullBilinear_apply]
    rfl
  rw [he]
  refine ⟨fun r=>hpos (A r),fun r s=>hsym (A r) (A s),?_,?_⟩
  · intro q hq r
    change L₀ (A (q-p)) (A r)=0
    rw [map_sub]
    exact hker (A q) hq (A r)
  · intro ι _ pj w hw hw1 hbar ha i hi
    have hbar' : ∑ i,w i • A (pj i)=A p := by
      simpa only [map_sum,map_smul] using congrArg A hbar
    have H := hjet ι (fun j=>A (pj j)) w hw hw1 hbar' ha i hi
    have H' := H.comp_stationary (A.hasFDerivAt (x := 0)) (map_zero A)
    have heB : pullBilinear (w i • L₀) A=w i • pullBilinear L₀ A := by
      ext r s
      rfl
    rw [heB] at H'
    convert H' using 1
    funext r
    simp only [movingNormal_eq hb,map_add]
    rfl

end WeakMTWTransport

end

end OAI
