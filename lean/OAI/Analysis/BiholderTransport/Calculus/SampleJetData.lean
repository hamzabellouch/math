import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.UniformFixedCrossing
import OAI.Analysis.BiholderTransport.Calculus.SamplePoleDerivative
import OAI.Analysis.BiholderTransport.Regularity.NonnegativeTransfer

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

omit [Nonempty M] in
lemma exists_actual_uniform_regular_split_after {t:ℝ} (ht : 0<t) (ht1 : t<1) :
    ∃ s:ℝ,t<s ∧ s<1 ∧ ∀ x:M,∀ p:TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → s • p∈injectivityDomain x ∧
      (1-s) • (sprayFlow s (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow s (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have H : ∀ᶠ s in 𝓝[<] (1:ℝ),t<s ∧ s<1 ∧ ∀ x:M,
      ∀ p:TangentSpace 𝓘(ℝ,Model n) x,‖p‖≤Metric.diam (univ:Set M) →
        (1-s) • (sprayFlow s (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).2∈
          injectivityDomain (sprayFlow s (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1 := by
    filter_upwards [(uniformly_shifted_injectivityDomain_near_one
      (n := n) (M := M) (Metric.diam (univ:Set M))).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds ht1).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
      with s hs hst hs1
    exact ⟨hst,hs1,hs⟩
  obtain ⟨s,hst,hs1,hs⟩ := H.exists
  exact ⟨s,hst,hs1,fun x p hp=>⟨contracted_minimizer_mem_injectivityDomain hp
    (ht.trans hst) hs1,hs x p (minimizing_norm_le_diam hp)⟩⟩

lemma WeakMTW.actual_sample_pole_matrix (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {x a c : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈normalSubdifferential (n := n) (cTransform v) x)
    (hz : riemannianExp x (t • p)∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hD : DifferentiableAt ℝ
      (fun w : Model n => extChartAt 𝓘(ℝ,Model n) c
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm w)))
      (extChartAt 𝓘(ℝ,Model n) a (riemannianExp x (t • p)))) :
    let V := TangentSpace 𝓘(ℝ,Model n) x
    let I : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
    let L : V →L[ℝ] V →L[ℝ] ℝ := t • I - fderiv ℝ (fderiv ℝ
      (fun q:V=>hopfLax t (cTransform v) (riemannianExp x (t • q)))) p
    DifferentiableAt ℝ (fderiv ℝ
      (fun q:V=>hopfLax t (cTransform v) (riemannianExp x (t • q)))) p ∧
    (∀ d:V,0≤L d d) ∧ (∀ d e:V,L d e=L e d) ∧
    (∀ q∈activeLogs v x,∀ d:V,L (q-p) d=0) ∧
    (∀ (ι:Type) [Fintype ι] (pj:ι → V) (w:ι → ℝ),
      (∀ j,0≤w j) → (∑ j,w j=1) → (∑ j,w j • pj j=p) →
      (∀ j,pj j∈activeLogs v x) → ∀ i,0<w i →
      HasLowerSecondTaylor (fun d:V=>v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2)
        0 (w i • L)) := by
  dsimp only
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let q : subgradientGraph (n := n) (cTransform v) := ⟨⟨x,p⟩,hp⟩
  have hpole : hopfPole (n := n) t (cTransform v) (riemannianExp x (t • p))=x := by
    exact congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  obtain ⟨e,R,he,he0,herep⟩ := hmtw.exists_actual_normal_pole_derivative hv ht ht1 hz hx hpole hD
  have hpre := hmtw.active_hull_precut hv ht ht1 x p
    (normalSubdifferential_subset_active_hull hv x hp)
  have hdual : IsCostDualPair (cTransform v) (cTransform (cTransform v)) :=
    ⟨(cTransform_triple hv).symm,rfl⟩
  have HD' := hmtw.actualPole_second_derivative (continuous_cTransform hv)
    (continuous_cTransform (continuous_cTransform hv)) hdual ht ht1 hpre he he0 herep
  have HD := HD'.fderiv
  rw [HD,sub_sub_cancel]
  have H := hmtw.actualPole_taylor (continuous_cTransform hv)
    (continuous_cTransform (continuous_cTransform hv)) hdual ht ht1 hpre he he0 herep
  obtain ⟨s,hts,hs1,hs⟩ := exists_actual_uniform_regular_split_after (n := n) (M := M) ht ht1
  refine ⟨HD'.differentiableAt,H.2.1,?_,?_,?_⟩
  · intro d f
    change inner ℝ (R d) f=inner ℝ (R f) d
    exact (H.2.2 d f).trans (real_inner_comm (R f) d)
  · intro r hr d
    have hk := hmtw.actualPole_kernel (continuous_cTransform hv)
      (continuous_cTransform (continuous_cTransform hv)) hdual ht ht1 (ht.trans hts) hs1
      hpre hr.1 (active_contact_biconjugate hv hr.2).2 (hs x r hr.1).1 (hs x r hr.1).2
      he he0 herep
    simp only [ContinuousLinearMap.comp_apply,hk,map_zero,zero_apply]
  · intro ι _ pj w hw hw1 hbar ha i hi
    exact hmtw.modified_active_lower_jet_nonneg hv ht hts hs1 pj w hw hw1 i hi
      (fun j=>(ha j).1) (fun j=>(ha j).2) (fun j=>(hs x (pj j) (ha j).1).1)
      (fun j=>(hs x (pj j) (ha j).1).2) (hbar ▸ he) (hbar ▸ he0) (hbar ▸ herep)

end WeakMTWTransport

end

end OAI
