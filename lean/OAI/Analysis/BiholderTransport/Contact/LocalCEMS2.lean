import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ContactPSD
import OAI.Analysis.BiholderTransport.Coordinates.AePullbackLipschitzChart
import OAI.Analysis.BiholderTransport.Regularity.PosSemidefApplyInner
import OAI.Analysis.BiholderTransport.Contact.LocalCEMS
import OAI.Analysis.BiholderTransport.Contact.ContactCharts2
import OAI.Analysis.BiholderTransport.Volume.IntrinsicJacobian

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section LocalCEMS
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma local_contact_cems_full {v : M → ℝ} (hv : Continuous v)
    {G : Set M} (hGm : MeasurableSet G)
    (hGD : ∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    (hGi : InjOn (contactSelection hv) G)
    (hReg : ∀ x∈G, ∃ p A, NormalAlexandrovContact (n := n) v x p A)
    (a b : M) (hGs : G⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hTs : contactSelection hv '' G⊆(extChartAt 𝓘(ℝ,Model n) b).source)
    {C D H K : ℝ≥0} (hC : 0<C) (hK : 0<K)
    (hd : LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) G)
    (hdi : LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
      ((extChartAt 𝓘(ℝ,Model n) a) '' G))
    (he : LipschitzOnWith H (extChartAt 𝓘(ℝ,Model n) b) (contactSelection hv '' G))
    (hei : LipschitzOnWith K (extChartAt 𝓘(ℝ,Model n) b).symm
      ((extChartAt 𝓘(ℝ,Model n) b) '' (contactSelection hv '' G)))
    {l u : ℝ≥0∞} (hl : 0<l)
    (hmass : ∀ B : Set M, MeasurableSet B → B⊆G →
      l*metricVolume n B≤ metricVolume n (contactSelection hv '' B) ∧
      metricVolume n (contactSelection hv '' B)≤u*metricVolume n B) :
    ∀ᵐ x ∂(metricVolume n).restrict G, ∃ p A,
      NormalAlexandrovContact (n := n) v x p A ∧
      (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
      ∃ R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      ∃ S : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n,
        l/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n)≤
          ENNReal.ofReal |(S.comp ((normalHessianOperator x p+A).comp R)).det| ∧
        ENNReal.ofReal |(S.comp ((normalHessianOperator x p+A).comp R)).det|≤
          (H:ℝ≥0∞)^n*u*(D:ℝ≥0∞)^n ∧
        |(S.comp ((normalHessianOperator x p+A).comp R)).det| *chartJacobian (n := n) a x=
          chartJacobian (n := n) b (contactSelection hv x)*expJacobian (n := n) x p*
            |(normalHessianOperator x p+A).det| := by
  classical
  let d := extChartAt 𝓘(ℝ,Model n) a
  let e := extChartAt 𝓘(ℝ,Model n) b
  let T := contactSelection hv
  have hIm : MeasurableSet (d '' G) := hGm.image_of_continuousOn_injOn hd.continuousOn
    (d.injOn.mono hGs)
  have hEx (z : Model n) (hz : z∈d '' G) :
      ∃ F : Model n →L[ℝ] Model n,
        HasFDerivWithinAt (e ∘ T ∘ d.symm) F (d '' G) z ∧
        ∃ x∈G, d x=z ∧ ∃ p A, NormalAlexandrovContact (n := n) v x p A ∧
          ∃ R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
          ∃ S : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n,
            F=S.comp ((normalHessianOperator x p+A).comp R) ∧
            S=fderiv ℝ (e ∘ riemannianExp (n := n) x) p ∧
            (fderiv ℝ (d ∘ riemannianExp (n := n) x) 0).comp R=
              ContinuousLinearMap.id ℝ (Model n) := by
    obtain ⟨x,hx,rfl⟩ := hz
    obtain ⟨p,A,hp⟩ := hReg x hx
    obtain ⟨R,S,hF,hS,hR⟩ := contact_selection_chart_differential_full hv (contactSelection_mem hv)
      hGD hx hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 a b hGs (hTs ⟨x,hx,rfl⟩)
    exact ⟨_,hF,x,hx,rfl,p,A,hp,R,S,rfl,hS,hR⟩
  let F : Model n → Model n →L[ℝ] Model n := fun z =>
    if hz : z∈d '' G then (hEx z hz).choose else 0
  have hF (z : Model n) (hz : z∈d '' G) :
      HasFDerivWithinAt (e ∘ T ∘ d.symm) (F z) (d '' G) z := by
    simpa only [F,dite_eq_left hz] using (hEx z hz).choose_spec.1
  have hJac := ae_chart_jacobian_bounds d e hGm hIm hGs hTs hGi
    hC hK hd hdi he hei hmass hF
  filter_upwards [hJac,ae_restrict_mem hGm] with x hx hxG
  have hxI : d x∈d '' G := ⟨x,hxG,rfl⟩
  have hFspec := (hEx (d x) hxI).choose_spec.2
  obtain ⟨y,hy,hyx,p,A,hp,R,S,hEq,hS,hR⟩ := hFspec
  have hyx' : y=x := d.injOn (hGs hy) (hGs hxG) hyx
  subst y
  have hEq' : F (d x)=S.comp ((normalHessianOperator x p+A).comp R) := by
    simpa only [F,dite_eq_left hxI] using hEq
  rw [hEq'] at hx
  refine ⟨p,A,hp,?_,R,S,hx.1,hx.2,?_⟩
  · apply posDef_of_posSemidef_injective
    · intro w z
      simp only [add_apply,inner_add_left,inner_add_right,
        inner_normalHessianOperator,hp.2.2.1]
      rw [← real_inner_comm w (normalHessianOperator x p z),inner_normalHessianOperator,
        normalHessian_symm hp.2.1 w z]
    · exact normal_contact_hessian_posSemidef hv hp.1 hp.2.1 hp.2.2.2
    · apply injective_middle_of_det_comp_ne_zero (by rfl) R S
      intro hh
      have hpos : 0<l/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n) := ENNReal.div_pos hl.ne'
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
          (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      rw [hh,abs_zero,ENNReal.ofReal_zero] at hx
      exact (not_le_of_gt hpos) hx.1
  · have hTx : T x=riemannianExp x p := contact_unique_of_mdifferentiable hv (hGD x hxG)
      (contactSelection_mem hv x) hp.1.2
    change contactSelection hv x=riemannianExp x p at hTx
    rw [hS,hTx]
    exact intrinsic_contact_det a b (hGs hxG) (hTx ▸ hTs ⟨x,hxG,rfl⟩)
      (normalHessianOperator x p+A) R hR

end LocalCEMS
end WeakMTWTransport

end

end

end

end OAI
