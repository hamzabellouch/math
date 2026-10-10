import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull
import OAI.Analysis.BiholderTransport.Coordinates.LocalMetricCharts

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma activeLog_derivative_eq {v : M → ℝ} (hv : Continuous v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ activeLogs v x)
    {D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun h => cTransform v (riemannianExp x h)) D 0) :
    D = innerSL ℝ p := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    cTransform v (riemannianExp x h) + 2 * normalCost x ((1/2:ℝ) • p) h
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro h
    have hh := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
    dsimp [f,normalCost]
    rw [riemannianExp_zero]
    linarith
  have hf : HasFDerivAt f (D - innerSL ℝ p) 0 := by
    apply (hD.add ((normalCost_hasFDerivAt_zero hID).const_mul 2)).congr_fderiv
    ext h
    simp only [_root_.add_apply,_root_.sub_apply,
      _root_.smul_apply,innerSL_apply_apply,inner_neg_left,
      real_inner_smul_left,smul_eq_mul]
    ring
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hf)

lemma activeLogs_subsingleton_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) :
    (activeLogs (n := n) v x).Subsingleton := by
  have hD' : DifferentiableAt ℝ (fun h : TangentSpace 𝓘(ℝ,Model n) x => cTransform v (riemannianExp x h)) 0 := by
    have he := ((contMDiff_riemannianExp_fiber (n := n) x 0).mdifferentiableAt (by simp))
    have hD0 : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v)
        (riemannianExp (n := n) x 0) := by simpa only [riemannianExp_zero] using hD
    exact (hD0.comp 0 he).differentiableAt
  intro p hp q hq
  have hh := (activeLog_derivative_eq hv hp hD'.hasFDerivAt).symm.trans
    (activeLog_derivative_eq hv hq hD'.hasFDerivAt)
  apply ext_inner_right ℝ
  intro h
  exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) hh

lemma contact_singleton_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {y z : M} (hy : contactGap (cTransform v) v x y = 0)
    (hz : contactGap (cTransform v) v x z = 0) : y = z := by
  obtain ⟨p,hp,hep⟩ := exists_minimizing_vector (n := n) x y
  obtain ⟨q,hq,heq⟩ := exists_minimizing_vector (n := n) x z
  have hp' : p ∈ activeLogs v x := ⟨hp,by simpa only [hep] using hy⟩
  have hq' : q ∈ activeLogs v x := ⟨hq,by simpa only [heq] using hz⟩
  have he := activeLogs_subsingleton_of_mdifferentiable hv hD hp' hq'
  exact hep.symm.trans ((congrArg (riemannianExp x) he).trans heq)

variable [MeasurableSpace M] [BorelSpace M]

lemma lipschitz_ae_mdifferentiable_metricVolume {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∀ᵐ x ∂(metricVolume (M := M) n), MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) u x := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) := continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  have hh := lipschitz_ae_mdifferentiable (E := Model n) hu
  have hh' : ∀ᵐ x ∂(Measure.hausdorffMeasure (n : ℝ) : Measure M),
      MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) u x := by
    simpa [Model] using hh
  exact Measure.smul_absolutelyContinuous.ae_le hh'

lemma cTransform_ae_singleton_contacts [Nonempty M] {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ x ∂(metricVolume (M := M) n),
      ∀ y z : M, contactGap (cTransform v) v x y = 0 →
        contactGap (cTransform v) v x z = 0 → y = z := by
  have hlip := cTransform_lipschitz hv (D := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩)
    (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))
  filter_upwards [lipschitz_ae_mdifferentiable_metricVolume (n := n) hlip] with x hx
  exact fun y z hy hz => contact_singleton_of_mdifferentiable hv hx hy hz

end WeakMTWTransport

end

end OAI
