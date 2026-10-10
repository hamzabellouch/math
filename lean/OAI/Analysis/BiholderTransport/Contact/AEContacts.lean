import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull
import OAI.Analysis.BiholderTransport.Regularity.AERademacher

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AEContacts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma active_log_derivative {v : M → ℝ} (hv : Continuous v) {x : M}
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈activeLogs (n := n) v x) :
    HasFDerivAt (fun h => cTransform v (riemannianExp x h)) (innerSL ℝ p) 0 := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    (-2:ℝ)*(normalCost x ((1/2:ℝ) • p) h-normalCost x ((1/2:ℝ) • p) 0)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hID).sub_const
      (normalCost x ((1/2:ℝ) • p) 0)).const_smul (-2:ℝ)).congr_fderiv
    ext h
    simp only [smul_apply,innerSL_apply_apply,inner_neg_left,real_inner_smul_left,smul_eq_mul]
    ring
  have hU : DifferentiableAt ℝ (fun h : TangentSpace 𝓘(ℝ,Model n) x => cTransform v (riemannianExp x h)) 0 := by
    have hf : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v)
        (riemannianExp (n := n) x 0) := by simpa only [riemannianExp_zero] using hDiff
    exact (hf.comp 0 ((contMDiff_riemannianExp_fiber x).contMDiffAt.mdifferentiableAt
      (by simp))).differentiableAt
  have hMin : IsLocalMin (fun h => cTransform v (riemannianExp x h)-f h) 0 := by
    apply Filter.Eventually.of_forall
    intro h
    have hs := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
    have he : f h = -(cost (riemannianExp x h) (riemannianExp x ((1/2:ℝ) • p)) -
        cost x (riemannianExp x ((1/2:ℝ) • p))) / (1/2:ℝ) := by
      dsimp [f,normalCost]
      rw [riemannianExp_zero]
      ring
    change cTransform v (riemannianExp x 0)-f 0≤
      cTransform v (riemannianExp x h)-f h
    simp only [riemannianExp_zero,show f 0=0 by simp [f],sub_zero,he]
    linarith only [hs]
  have he := sub_eq_zero.mp (hMin.hasFDerivAt_eq_zero (hU.hasFDerivAt.sub hD))
  rw [←he]
  exact hU.hasFDerivAt

omit [MeasurableSpace M] [BorelSpace M] in
lemma contact_unique_of_mdifferentiable {v : M → ℝ} (hv : Continuous v) {x : M}
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {y z : M} (hy : contactGap (cTransform v) v x y=0)
    (hz : contactGap (cTransform v) v x z=0) : y=z := by
  obtain ⟨p,hp,hep⟩ := exists_minimizing_vector (n := n) x y
  obtain ⟨q,hq,heq⟩ := exists_minimizing_vector (n := n) x z
  have hpA : p∈activeLogs (n := n) v x := ⟨hp,by simpa only [hep] using hy⟩
  have hqA : q∈activeLogs (n := n) v x := ⟨hq,by simpa only [heq] using hz⟩
  have H := (active_log_derivative hv hDiff hpA).unique (active_log_derivative hv hDiff hqA)
  have hpq : p=q := by
    apply ext_inner_right ℝ
    intro h
    exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) H
  rw [←hep,←heq,hpq]

variable [Nonempty M]
lemma cTransform_ae_unique_contact {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ x ∂metricVolume (M := M) n, ∃! y, contactGap (cTransform v) v x y=0 := by
  filter_upwards [cTransform_ae_mdifferentiableAt hv] with x hx
  obtain ⟨y,hy⟩ := cTransform_gap_zero hv x
  exact ⟨y,hy,fun z hz => contact_unique_of_mdifferentiable hv hx hz hy⟩

end AEContacts
end WeakMTWTransport

end

end

end

end OAI
