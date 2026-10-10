import OAI.Probability.SLE.Geometry.NoBoundaryAtoms
import OAI.Probability.SLE.Geometry.HalfPlaneChartBoundary

namespace OAI

/-! Finite nonzero real limits of conformal half-plane maps at actual
finite physical Brownian exits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

theorem halfPlane_finite_exit_limit
    (W : WienerLaw) (hW : IsWiener W) {D : Set ℂ} (hD : IsOpen D)
    {g f : ℂ → ℂ} (hg : DifferentiableOn ℂ g D)
    (hf : DifferentiableOn ℂ f upperHalfPlane)
    (hgH : MapsTo g D upperHalfPlane) (hfD : MapsTo f upperHalfPlane D)
    (hinv : ∀ z∈D, f (g z)=z) (w : ℂ) (hw : w∈D) (T : ℝ≥0) :
    ∀ᵐ b ∂W.prod W, ∀ τ : ℝ≥0, 0 < τ → τ ≤ T →
      (∀ t<τ, w+Complex.equivRealProdCLM.symm (planarWiener t b)∈D) →
      w+Complex.equivRealProdCLM.symm (planarWiener τ b)∉D →
      ∃ x : ℝ, x≠0 ∧
        Tendsto (fun t => g (w+Complex.equivRealProdCLM.symm (planarWiener t b)))
          (𝓝[<] τ) (𝓝 (x:ℂ)) := by
  let v := g w
  have hv : 0 < v.im := hgH hw
  let F := halfPlaneToDisk v ∘ g
  let H := f ∘ diskToHalfPlane v
  have hF : DifferentiableOn ℂ F D := (halfPlaneToDisk_differentiable hv).comp hg hgH
  have hFD : MapsTo F D (ball 0 1) := (halfPlaneToDisk_maps hv).comp hgH
  have hH : ContinuousOn H (ball 0 1) := hf.continuousOn.comp
    (diskToHalfPlane_differentiable v).continuousOn (diskToHalfPlane_maps hv)
  have hHD : MapsTo H (ball 0 1) D := hfD.comp (diskToHalfPlane_maps hv)
  have hFG (z) (hz : z∈D) : diskToHalfPlane v (F z)=g z :=
    diskToHalfPlane_halfPlaneToDisk hv (hgH hz)
  have hHF (z) (hz : z∈D) : H (F z)=z := by
    change f (diskToHalfPlane v (F z))=z
    rw [hFG z hz,hinv z hz]
  have hF0 : F w=0 := by simp [F,v,halfPlaneToDisk]
  have hlim := conformal_disk_finite_exit_limit W hW hD w hw hF hFD hH hHD hHF T
  have hnull1 := planarDiskExitAtom_null W hW hD w hw hF hFD hF0 1 (by simp) T
  have hnull0 := planarDiskExitAtom_null W hW hD w hw hF hFD hF0
    (halfPlaneToDisk v 0) (halfPlaneToDisk_zero_norm hv) T
  have hno1 : ∀ᵐ b ∂W.prod W, b∉planarDiskExitAtom D F w 1 T := by
    simpa only [ae_iff,not_not,ofPred_mem_eq] using hnull1
  have hno0 : ∀ᵐ b ∂W.prod W, b∉planarDiskExitAtom D F w (halfPlaneToDisk v 0) T := by
    simpa only [ae_iff,not_not,ofPred_mem_eq] using hnull0
  filter_upwards [hlim,hno1,hno0] with b hb hb1 hb0
  intro τ hτ hτT hp hx
  obtain ⟨c,hcn,hc⟩ := hb τ hτ hτT hp hx
  have hc1 : c≠1 := by
    intro he
    exact hb1 ⟨τ,hτ,hτT,hp,hx,he ▸ hc⟩
  have hc0 : c≠halfPlaneToDisk v 0 := by
    intro he
    exact hb0 ⟨τ,hτ,hτT,hp,hx,he ▸ hc⟩
  have hgconv := (diskToHalfPlane_continuousAt (v := v) hc1).tendsto.comp hc
  have heq : (fun t => diskToHalfPlane v (F (w+Complex.equivRealProdCLM.symm (planarWiener t b))))
      =ᶠ[𝓝[<] τ] (fun t => g (w+Complex.equivRealProdCLM.symm (planarWiener t b))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hFG _ (hp t ht)
  have hgconv' := hgconv.congr' heq
  let z := diskToHalfPlane v c
  have hzI : z.im=0 := diskToHalfPlane_boundary_im hcn
  have hz0 : z≠0 := diskToHalfPlane_boundary_ne_zero hv hc1 hc0
  have hzreal : z=(z.re:ℂ) := by apply Complex.ext <;> simp [hzI]
  refine ⟨z.re,?_,?_⟩
  · intro he
    exact hz0 (by rw [hzreal,he,Complex.ofReal_zero])
  · change Tendsto _ (𝓝[<] τ) (𝓝 z) at hgconv'
    rwa [hzreal] at hgconv'

end SLEExactGauge

end

end OAI
