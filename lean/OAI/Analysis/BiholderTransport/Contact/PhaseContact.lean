import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.CotangentFlow
import OAI.Analysis.BiholderTransport.Convexity.ProximalProducer

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

lemma coordinatePhaseFlow_of_minimizer {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {u:M → ℝ} (hu:Continuous u) (hp:p∈minimizingVectors x)
    {t:ℝ} (ht:0<t) (ht1:t≤1)
    (he:hopfLax t u (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=
      u x+cost x (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hz:(sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1∈
      (extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1) :
    coordinatePhaseFlow a (t,
      extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1,
      fderiv ℝ (fun z=>hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z))
        (extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1)) =
      phaseLower a (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M) (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  let w:TangentBundle 𝓘(ℝ,Model n) M:=⟨x,p⟩
  let z:=sprayFlow t w
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let η:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hf:=hopfLax_derivative_of_minimizer hu hp ht ht1 he hd
  have hf':HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u) z.1 (innerSL ℝ ((1:ℝ) • z.2)) := by
    simpa only [one_smul] using hf
  have hh:=coordinate_gradient_of_hasMFDerivAt z hz (hopfLax t u) 1 hf'
  simp only [one_smul] at hh
  have hi:=riemannianCoordinateMetric_isInvertible (χ.map_source hz)
  have hraise:phaseRaise a (χ z.1,fderiv ℝ (fun q=>hopfLax t u (χ.symm q)) (χ z.1))=η z := by
    apply Prod.ext
    · rfl
    · change (riemannianCoordinateMetric a (χ z.1)).inverse _=(η z).2
      rw [hh.fderiv,hi.inverse_apply_self]
  change phaseLower a (η (sprayFlow (-t) (η.symm (phaseRaise a
    (χ z.1,fderiv ℝ (fun q=>hopfLax t u (χ.symm q)) (χ z.1))))))=phaseLower a (η w)
  rw [hraise,η.left_inv ((tangent_chart_source_iff _ _).mpr hz)]
  rw [←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

omit [Nonempty M] in
lemma divided_kernel_gradient {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {t:ℝ} (ht:t≠0) (hp:t • p∈injectivityDomain x)
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    HasFDerivAt (fun y=>cost ((extChartAt 𝓘(ℝ,Model n) a).symm y)
      (riemannianExp x (t • p))/t)
      (-(phaseLower a (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M) (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M))).2)
      (extChartAt 𝓘(ℝ,Model n) a x) := by
  have hg:=cost_start_gradient_of_injectivityDomain hp
  have hg':HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (fun y=>cost y (riemannianExp x (t • p))) x
      (innerSL ℝ ((-t) • p)) := by simpa only [neg_smul] using hg
  have hc:=coordinate_gradient_of_hasMFDerivAt (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)
    hx (fun y=>cost y (riemannianExp x (t • p))) (-t) hg'
  simp only [div_eq_mul_inv]
  apply (hc.mul_const t⁻¹).congr_fderiv
  ext v
  simp only [smul_apply, neg_apply,smul_eq_mul,phaseLower]
  field_simp
  rfl

lemma phase_contact_semiconvex {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {u:M → ℝ} (hu:Continuous u) (hp:p∈minimizingVectors x)
    {t:ℝ} (ht:0<t) (ht1:t<1)
    (he:hopfLax t u (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=
      u x+cost x (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hz:(sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1∈
      (extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1)
    {s:Set (Model n)} {K:ℝ}
    (hxs:extChartAt 𝓘(ℝ,Model n) a x∈s)
    (hsem:ConvexOn ℝ s (fun y=>u ((extChartAt 𝓘(ℝ,Model n) a).symm y)+K/2*‖y‖^2)) :
    let Q:=coordinatePhaseFlow a (t,
      extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1,
      fderiv ℝ (fun z=>hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z))
        (extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1))
    Q.1=extChartAt 𝓘(ℝ,Model n) a x ∧
      IsSemiconvexSubgradientOn (fun y=>u ((extChartAt 𝓘(ℝ,Model n) a).symm y)) s K Q.1
        ((InnerProductSpace.toDual ℝ (Model n)).symm Q.2) := by
  dsimp only
  rw [coordinatePhaseFlow_of_minimizer hu hp ht ht1.le he hz hd]
  refine ⟨rfl,?_⟩
  have hk:=divided_kernel_gradient ht.ne' (contracted_minimizer_mem_injectivityDomain hp ht ht1) hx
  have hmin:∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,Model n) a x),
      u ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))+
        cost ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))
          (riemannianExp x (t • p))/t ≤
      u ((extChartAt 𝓘(ℝ,Model n) a).symm y)+
        cost ((extChartAt 𝓘(ℝ,Model n) a).symm y) (riemannianExp x (t • p))/t := by
    apply Eventually.of_forall
    intro y
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,riemannianExp_smul,←he]
    exact hopfLax_le hu t _ _
  have HH:=kernel_minimum_semiconvex_subgradient hsem hxs hk hmin
  simp only [neg_neg] at HH
  convert HH using 1
  rfl

end WeakMTWTransport

end

end OAI
