import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.SplitPairing
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition
import OAI.Analysis.BiholderTransport.LinearAlgebra.MovingSplit

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
section Prefix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def prefixNormalCost (x : M) (t : ℝ)
    (q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x q.1) (riemannianExp x (t • q.2))/t

lemma prefixNormalCost_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (prefixNormalCost x t) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x q.1) (0,p) :=
    (he _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x (t • q.2)) (0,p) :=
    (he _).comp (0,p) (show ContDiffAt ℝ ∞ (fun q : V×V => t • q.2) (0,p) from by fun_prop).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc
  exact ((hc'.comp (0,p) (hu.prodMk hv)).contDiffAt.div_const t)

lemma prefixNormalCost_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0 < t) (hp : t • p ∈ injectivityDomain x) :
    prefixNormalCost x t (0,p) = t/2*‖p‖^2 := by
  have H := injectivityDomain_subset_minimizingVectors x hp
  change dist x (riemannianExp x (t • p)) = ‖t • p‖ at H
  simp only [prefixNormalCost,riemannianExp_zero,cost,H,norm_smul_of_nonneg ht.le]
  field_simp

lemma prefixNormalCost_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t ≠ 0) (hp : t • p ∈ injectivityDomain x)
    (u : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixNormalCost x t) (0,p) (u,0) = -inner ℝ p u := by
  have hB := (prefixNormalCost_contDiffAt hp).differentiableAt (by simp)
  have hnc := ((normalCost_contDiffAt hp).differentiableAt (by simp)).hasFDerivAt
  have H := hnc.mul_const t⁻¹
  have H' : HasFDerivAt (fun a => prefixNormalCost x t (a,p))
      (t⁻¹ • fderiv ℝ (normalCost x (t • p)) 0) 0 := by
    simpa only [prefixNormalCost,normalCost,div_eq_mul_inv] using H
  have hpair := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const p (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have heq := (hB.hasFDerivAt.comp (f := fun a => (a,p)) 0 hpair).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A u) heq
  change fderiv ℝ (prefixNormalCost x t) (0,p) (u,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • p)) 0 u at hh
  rw [normalCost_fderiv_zero hp,real_inner_smul_left] at hh
  rw [hh]
  field_simp

lemma prefixNormalCost_target_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0 < t) (hp : t • p ∈ injectivityDomain x)
    (u : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixNormalCost x t) (0,p) (0,u) = t*inner ℝ p u := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hB := (prefixNormalCost_contDiffAt hp).differentiableAt (by simp)
  have hnear : ∀ᶠ q : V in 𝓝 p, t • q ∈ injectivityDomain x :=
    (show ContinuousAt (fun q : V => t • q) p from by fun_prop).preimage_mem_nhds
      (isOpen_injectivityDomain x |>.mem_nhds hp)
  have heq : (fun q : V => prefixNormalCost x t (0,q)) =ᶠ[𝓝 p]
      (fun q : V => t/2*‖q‖^2) := hnear.mono (fun _ h => prefixNormalCost_zero ht h)
  have H := ((hasFDerivAt_id (𝕜 := ℝ) p).norm_sq).const_mul (t/2)
  have Hd : HasFDerivAt (fun q : V => prefixNormalCost x t (0,q))
      ((t/2) • (2 • innerSL ℝ p)) p := by
    exact H.congr_of_eventuallyEq heq
  have hpair := (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hh := congrArg (fun A : V →L[ℝ] ℝ => A u)
    ((hB.hasFDerivAt.comp (f := fun q : V => ((0:V),q)) p hpair).unique Hd)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,
    smul_apply,innerSL_apply_apply] at hh
  convert! hh using 1
  simp only [smul_eq_mul]
  ring

lemma prefixNormalCost_hessian_blocks {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0 < t) (hp : t • p ∈ injectivityDomain x)
    (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixNormalCost x t)) (0,p) (u,0) (0,v) = -inner ℝ u v ∧
    fderiv ℝ (fderiv ℝ (prefixNormalCost x t)) (0,p) (0,u) (0,v) = t*inner ℝ u v := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hB₂ := (prefixNormalCost_contDiffAt hp).of_le (m := 2)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hnear : ∀ᶠ q : V in 𝓝 p, t • q ∈ injectivityDomain x :=
    (show ContinuousAt (fun q : V => t • q) p from by fun_prop).preimage_mem_nhds
      (isOpen_injectivityDomain x |>.mem_nhds hp)
  constructor
  · have heq : (fun q : V => fderiv ℝ (prefixNormalCost x t) (0,q) (u,0)) =ᶠ[𝓝 p]
        (fun q : V => -inner ℝ u q) := by
      filter_upwards [hnear] with q hq
      rw [prefixNormalCost_source_gradient ht.ne' hq,real_inner_comm]
    have H := pair_hessian_snd_from_gradient hB₂ (u,0) heq
      (((innerSL ℝ u).hasFDerivAt (x := p)).neg) v
    rw [(hB₂.isSymmSndFDerivAt (by simp)).eq] at H
    exact H
  · have heq : (fun q : V => fderiv ℝ (prefixNormalCost x t) (0,q) (0,v)) =ᶠ[𝓝 p]
        (fun q : V => t*inner ℝ v q) := by
      filter_upwards [hnear] with q hq
      rw [prefixNormalCost_target_gradient ht hq,real_inner_comm]
    have H := pair_hessian_snd_from_gradient hB₂ (0,v) heq
      (((innerSL ℝ v).hasFDerivAt (x := p)).const_mul t) u
    simpa only [smul_apply,innerSL_apply_apply,real_inner_comm v u,smul_eq_mul] using H

end Prefix
end WeakMTWTransport

end

end

end

end OAI
