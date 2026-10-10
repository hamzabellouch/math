import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective
import OAI.Analysis.SymmetricDomains.UniformSmallOperators

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
namespace Release061
variable {P E F G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem c1_small_operators {f : P × E → F} {S : Set (P × E)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S)
    {K : Set E} (hK : IsCompact K) {p₀ : P} (hKS : {p₀} ×ˢ K ⊆ S)
    (L : P → F →L[ℝ] G) (hL : Tendsto (fun p => ‖L p‖) (𝓝 p₀) (𝓝 0)) :
    TendstoUniformlyOn (fun p x => L p (f (p,x))) (fun _ => 0) (𝓝 p₀) K ∧
    TendstoUniformlyOn (fun p x => fderiv ℝ (fun y => L p (f (p,y))) x)
      (fun _ => 0) (𝓝 p₀) K := by
  obtain ⟨hv,hd⟩ := c1_family_uniformly_compact hS hf hK hKS
  have hbase : ContinuousOn (fun x => f (p₀,x)) K := by
    exact hf.continuousOn.comp (by fun_prop) (fun x hx => hKS ⟨rfl,hx⟩)
  have hdbase : ContinuousOn (fun x => fderiv ℝ (fun y => f (p₀,y)) x) K := by
    exact (c1_partial_family hS hf).comp
      (show ContinuousOn (fun x : E => (p₀,x)) K by fun_prop)
      (fun x hx => hKS ⟨mem_singleton p₀,hx⟩)
  refine ⟨uniform_small_operators hK hbase hv L hL,?_⟩
  obtain ⟨C,_,hC⟩ := uniformly_eventually_norm_bounded hK hdbase hd
  obtain ⟨V,W,hV,_,hpV,hKW,hVW⟩ := generalized_tube_lemma
    isCompact_singleton hK hS hKS
  have hp : V ∈ 𝓝 p₀ := hV.mem_nhds (hpV (mem_singleton p₀))
  apply uniform_zero_of_norm_bound hL (C := C)
  filter_upwards [hC,hp] with p hC hp
  intro x hx
  have hs : (p,x) ∈ S := hVW ⟨hp,hKW hx⟩
  have hdiff : DifferentiableAt ℝ (fun y => f (p,y)) x :=
    (((hf _ hs).contDiffAt (hS.mem_nhds hs)).differentiableAt (by norm_num)).comp x (by fun_prop)
  have he : fderiv ℝ (fun y => L p (f (p,y))) x =
      (L p).comp (fderiv ℝ (fun y => f (p,y)) x) :=
    ((L p).hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _))

lemma c1_family_eventually_differentiable {f : P × E → F} {S : Set (P × E)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S)
    {K : Set E} (hK : IsCompact K) {p₀ : P} (hKS : {p₀} ×ˢ K ⊆ S) :
    ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, DifferentiableAt ℝ (fun y => f (p,y)) x := by
  obtain ⟨V,W,hV,_,hpV,hKW,hVW⟩ := generalized_tube_lemma
    isCompact_singleton hK hS hKS
  filter_upwards [hV.mem_nhds (hpV (mem_singleton p₀))] with p hp
  intro x hx
  have hs : (p,x) ∈ S := hVW ⟨hp,hKW hx⟩
  exact (((hf _ hs).contDiffAt (hS.mem_nhds hs)).differentiableAt (by norm_num)).comp x (by fun_prop)

theorem c1_perturbed_family {f : P × E → F} {g : P × E → G} {S : Set (P × E)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S) (hg : ContDiffOn ℝ 1 g S)
    {K : Set E} (hK : IsCompact K) {p₀ : P} (hKS : {p₀} ×ˢ K ⊆ S)
    (L : P → G →L[ℝ] F) (hL : Tendsto (fun p => ‖L p‖) (𝓝 p₀) (𝓝 0)) :
    TendstoUniformlyOn (fun p x => f (p,x)+L p (g (p,x))) (fun x => f (p₀,x)) (𝓝 p₀) K ∧
    TendstoUniformlyOn (fun p x => fderiv ℝ (fun y => f (p,y)+L p (g (p,y))) x)
      (fun x => fderiv ℝ (fun y => f (p₀,y)) x) (𝓝 p₀) K ∧
    (∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, DifferentiableAt ℝ (fun y => f (p,y)+L p (g (p,y))) x) := by
  obtain ⟨hfv,hfd⟩ := c1_family_uniformly_compact hS hf hK hKS
  obtain ⟨hgv,hgd⟩ := c1_small_operators hS hg hK hKS L hL
  have hdf := c1_family_eventually_differentiable hS hf hK hKS
  have hdg := c1_family_eventually_differentiable hS hg hK hKS
  refine ⟨by simpa only [Pi.add_def,add_zero] using hfv.add hgv,?_,?_⟩
  · have hd := hfd.add hgd
    simp only [Pi.add_def,add_zero] at hd
    apply hd.congr
    filter_upwards [hdf,hdg] with p hp hq
    intro x hx
    exact (fderiv_fun_add (hp x hx) ((L p).differentiableAt.comp x (hq x hx))).symm
  · filter_upwards [hdf,hdg] with p hp hq
    intro x hx
    exact (hp x hx).add ((L p).differentiableAt.comp x (hq x hx))

theorem c1_perturbed_family_local [ProperSpace E]
    {f : P × E → F} {g : P × E → G}
    (hf : ContDiffAt ℝ 1 f 0) (hg : ContDiffAt ℝ 1 g 0)
    (L : P → G →L[ℝ] F) (hL : Tendsto (fun p => ‖L p‖) (𝓝 0) (𝓝 0)) :
    ∃ r : ℝ, 0 < r ∧
    TendstoUniformlyOn (fun p x => f (p,x)+L p (g (p,x))) (fun x => f (0,x)) (𝓝 0) (closedBall 0 r) ∧
    TendstoUniformlyOn (fun p x => fderiv ℝ (fun y => f (p,y)+L p (g (p,y))) x)
      (fun x => fderiv ℝ (fun y => f (0,y)) x) (𝓝 0) (closedBall 0 r) ∧
    (∀ᶠ p in 𝓝 (0 : P), ∀ x ∈ closedBall 0 r,
      DifferentiableAt ℝ (fun y => f (p,y)+L p (g (p,y))) x) := by
  obtain ⟨V,hV,hfV⟩ := hf.contDiffOn (le_refl _) (by simp)
  obtain ⟨W,hW,hgW⟩ := hg.contDiffOn (le_refl _) (by simp)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hW)
  have hKS : {(0 : P)} ×ˢ closedBall (0 : E) (ε/2) ⊆ ball 0 ε := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    change p = 0 at hp
    subst p
    simp only [mem_ball,dist_zero_right,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg x)]
    have hi : ‖x‖ ≤ ε/2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    linarith
  refine ⟨ε/2,half_pos hε,?_⟩
  exact c1_perturbed_family isOpen_ball
    (hfV.mono (fun x hx => (hsub hx).1)) (hgW.mono (fun x hx => (hsub hx).2))
    (isCompact_closedBall _ _) hKS L hL

end Release061

end

end OAI
