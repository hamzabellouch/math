import Mathlib

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

local instance (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  fun _ => inferInstance
local instance : ∀ x : M, ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  fun _ => inferInstance
end

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma metricDual_isInvertible [FiniteDimensional ℝ E] (b : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ v : E, v ≠ 0 → 0 < b v v) : b.IsInvertible := by
  have hinj : Function.Injective b := by
    intro u v huv
    have hz : b (u-v) = 0 := by rw [map_sub,huv,sub_self]
    by_contra huv'
    have hp := hb (u-v) (sub_ne_zero.mpr huv')
    simp only [hz,zero_apply] at hp
    exact (lt_irrefl 0) hp
  let A : E →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp b
  have hA : Function.Injective A := (InnerProductSpace.toDual ℝ E).symm.injective.comp hinj
  have hAsur : Function.Surjective A := LinearMap.injective_iff_surjective.mp hA
  have hsur : Function.Surjective b := by
    intro q
    obtain ⟨v,hv⟩ := hAsur ((InnerProductSpace.toDual ℝ E).symm q)
    refine ⟨v,(InnerProductSpace.toDual ℝ E).symm.injective hv⟩
  exact ⟨ContinuousLinearEquiv.ofBijective b (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsur),rfl⟩

def coordinateChristoffel (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) : E :=
  (g x).inverse ((1/2:ℝ) •
    ((fderiv ℝ g x) u v + (fderiv ℝ g x) v u -
      (((fderiv ℝ g x).flip u).flip v)))

lemma coordinateChristoffel_metric (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v w : E) (hg : (g x).IsInvertible) :
    2 * g x (coordinateChristoffel g x u v) w =
      (fderiv ℝ g x) u v w + (fderiv ℝ g x) v u w - (fderiv ℝ g x) w u v := by
  rw [coordinateChristoffel,hg.self_apply_inverse]
  simp only [smul_apply,sub_apply,add_apply,flip_apply,smul_eq_mul]
  ring

lemma coordinateChristoffel_self_metric (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x v : E) (hg : (g x).IsInvertible) :
    2 * g x (coordinateChristoffel g x v v) v = (fderiv ℝ g x) v v v := by
  have hh := coordinateChristoffel_metric g x v v v hg
  linarith

def coordinateGeodesicField (g : E → E →L[ℝ] E →L[ℝ] ℝ) (z : E × E) : E × E :=
  (z.2,-coordinateChristoffel g z.1 z.2 z.2)

lemma metric_speed_derivative {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {γ v : ℝ → E} {t : ℝ}
    (hg : DifferentiableAt ℝ g (γ t)) (hi : (g (γ t)).IsInvertible)
    (hs : ∀ a b, g (γ t) a b = g (γ t) b a)
    (hγ : HasDerivAt γ (v t) t)
    (hv : HasDerivAt v (-coordinateChristoffel g (γ t) (v t) (v t)) t) :
    HasDerivAt (fun s => g (γ s) (v s) (v s)) 0 t := by
  have hgγ : HasDerivAt (fun s => g (γ s)) ((fderiv ℝ g (γ t)) (v t)) t :=
    hg.hasFDerivAt.comp_hasDerivAt t hγ
  have hgv : HasDerivAt (fun s => g (γ s) (v s))
      ((fderiv ℝ g (γ t)) (v t) (v t) +
        g (γ t) (-coordinateChristoffel g (γ t) (v t) (v t))) t :=
    hgγ.clm_apply hv
  have h : HasDerivAt (fun s => g (γ s) (v s) (v s))
      (((fderiv ℝ g (γ t)) (v t) (v t) +
        g (γ t) (-coordinateChristoffel g (γ t) (v t) (v t))) (v t) +
        g (γ t) (v t) (-coordinateChristoffel g (γ t) (v t) (v t))) t :=
    hgv.clm_apply hv
  have hid := coordinateChristoffel_self_metric g (γ t) (v t) hi
  have heq : ((fderiv ℝ g (γ t)) (v t) (v t) +
      g (γ t) (-coordinateChristoffel g (γ t) (v t) (v t))) (v t) +
      g (γ t) (v t) (-coordinateChristoffel g (γ t) (v t) (v t)) = 0 := by
    simp only [add_apply,map_neg,neg_apply]
    rw [hs (v t) (coordinateChristoffel g (γ t) (v t) (v t))]
    linarith
  exact heq ▸ h

lemma contDiffAt_coordinateChristoffel [CompleteSpace E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x u v : E}
    (hg : ContDiffAt ℝ ∞ g x) (hi : (g x).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : E × E × E => coordinateChristoffel g z.1 z.2.1 z.2.2)
      (x,u,v) := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ g) x := hg.fderiv_right (by simp)
  have hinv : ContDiffAt ℝ ∞ (fun x => (g x).inverse) x :=
    hi.contDiffAt_map_inverse.comp x hg
  have hf1 : ContDiffAt ℝ ∞ (fun x => (fderiv ℝ g x).flip) x :=
    hd.continuousLinearMap_comp
      (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  have hx : ContDiffAt ℝ ∞ (fun z : E × E × E => z.1) (x,u,v) := contDiffAt_fst
  have hu : ContDiffAt ℝ ∞ (fun z : E × E × E => z.2.1) (x,u,v) :=
    contDiffAt_fst.comp (x,u,v) contDiffAt_snd
  have hv : ContDiffAt ℝ ∞ (fun z : E × E × E => z.2.2) (x,u,v) :=
    contDiffAt_snd.comp (x,u,v) contDiffAt_snd
  have hfc : ContDiffAt ℝ ∞ (fun z : E × E × E => (fderiv ℝ g z.1).flip)
      (x,u,v) := ContDiffAt.comp
        (g := fun y : E => (fderiv ℝ g y).flip)
        (f := fun z : E × E × E => z.1) (x,u,v) hf1 hx
  have hfu : ContDiffAt ℝ ∞ (fun z : E × E × E => (fderiv ℝ g z.1).flip z.2.1)
      (x,u,v) := hfc.clm_apply hu
  have hfu' : ContDiffAt ℝ ∞ (fun z : E × E × E => ((fderiv ℝ g z.1).flip z.2.1).flip)
      (x,u,v) := hfu.continuousLinearMap_comp
        (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hf2 : ContDiffAt ℝ ∞ (fun z : E × E × E =>
      (((fderiv ℝ g z.1).flip z.2.1).flip z.2.2)) (x,u,v) := hfu'.clm_apply hv
  have hduv : ContDiffAt ℝ ∞ (fun z : E × E × E => (fderiv ℝ g z.1) z.2.1 z.2.2)
      (x,u,v) := ((hd.comp (x,u,v) hx).clm_apply hu).clm_apply hv
  have hdvu : ContDiffAt ℝ ∞ (fun z : E × E × E => (fderiv ℝ g z.1) z.2.2 z.2.1)
      (x,u,v) := ((hd.comp (x,u,v) hx).clm_apply hv).clm_apply hu
  exact (hinv.comp (x,u,v) hx).clm_apply
    (((hduv.add hdvu).sub hf2).const_smul (1/2:ℝ))

lemma contDiffAt_coordinateGeodesicField [CompleteSpace E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x v : E}
    (hg : ContDiffAt ℝ ∞ g x) (hi : (g x).IsInvertible) :
    ContDiffAt ℝ ∞ (coordinateGeodesicField g) (x,v) := by
  have hΓ : ContDiffAt ℝ ∞ (fun z : E × E => coordinateChristoffel g z.1 z.2 z.2) (x,v) :=
    (contDiffAt_coordinateChristoffel (u := v) (v := v) hg hi).comp (x,v)
      (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_snd))
  exact contDiffAt_snd.prodMk hΓ.neg

lemma coordinate_geodesic_speed_constant
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {γ v : ℝ → E} {a b s t : ℝ}
    (hg : ∀ r ∈ Ioo a b, DifferentiableAt ℝ g (γ r))
    (hi : ∀ r ∈ Ioo a b, (g (γ r)).IsInvertible)
    (hs : ∀ r ∈ Ioo a b, ∀ u w, g (γ r) u w = g (γ r) w u)
    (hder : ∀ r ∈ Ioo a b, HasDerivAt γ (v r) r ∧
      HasDerivAt v (-coordinateChristoffel g (γ r) (v r) (v r)) r)
    (hs_mem : s ∈ Ioo a b) (ht_mem : t ∈ Ioo a b) :
    g (γ s) (v s) (v s) = g (γ t) (v t) (v t) := by
  have hd : ∀ r ∈ Ioo a b, HasDerivAt (fun q => g (γ q) (v q) (v q)) 0 r :=
    fun r hr => metric_speed_derivative (hg r hr) (hi r hr) (hs r hr)
      (hder r hr).1 (hder r hr).2
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs_mem ht_mem

end WeakMTWTransport

end

end OAI
