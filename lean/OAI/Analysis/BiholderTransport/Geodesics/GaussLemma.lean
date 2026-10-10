import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Coordinates
import OAI.Analysis.BiholderTransport.Calculus.PartialCalculus

namespace OAI

noncomputable section

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

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance gaussLemmaNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance gaussLemmaDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance gaussLemmaDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance gaussLemmaBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance gaussLemmaBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance gaussLemmaTrilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance gaussLemmaTrilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma metric_geodesic_variation_derivative {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {γ V J : ℝ → E} {t : ℝ} {W : E}
    (hg : DifferentiableAt ℝ g (γ t)) (hi : (g (γ t)).IsInvertible)
    (hγ : HasDerivAt γ (V t) t)
    (hV : HasDerivAt V (-coordinateChristoffel g (γ t) (V t) (V t)) t)
    (hJ : HasDerivAt J W t) :
    HasDerivAt (fun q => g (γ q) (V q) (J q))
      ((1/2:ℝ) * (fderiv ℝ g (γ t)) (J t) (V t) (V t) + g (γ t) (V t) W) t := by
  have h := ((hg.hasFDerivAt.comp_hasDerivAt t hγ).clm_apply hV).clm_apply hJ
  have hk := coordinateChristoffel_metric g (γ t) (V t) (V t) (J t) hi
  convert h using 1 <;> try rfl
  simp only [Function.comp_apply,add_apply,map_neg,neg_apply]
  linarith

lemma variation_mixed_derivative {A V : ℝ × ℝ → E} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hAV : ∀ z ∈ U, HasDerivAt (fun t => A (t,z.2)) (V z) z.1)
    {t s : ℝ} (hz : (t,s) ∈ U) :
    HasDerivAt (fun q => directionalDerivative A (0,1) (q,s))
      (directionalDerivative V (0,1) (t,s)) t := by
  have hAt := hA.contDiffAt (hU.mem_nhds hz)
  have heq : directionalDerivative A (1,0) =ᶠ[𝓝 (t,s)] V := by
    filter_upwards [hU.mem_nhds hz] with z hz
    exact (hasDerivAt_slice_left ((hA.contDiffAt (hU.mem_nhds hz)).differentiableAt
      (by simp))).unique (hAV z hz)
  have hm := directionalDerivative_commute hAt (0,1) (1,0)
  have heval : directionalDerivative (directionalDerivative A (1,0)) (0,1) (t,s) =
      directionalDerivative V (0,1) (t,s) := by
    unfold directionalDerivative
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] E => L (0,1)) heq.fderiv_eq
  rw [heval] at hm
  exact hm ▸ hasDerivAt_slice_left
    ((contDiffAt_directionalDerivative hAt (0,1)).differentiableAt (by simp))

lemma coordinate_gauss_variation
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hi : ∀ x ∈ S, (g x).IsInvertible)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {A V : ℝ × ℝ → E} {a b c d : ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo a b ×ˢ Ioo c d))
    (hV : ContDiffOn ℝ ∞ V (Ioo a b ×ˢ Ioo c d))
    (himg : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c d, A (t,s) ∈ S)
    (hode : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c d,
      HasDerivAt (fun q => A (q,s)) (V (t,s)) t ∧
      HasDerivAt (fun q => V (q,s))
        (-coordinateChristoffel g (A (t,s)) (V (t,s)) (V (t,s))) t)
    {x : E} {ν : ℝ → E}
    (h0 : 0 ∈ Ioo a b) (hA0 : ∀ s ∈ Ioo c d, A (0,s) = x)
    (hV0 : ∀ s ∈ Ioo c d, V (0,s) = ν s)
    {s t : ℝ} {w : E} (ht : t ∈ Ioo a b) (hs : s ∈ Ioo c d)
    (hν : HasDerivAt ν w s) :
    g (A (t,s)) (V (t,s)) (directionalDerivative A (0,1) (t,s)) =
      t * g x (ν s) w := by
  have hopen : IsOpen (Ioo a b ×ˢ Ioo c d) := isOpen_Ioo.prod isOpen_Ioo
  have hgd : ∀ q ∈ Ioo a b, ∀ r ∈ Ioo c d, DifferentiableAt ℝ g (A (q,r)) :=
    fun q hq r hr => (hg.contDiffAt (hS.mem_nhds (himg q hq r hr))).differentiableAt
      (by simp)
  have he : ∀ q ∈ Ioo a b, ∀ r ∈ Ioo c d,
      g (A (q,r)) (V (q,r)) (V (q,r)) = g x (ν r) (ν r) := by
    intro q hq r hr
    have hh := coordinate_geodesic_speed_constant
      (fun p hp => hgd p hp r hr) (fun p hp => hi _ (himg p hp r hr))
      (fun p hp => hsym _ (himg p hp r hr)) (fun p hp => hode p hp r hr) hq h0
    simpa only [hA0 r hr,hV0 r hr] using hh
  have hder : ∀ q ∈ Ioo a b,
      HasDerivAt (fun p => g (A (p,s)) (V (p,s))
        (directionalDerivative A (0,1) (p,s))) (g x (ν s) w) q := by
    intro q hq
    let J := directionalDerivative A (0,1) (q,s)
    let W := directionalDerivative V (0,1) (q,s)
    have hAr := hasDerivAt_slice_right
      ((hA.contDiffAt (hopen.mem_nhds ⟨hq,hs⟩)).differentiableAt (by simp))
    have hVr := hasDerivAt_slice_right
      ((hV.contDiffAt (hopen.mem_nhds ⟨hq,hs⟩)).differentiableAt (by simp))
    have hE := (((hgd q hq s hs).hasFDerivAt.comp_hasDerivAt s hAr).clm_apply hVr).clm_apply hVr
    have hE0 := ((hasDerivAt_const s (g x)).clm_apply hν).clm_apply hν
    have heq : (fun r => g (A (q,r)) (V (q,r)) (V (q,r))) =ᶠ[𝓝 s]
        (fun r => g x (ν r) (ν r)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact he q hq r hr
    have hval := (hE.congr_of_eventuallyEq heq.symm).unique hE0
    have hJ := variation_mixed_derivative hopen hA
      (fun z hz => (hode z.1 hz.1 z.2 hz.2).1) (hz := ⟨hq,hs⟩)
    have hG := metric_geodesic_variation_derivative
      (γ := fun p => A (p,s)) (V := fun p => V (p,s))
      (J := fun p => directionalDerivative A (0,1) (p,s)) (hgd q hq s hs)
      (hi _ (himg q hq s hs)) (hode q hq s hs).1 (hode q hq s hs).2 hJ
    have hval' : (1/2:ℝ) * (fderiv ℝ g (A (q,s))) J (V (q,s)) (V (q,s)) +
        g (A (q,s)) (V (q,s)) W = g x (ν s) w := by
      simp only [Function.comp_apply,add_apply,zero_apply,zero_add] at hval
      rw [hsym _ (himg q hq s hs) W (V (q,s)),
        hsym x (hA0 s hs ▸ himg 0 h0 s hs) w (ν s)] at hval
      linarith
    exact hval' ▸ hG
  have hJ0 : directionalDerivative A (0,1) (0,s) = 0 := by
    have hAr := hasDerivAt_slice_right
      ((hA.contDiffAt (hopen.mem_nhds ⟨h0,hs⟩)).differentiableAt (by simp))
    have heq : (fun r => A (0,r)) =ᶠ[𝓝 s] (fun _ => x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact hA0 r hr
    exact (hAr.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const s x)
  have hd : ∀ q ∈ Ioo a b,
      HasDerivAt (fun p => g (A (p,s)) (V (p,s))
        (directionalDerivative A (0,1) (p,s)) - p * g x (ν s) w) 0 q := by
    intro q hq
    convert (hder q hq).sub ((hasDerivAt_id q).mul_const (g x (ν s) w)) using 1 <;>
      first | rfl | simp only [one_mul,sub_self]
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun q hq => (hd q hq).differentiableAt.differentiableWithinAt)
    (fun q hq => (hd q hq).deriv) ht h0
  simpa only [hJ0,map_zero,zero_mul,sub_zero,sub_eq_zero] using heq

end WeakMTWTransport

end

end OAI
