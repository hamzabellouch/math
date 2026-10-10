import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.ImplicitNeighborhood
import OAI.Analysis.BiholderTransport.Geodesics.GaussLemma

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

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma coordinate_endpoint_gauss
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hi : ∀ x ∈ S, (g x).IsInvertible)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {Ψ W : ℝ × E → E} {a b R : ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo a b ×ˢ Metric.ball 0 R))
    (hW : ContDiffOn ℝ ∞ W (Ioo a b ×ˢ Metric.ball 0 R))
    (himg : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {x : E} (h0 : 0 ∈ Ioo a b)
    (hΨ0 : ∀ v ∈ Metric.ball 0 R, Ψ (0,v) = x)
    (hW0 : ∀ v ∈ Metric.ball 0 R, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo a b) {v : E} (hv : v ∈ Metric.ball 0 R) (w : E) :
    g (Ψ (τ,v)) (W (τ,v)) ((fderiv ℝ (fun z => Ψ (τ,z)) v) w) = τ * g x v w := by
  have hνc : ContinuousAt (fun s : ℝ => v + s • w) 0 := by fun_prop
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, v + s • w ∈ Metric.ball 0 R :=
    hνc (by simpa only [zero_smul,add_zero] using Metric.isOpen_ball.mem_nhds hv)
  obtain ⟨δ,hd,hδ⟩ := Metric.mem_nhds_iff.mp hnear
  have hνmem : ∀ s ∈ Ioo (-δ) δ, v + s • w ∈ Metric.ball 0 R := by
    intro s hs
    exact hδ (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using abs_lt.mpr hs)
  let A : ℝ × ℝ → E := fun z => Ψ (z.1,v + z.2 • w)
  let V : ℝ × ℝ → E := fun z => W (z.1,v + z.2 • w)
  have hA : ContDiffOn ℝ ∞ A (Ioo a b ×ˢ Ioo (-δ) δ) :=
    hΨ.comp (contDiffOn_fst.prodMk (contDiffOn_const.add
      (contDiffOn_snd.smul contDiffOn_const))) (fun z hz => ⟨hz.1,hνmem z.2 hz.2⟩)
  have hV : ContDiffOn ℝ ∞ V (Ioo a b ×ˢ Ioo (-δ) δ) :=
    hW.comp (contDiffOn_fst.prodMk (contDiffOn_const.add
      (contDiffOn_snd.smul contDiffOn_const))) (fun z hz => ⟨hz.1,hνmem z.2 hz.2⟩)
  have hs0 : (0:ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hd,hd⟩
  have hν : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    convert ((hasDerivAt_id (0:ℝ)).smul_const w).const_add v using 1 <;>
      first | rfl | simp only [one_smul]
  have hG := coordinate_gauss_variation hS hg hi hsym hA hV
    (fun t ht s hs => himg t ht (v+s•w) (hνmem s hs))
    (fun t ht s hs => hode t ht (v+s•w) (hνmem s hs))
    h0 (fun s hs => hΨ0 (v+s•w) (hνmem s hs))
    (fun s hs => hW0 (v+s•w) (hνmem s hs)) hτ hs0 hν
  have hψd : DifferentiableAt ℝ (fun z => Ψ (τ,z)) v :=
    ((hΨ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hτ,hv⟩)).comp v
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hψder := (show HasFDerivAt (fun z => Ψ (τ,z))
      (fderiv ℝ (fun z => Ψ (τ,z)) v) (v+(0:ℝ)•w) by
    simpa only [zero_smul,add_zero] using hψd.hasFDerivAt).comp_hasDerivAt 0 hν
  have hAr := hasDerivAt_slice_right ((hA.contDiffAt
    ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hτ,hs0⟩)).differentiableAt (by simp))
  have hJ : directionalDerivative A (0,1) (τ,0) =
      (fderiv ℝ (fun z => Ψ (τ,z)) v) w := hAr.unique hψder
  simpa only [A,V,zero_smul,add_zero,hJ] using hG

omit [FiniteDimensional ℝ E] in
lemma coordinate_geodesic_zero_velocity
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {γ V : ℝ → E} {a b : ℝ}
    (hg : ∀ t ∈ Ioo a b, DifferentiableAt ℝ g (γ t))
    (hi : ∀ t ∈ Ioo a b, (g (γ t)).IsInvertible)
    (hpos : ∀ t ∈ Ioo a b, ∀ w : E, w ≠ 0 → 0 < g (γ t) w w)
    (hsym : ∀ t ∈ Ioo a b, ∀ u v, g (γ t) u v = g (γ t) v u)
    (hode : ∀ t ∈ Ioo a b, HasDerivAt γ (V t) t ∧
      HasDerivAt V (-coordinateChristoffel g (γ t) (V t) (V t)) t)
    {s : ℝ} (hs : s ∈ Ioo a b) (hVs : V s = 0) {t : ℝ} (ht : t ∈ Ioo a b) :
    γ t = γ s ∧ V t = 0 := by
  have hVz : ∀ q ∈ Ioo a b, V q = 0 := by
    intro q hq
    have h := coordinate_geodesic_speed_constant hg hi hsym hode hq hs
    simp only [hVs,map_zero] at h
    by_contra hn
    exact (ne_of_gt (hpos q hq _ hn)) h
  refine ⟨?_,hVz t ht⟩
  apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun q hq => (hode q hq).1.differentiableAt.differentiableWithinAt) _ ht hs
  intro q hq
  exact (hode q hq).1.deriv.trans (hVz q hq)

end

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
lemma exists_smooth_local_diffeomorphism {f : Y → Y} {S : Set Y}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) {a : Y} (ha : a ∈ S)
    (hi : (fderiv ℝ f a).IsInvertible) :
    ∃ e : OpenPartialHomeomorph Y Y, (e : Y → Y) = f ∧ a ∈ e.source ∧
      e.source ⊆ S ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hfa : ContDiffAt ℝ ∞ f a := hf.contDiffAt (hS.mem_nhds ha)
  obtain ⟨L,hL⟩ := hi
  have hder : HasFDerivAt f (L : Y →L[ℝ] Y) a :=
    hL ▸ (hfa.differentiableAt (by simp)).hasFDerivAt
  let e := hfa.toOpenPartialHomeomorph f hder (by simp)
  have hea : a ∈ e.source := hfa.mem_toOpenPartialHomeomorph_source hder (by simp)
  have hfc : ContinuousAt (fderiv ℝ f) a :=
    (hf.continuousOn_fderiv_of_isOpen hS (by simp) a ha).continuousAt (hS.mem_nhds ha)
  have hev : ∀ᶠ y in 𝓝 a, y ∈ S ∧ (fderiv ℝ f y).IsInvertible :=
    (show ∀ᶠ y in 𝓝 a, y ∈ S from hS.mem_nhds ha).and
      (hfc (isOpen_invertible_endomorphism.mem_nhds ⟨L,hL⟩))
  obtain ⟨U,hUsub,hU,haU⟩ := mem_nhds_iff.mp hev
  let d := e.restrOpen U hU
  have hdf : (d : Y → Y) = f := rfl
  have hdsub : d.source ⊆ S := fun _ hz => (hUsub hz.2).1
  refine ⟨d,hdf,⟨hea,haU⟩,hdsub,?_,?_⟩
  · simpa only [hdf] using hf.mono hdsub
  · intro z hz
    have hy := d.map_target hz
    have hfy : ContDiffAt ℝ ∞ f (d.symm z) := hf.contDiffAt (hS.mem_nhds (hdsub hy))
    obtain ⟨A,hA⟩ := (hUsub hy.2).2
    have hdy : HasFDerivAt d (A : Y →L[ℝ] Y) (d.symm z) := by
      rw [hdf,hA]
      exact (hfy.differentiableAt (by simp)).hasFDerivAt
    exact (d.contDiffAt_symm hz hdy (by simpa only [hdf] using hfy)).contDiffWithinAt

end WeakMTWTransport

end

end OAI
