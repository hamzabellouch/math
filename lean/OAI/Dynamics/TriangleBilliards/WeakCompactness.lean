import OAI.Dynamics.TriangleBilliards.RegularizedModes

namespace OAI

universe uAlpha uBeta uE uF uIota uKappa

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section

open Filter Set
open scoped Topology

noncomputable section

namespace TriangularBilliards.Analytic

section Weak

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α : Type uAlpha} {l : Filter α}

/-- Scalar-test characterization of weak convergence over the real field. -/
def WeaklyTendsto (u : α → E) (l : Filter α) (v : E) : Prop :=
  ∀ L : E →L[ℝ] ℝ, Tendsto (fun n => L (u n)) l (𝓝 (L v))

lemma weaklyTendsto_of_tendsto {u : α → E} {v : E}
    (h : Tendsto u l (𝓝 v)) : WeaklyTendsto u l v :=
  fun L => L.continuous.continuousAt.tendsto.comp h

lemma WeaklyTendsto.comp {u : α → E} {v : E} (h : WeaklyTendsto u l v)
    {β : Type uBeta} {m : Filter β} {φ : β → α} (hφ : Tendsto φ m l) :
    WeaklyTendsto (u ∘ φ) m v :=
  fun L => (h L).comp hφ

lemma WeaklyTendsto.prod {u : α → E} {v : α → F} {a : E} {b : F}
    (hu : WeaklyTendsto u l a) (hv : WeaklyTendsto v l b) :
    WeaklyTendsto (fun n => (u n, v n)) l (a, b) := by
  intro L
  have h := (hu (L.comp (ContinuousLinearMap.inl ℝ E F))).add
    (hv (L.comp (ContinuousLinearMap.inr ℝ E F)))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← map_add, Prod.add_def, add_zero, zero_add] using h

lemma WeaklyTendsto.sub_const {u : α → E} {v : E}
    (h : WeaklyTendsto u l v) (w : E) :
    WeaklyTendsto (fun n => u n - w) l (v - w) := by
  intro L
  simpa only [map_sub] using (h L).sub_const (L w)

/-- Norm-closed convex sets remain closed under weak limits. In particular
this applies to a uniform L∞ bound inside L² and to a closed derivative graph. -/
lemma WeaklyTendsto.mem_of_closed_convex [l.NeBot] {u : α → E} {v : E}
    (h : WeaklyTendsto u l v) {C : Set E} (hc : IsClosed C) (hcv : Convex ℝ C)
    (hu : ∀ᶠ n in l, u n ∈ C) : v ∈ C := by
  by_contra hn
  obtain ⟨L, t, hC, hv⟩ := geometric_hahn_banach_closed_point hcv hc hn
  have hle : L v ≤ t := le_of_tendsto (h L) (hu.mono fun n hn => (hC _ hn).le)
  exact (not_le_of_gt hv) hle

lemma WeaklyTendsto.norm_le [l.NeBot] {u : α → E} {v : E}
    (h : WeaklyTendsto u l v) {r : ℝ} (hu : ∀ᶠ n in l, ‖u n‖ ≤ r) : ‖v‖ ≤ r := by
  have hv := h.mem_of_closed_convex Metric.isClosed_closedBall (convex_closedBall (0 : E) r)
    (hu.mono fun n hn => (mem_closedBall_zero_iff).mpr hn)
  exact mem_closedBall_zero_iff.mp hv

lemma WeaklyTendsto.norm_le_of_bounds [l.NeBot] {u : α → E} {v : E}
    (h : WeaklyTendsto u l v) {r : α → ℝ} {R : ℝ}
    (hr : Tendsto r l (𝓝 R)) (hu : ∀ᶠ n in l, ‖u n‖ ≤ r n) : ‖v‖ ≤ R := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply h.norm_le
  filter_upwards [hu, hr.eventually (gt_mem_nhds (show R < R + ε by linarith))]
    with n hn hrn
  exact hn.trans hrn.le

end Weak

section Hilbert

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

/-- Weak sequential compactness of a bounded set in a separable real Hilbert
space, obtained from Banach–Alaoglu and Riesz. -/
lemma exists_weak_subsequence (u : ℕ → E) {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ v : E, ‖v‖ ≤ R ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeaklyTendsto (u ∘ φ) atTop v := by
  let J := InnerProductSpace.toDual ℝ E
  let w : ℕ → WeakDual ℝ E := fun n => StrongDual.toWeakDual (J (u n))
  have hw : ∀ n, w n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) R := by
    intro n
    change dist (J (u n)) 0 ≤ R
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E 0 R) hw
  let v : E := J.symm (WeakDual.toStrongDual a)
  have hv : ‖v‖ ≤ R := by
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, v,
      LinearIsometryEquiv.norm_map] using ha
  refine ⟨v, hv, φ, hφ, ?_⟩
  intro L
  let x : E := J.symm L
  have heq (y : E) : (J y) x = L y := by
    change inner ℝ y (J.symm L) = L y
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have heqa : a x = L v := by
    change (WeakDual.toStrongDual a) x = L v
    have hj : J v = WeakDual.toStrongDual a := J.apply_symm_apply _
    rw [← hj, heq]
  have h := (WeakDual.eval_continuous x).continuousAt.tendsto.comp hlim
  change Tendsto (fun n => (J (u (φ n))) x) atTop (𝓝 (a x)) at h
  simpa only [heq, heqa, Function.comp_apply] using h

end Hilbert

section DerivativeGraph

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A distributional graph described by test identities. Instantiating it
with weak differentiation requires constructing its actual test functionals. -/
def TestGraph {ι : Type uIota} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ) : Set (E × F) :=
  {p | ∀ i, A i p.1 = B i p.2}

lemma testGraph_closed {ι : Type uIota} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ) :
    IsClosed (TestGraph A B) := by
  have h : TestGraph A B = ⋂ i, {p : E × F | A i p.1 = B i p.2} := by
    ext p
    simp only [TestGraph, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun i => isClosed_eq ((A i).continuous.comp continuous_fst)
    ((B i).continuous.comp continuous_snd)

lemma testGraph_convex {ι : Type uIota} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ) :
    Convex ℝ (TestGraph A B) := by
  intro p hp q hq a b _ _ _ i
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    map_add, map_smul, hp i, hq i]

/-- Identifying the weak derivative limit uses only test identities, not
an unjustified claim that the entire horizontal derivative lies in L². -/
lemma testGraph_weak_limit {ι : Type uIota} {α : Type uAlpha} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ)
    {l : Filter α} [l.NeBot] {u : α → E} {d : α → F} {v : E} {e : F}
    (hu : WeaklyTendsto u l v) (hd : WeaklyTendsto d l e)
    (hgraph : ∀ᶠ n in l, (u n, d n) ∈ TestGraph A B) : (v, e) ∈ TestGraph A B :=
  (hu.prod hd).mem_of_closed_convex (testGraph_closed A B) (testGraph_convex A B) hgraph

end DerivativeGraph

section TestGraphLimits

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [TopologicalSpace.SeparableSpace F]

omit [CompleteSpace F] [TopologicalSpace.SeparableSpace F] in
lemma testGraph_unique {ι : Type uIota} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ)
    (hsep : ∀ v : F, (∀ i, B i v = 0) → v = 0)
    {u : E} {d e : F} (hd : (u, d) ∈ TestGraph A B) (he : (u, e) ∈ TestGraph A B) :
    d = e := by
  apply sub_eq_zero.mp
  apply hsep
  intro i
  rw [map_sub, ← hd i, ← he i, sub_self]

/-- The second-limit step: strong convergence of the functions and a
uniform bound for only the relevant derivatives suffice to pass a fixed
pairing to the limit. There is no bound for the sum of all mode derivatives. -/
lemma testGraph_pairing_of_strong_limit {ι : Type uIota}
    (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ)
    (hsep : ∀ v : F, (∀ i, B i v = 0) → v = 0)
    (u : ℕ → E) (d : ℕ → F) {f : E} {e : F} {R : ℝ}
    (hgraph : ∀ n, (u n, d n) ∈ TestGraph A B)
    (hf : (f, e) ∈ TestGraph A B)
    (hu : Tendsto u atTop (𝓝 f)) (hd : ∀ n, ‖d n‖ ≤ R)
    (L : F →L[ℝ] ℝ) (hL : Tendsto (fun n => L (d n)) atTop (𝓝 0)) : L e = 0 := by
  obtain ⟨e', _, φ, hφ, he'⟩ := exists_weak_subsequence d hd
  have hfu := (weaklyTendsto_of_tendsto hu).comp hφ.tendsto_atTop
  have hfe' : (f, e') ∈ TestGraph A B :=
    testGraph_weak_limit A B hfu he' (Eventually.of_forall fun n => hgraph (φ n))
  have heq := testGraph_unique A B hsep hfe' hf
  have hzero : L e' = 0 := tendsto_nhds_unique (he' L) (hL.comp hφ.tendsto_atTop)
  simpa only [heq] using hzero

end TestGraphLimits

section FirstLimit

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
  [CompleteSpace F] [TopologicalSpace.SeparableSpace F]

/-- The fixed-clearance-budget weak limit. The derivative bound `M` is
allowed to depend on that fixed budget. An application must supply all
smoothing, support, transport and distributional-graph properties; this
lemma supplies the two subsequence extractions and all limit passages. -/
lemma testGraph_first_limit {ι : Type uIota} {κ : Type uKappa}
    (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ) (X : κ → E →L[ℝ] ℝ)
    (C : Set E) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (u : ℕ → E) (d : ℕ → F) {f : E} {H M δ : ℝ} (δn : ℕ → ℝ)
    (hu : ∀ n, ‖u n‖ ≤ H) (hd : ∀ n, ‖d n‖ ≤ M)
    (hC : ∀ n, u n ∈ C) (hgraph : ∀ n, (u n, d n) ∈ TestGraph A B)
    (hX : ∀ k, Tendsto (fun n => X k (u n)) atTop (𝓝 0))
    (hδn : Tendsto δn atTop (𝓝 δ)) (hclose : ∀ n, ‖u n - f‖ ≤ δn n)
    (L : F →L[ℝ] ℝ) (hL : Tendsto (fun n => L (d n)) atTop (𝓝 0)) :
    ∃ g : E, ∃ e : F,
      g ∈ C ∧ (∀ k, X k g = 0) ∧ ‖g - f‖ ≤ δ ∧ (g, e) ∈ TestGraph A B ∧ L e = 0 := by
  obtain ⟨g, _, φ, hφ, hg⟩ := exists_weak_subsequence u hu
  obtain ⟨e, _, ψ, hψ, he⟩ := exists_weak_subsequence (d ∘ φ) (fun n => hd (φ n))
  have hw : WeaklyTendsto (u ∘ φ ∘ ψ) atTop g := hg.comp hψ.tendsto_atTop
  have hφψ : Tendsto (φ ∘ ψ) atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  refine ⟨g, e, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw.mem_of_closed_convex hCclosed hCconvex
      (Eventually.of_forall fun n => hC (φ (ψ n)))
  · intro k
    exact tendsto_nhds_unique (hw (X k)) ((hX k).comp hφψ)
  · exact (hw.sub_const f).norm_le_of_bounds (hδn.comp hφψ)
      (Eventually.of_forall fun n => hclose (φ (ψ n)))
  · exact testGraph_weak_limit A B hw he
      (Eventually.of_forall fun n => hgraph (φ (ψ n)))
  · exact tendsto_nhds_unique (he L) (hL.comp hφψ)

end FirstLimit

end TriangularBilliards.Analytic

namespace TriangularBilliards.Analytic

lemma exists_weak_subsequence_unrestricted
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : ℕ → E) {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ v : E, ‖v‖ ≤ R ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeaklyTendsto (u ∘ φ) atTop v := by
  let S := (Submodule.span ℝ (Set.range u)).topologicalClosure
  have hS : TopologicalSpace.IsSeparable (S : Set E) :=
    ((Set.countable_range u).isSeparable.span (R := ℝ)).closure
  let : TopologicalSpace.SeparableSpace S := hS.separableSpace
  let w (n : ℕ) : S := ⟨u n, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self n))⟩
  obtain ⟨v,hv,φ,hφ,hw⟩ := exists_weak_subsequence w hu
  refine ⟨v.val,hv,φ,hφ,?_⟩
  intro L
  exact hw (L.comp S.subtypeL)

end TriangularBilliards.Analytic

end
end
end
end
end
end
end
end
end
end

end OAI
