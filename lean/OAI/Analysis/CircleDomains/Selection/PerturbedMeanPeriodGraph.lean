import OAI.Analysis.CircleDomains.Selection.MeanBranchAtlas
import OAI.Analysis.CircleDomains.Selection.MeanBranchTransitions
import OAI.Analysis.CircleDomains.Selection.PeriodDomainValues

namespace OAI

/-! Construction of the actual closed period-level graph from a compact
mean law and a shared bounded continuous smoothing correction. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem exists_perturbed_mean_period_graph
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (S U M : Set Sphere) (hS : IsOpen S) (hU : IsOpen U) (hM : IsClosed M)
    (b : Sphere) (hbS : b ∉ S) (hbU : b ∉ U) (hMS : M \ {b} ⊆ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val)
    (R : Sphere → ℝ) (hR : ContinuousOn R (U ∩ S)) (hRbound : ∀ x, |R x| ≤ 1) :
    ∃ (I : Type) (_ : Countable I) (V : I → Set Sphere) (a B : I → ℝ)
      (f : I → Sphere → ℝ),
      S ⊆ ⋃ i, V i ∧ (∀ i, IsOpen (V i) ∧ closure (V i) ⊆ S) ∧
      (∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i))) ∧
      (∀ i x, |f i x| ≤ B i) ∧ (∀ i, ContinuousOn (f i) (U ∩ V i)) ∧
      (∀ i x, x ∈ V i → f i x =
        meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + R x) ∧
      (∀ i j x, x ∈ V i → x ∈ V j →
        ∃ k : ℤ, f j =ᶠ[𝓝[U] x] fun y => f i y + k) ∧
      IsClosed (periodBandGraph U M b V f) ∧
      ∀ x ∈ U, ∀ θ : UnitAddCircle,
        (x, θ) ∈ periodBandGraph U M b V f ↔
          x ∈ M ∧ diskMeanCircle hsch K hKS η (F x) + (R x : UnitAddCircle) = θ := by
  obtain ⟨I, hI, V, a, B, u, hcover, hV, hlog, hbound, hcont, hu, hcircle⟩ :=
    exists_bounded_mean_branch_atlas hsch hsep K hK hKS η F S U hS h0 h1 hmiss
  let : Countable I := hI
  let f : I → Sphere → ℝ := fun i => localBranchRepresentative (V i) (fun x => u i x + R x)
  have hf (i : I) (x : Sphere) (hx : x ∈ V i) : f i x =
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + R x := by
    change (V i).indicator (fun y => u i y + R y) x = _
    rw [indicator_of_mem hx, hu i x hx]
  have hfb (i : I) (x : Sphere) : |f i x| ≤ B i + 1 := by
    have hB : 0 ≤ B i := (abs_nonneg (u i b)).trans (hbound i b)
    apply localBranchRepresentative_bound (D := univ) (by linarith : 0 ≤ B i + 1)
      (fun y _ => (abs_add_le (u i y) (R y)).trans (add_le_add (hbound i y) (hRbound y))) x (mem_univ x)
  have hfc (i : I) : ContinuousOn (f i) (U ∩ V i) := by
    apply localBranchRepresentative_continuousOn
    exact (hcont i).add (hR.mono (fun x hx => ⟨hx.1, (hV i).2 (subset_closure hx.2)⟩))
  have htrans (i j : I) (x : Sphere) (hi : x ∈ V i) (hj : x ∈ V j) :
      ∃ k : ℤ, f j =ᶠ[𝓝[U] x] fun y => f i y + k := by
    have hiC : ContinuousAt (fun y => logarithmicCutChart (a i) (F y)) x :=
      (hlog i).continuousAt (mem_of_superset ((hV i).1.mem_nhds hi) subset_closure)
    have hjC : ContinuousAt (fun y => logarithmicCutChart (a j) (F y)) x :=
      (hlog j).continuousAt (mem_of_superset ((hV j).1.mem_nhds hj) subset_closure)
    obtain ⟨k, hk⟩ := mean_logarithmic_branches_eventually_add_int hsch hsep K hK hKS η
      F (a i) (a j) x hiC hjC
    have heq : f j =ᶠ[𝓝 x] fun y => f i y + k := by
      filter_upwards [hk, (hV i).1.mem_nhds hi, (hV j).1.mem_nhds hj] with y hy hiy hjy
      rw [hf j y hjy, hf i y hiy, hy]
      ring
    exact ⟨k, heq.filter_mono nhdsWithin_le_nhds⟩
  have hbV (i : I) : b ∉ V i := fun hi => hbS ((hV i).2 (subset_closure hi))
  have hcoverM : M \ {b} ⊆ ⋃ i, V i := hMS.trans hcover
  refine ⟨I, hI, V, a, (fun i => B i + 1), f, hcover, hV, hlog, hfb, hfc, hf, htrans, ?_, ?_⟩
  · exact isClosed_periodBandGraph_of_integer_transitions U M hM b V
      (fun i => (hV i).1) hbV hcoverM f (fun i => B i + 1) (fun i x _ => hfb i x) htrans
  · intro x hx θ
    apply periodBandGraph_on_domain hU M b hbU V (fun i => (hV i).1) hcoverM f hfc
      (fun y => diskMeanCircle hsch K hKS η (F y) + (R y : UnitAddCircle)) _ hx θ
    intro i y hy
    change (((V i).indicator (fun z => u i z + R z) y : ℝ) : UnitAddCircle) = _
    rw [indicator_of_mem hy.2, AddCircle.coe_add, hcircle i y hy.2]

end CircleDomainRigidity

end

end OAI
