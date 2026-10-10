import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Closed convex hulls of decreasing weakly compact sets

All closures of convex hulls below are taken in the original norm topology.
The compact sets themselves live in the distinct weak copy.  A continuous
linear functional attains a maximum on each compact set.  Nested compact
half-space cuts then supply a point of the intersection with at least the
value of the proposed anchor.  Hahn--Banach separation proves membership
in the norm-closed convex hull of that intersection.
-/

noncomputable section

open Set Topology

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The scalar evaluations separate points of the actual weak copy. -/
private theorem weakCopy_t2Space : T2Space (WeakSpace ℝ X) := by
  apply T2Space.of_injective_continuous
    (f := fun z : WeakSpace ℝ X =>
      fun f : X →L[ℝ] ℝ => f ((toWeakSpace ℝ X).symm z))
  · intro z w h
    apply (toWeakSpace ℝ X).symm.injective
    by_contra hne
    obtain ⟨f, hf⟩ := geometric_hahn_banach_point_point hne
    exact hf.ne (congrFun h f)
  · exact WeakBilin.coeFn_continuous (topDualPairing ℝ X).flip

/-- A decreasing sequence of nonempty weakly compact sets has nonempty
compact intersection.  No completeness assumption on the normed space is
needed. -/
theorem weaklyCompact_iInter_nonempty_compact
    (B : ℕ → Set (WeakSpace ℝ X))
    (hBc : ∀ n, IsCompact (B n)) (hBn : ∀ n, (B n).Nonempty)
    (hBanti : Antitone B) :
    (⋂ n, B n).Nonempty ∧ IsCompact (⋂ n, B n) := by
  let : T2Space (WeakSpace ℝ X) := weakCopy_t2Space
  refine ⟨?_, ?_⟩
  · exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      B hBanti.directed_ge hBn hBc (fun n => (hBc n).isClosed)
  · exact (hBc 0).of_isClosed_subset
      (isClosed_iInter fun n => (hBc n).isClosed) (iInter_subset B 0)

/-- A functional's maximum over a nonempty weakly compact set bounds its
value on the norm-closed convex hull. -/
theorem exists_dual_ge_of_mem_closure_convexHull_weaklyCompact
    (B : Set (WeakSpace ℝ X)) (hBc : IsCompact B) (hBn : B.Nonempty)
    {x : X} (hx : x ∈ closure (convexHull ℝ ((toWeakSpace ℝ X) ⁻¹' B)))
    (f : X →L[ℝ] ℝ) :
    ∃ z ∈ B, f x ≤ f ((toWeakSpace ℝ X).symm z) := by
  let F : WeakSpace ℝ X → ℝ := fun z => f ((toWeakSpace ℝ X).symm z)
  have hF : Continuous F := WeakBilin.eval_continuous (topDualPairing ℝ X).flip f
  obtain ⟨z, hz, hzmax⟩ := hBc.exists_isMaxOn hBn hF.continuousOn
  refine ⟨z, hz, ?_⟩
  have hbound : closure (convexHull ℝ ((toWeakSpace ℝ X) ⁻¹' B)) ⊆
      {y : X | f y ≤ f ((toWeakSpace ℝ X).symm z)} := by
    apply closure_minimal
    · apply convexHull_min
      · intro y hy
        have h : F ((toWeakSpace ℝ X) y) ≤ F z := hzmax hy
        change f y ≤ f ((toWeakSpace ℝ X).symm z)
        simpa only [F, LinearEquiv.symm_apply_apply] using h
      · exact (convex_Iic (f ((toWeakSpace ℝ X).symm z))).linear_preimage
          f.toLinearMap
    · exact isClosed_le f.continuous continuous_const
  exact hbound hx

/-- A point in the norm-closed convex hull of every decreasing nonempty
weakly compact set belongs to the norm-closed convex hull of their
intersection.  Compactness, rather than a general interchange law for
convex hulls and intersections, supplies the crucial step. -/
theorem mem_closure_convexHull_iInter_weaklyCompact
    (B : ℕ → Set (WeakSpace ℝ X))
    (hBc : ∀ n, IsCompact (B n)) (hBn : ∀ n, (B n).Nonempty)
    (hBanti : Antitone B) {x : X}
    (hx : ∀ n, x ∈ closure (convexHull ℝ ((toWeakSpace ℝ X) ⁻¹' B n))) :
    x ∈ closure (convexHull ℝ ((toWeakSpace ℝ X) ⁻¹' (⋂ n, B n))) := by
  let : T2Space (WeakSpace ℝ X) := weakCopy_t2Space
  by_contra hxout
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ ((toWeakSpace ℝ X) ⁻¹' (⋂ n, B n))).closure
    isClosed_closure hxout
  let F : WeakSpace ℝ X → ℝ := fun z => f ((toWeakSpace ℝ X).symm z)
  have hF : Continuous F := WeakBilin.eval_continuous (topDualPairing ℝ X).flip f
  let C : ℕ → Set (WeakSpace ℝ X) := fun n => B n ∩ {z | f x ≤ F z}
  have hCc (n : ℕ) : IsCompact (C n) :=
    (hBc n).inter_right (isClosed_le continuous_const hF)
  have hCn (n : ℕ) : (C n).Nonempty := by
    obtain ⟨z, hz, hzx⟩ :=
      exists_dual_ge_of_mem_closure_convexHull_weaklyCompact (B n) (hBc n) (hBn n)
        (hx n) f
    exact ⟨z, hz, hzx⟩
  have hCanti : Antitone C := by
    intro m n hmn z hz
    exact ⟨hBanti hmn hz.1, hz.2⟩
  obtain ⟨⟨z, hz⟩, _⟩ := weaklyCompact_iInter_nonempty_compact C hCc hCn hCanti
  have hzB : z ∈ ⋂ n, B n := mem_iInter.mpr fun n => (mem_iInter.mp hz n).1
  have hzD : (toWeakSpace ℝ X).symm z ∈
      closure (convexHull ℝ ((toWeakSpace ℝ X) ⁻¹' (⋂ n, B n))) := by
    apply subset_closure
    apply subset_convexHull
    simpa only [mem_preimage, LinearEquiv.apply_symm_apply] using hzB
  have hzx : f x ≤ f ((toWeakSpace ℝ X).symm z) := (mem_iInter.mp hz 0).2
  exact not_le_of_gt (hux.trans_le hzx) (hfu _ hzD).le

end ReflexiveFixedPoints

end

end OAI
