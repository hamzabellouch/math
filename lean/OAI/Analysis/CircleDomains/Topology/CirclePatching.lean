import OAI.Analysis.CircleDomains.Sobolev.CircleEnergy
import OAI.Analysis.CircleDomains.Selection.FinitePatching

namespace OAI

/-!
# Patching circle coordinates across filling disks

Real collar extensions project to genuine circle maps. Equality of the
projections on full boundary neighborhoods suffices for smooth patching;
global real branches on the retained region are unnecessary.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem smoothCircleOn_patchOpenRegions
    {I : Type*} [Fintype I] (D : I → Set (ℝ × ℝ))
    (hD : ∀ i, IsOpen (D i)) (hdisj : Pairwise (Disjoint on D))
    {Ω : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) → UnitAddCircle) (hf : SmoothCircleOn f (Ω \ ⋃ i, D i))
    (g : I → (ℝ × ℝ) → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hagree : ∀ i x, x ∈ Ω ∩ frontier (D i) →
      (fun y => (g i y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    SmoothCircleOn (patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f) Ω := by
  apply smoothCircleOn_iff_local_lifts.mpr
  intro x hx
  by_cases hm : ∃ i, x ∈ D i
  · obtain ⟨i, hi⟩ := hm
    exact ⟨g i, (hg i).contDiffAt,
      (patchOpenRegions_eventuallyEq_inside D (fun i x => (g i x : UnitAddCircle))
        f hD hdisj hi).symm⟩
  · have hpatch := patchOpenRegions_eventuallyEq_outside D
      (fun i x => (g i x : UnitAddCircle)) f hD (not_exists.mp hm)
      (fun i hi => hagree i x ⟨hx, hi⟩)
    obtain ⟨u, hu, hproj⟩ := smoothCircleOn_iff_local_lifts.mp hf x
      ⟨hx, fun hi => hm (mem_iUnion.mp hi)⟩
    exact ⟨u, hu, hproj.trans hpatch.symm⟩

theorem circleGradient_patchOpenRegions_inside
    {I : Type*} (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D))
    (f : (ℝ × ℝ) → UnitAddCircle)
    (g : I → (ℝ × ℝ) → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {i : I} {x : ℝ × ℝ} (hx : x ∈ D i) :
    circleGradient (patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f) x =
      planarGradient (g i) x := by
  have heq := patchOpenRegions_eventuallyEq_inside D
    (fun i x => (g i x : UnitAddCircle)) f hD hdisj hx
  have hc : ContinuousAt (patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f) x :=
    (((AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp
      (hg i).continuous.continuousAt).congr heq.symm)
  exact circleGradient_eq_lift hc (hg i).continuous.continuousAt heq.symm

theorem circleGradient_patchOpenRegions_outside
    {I : Type*} [Fintype I] (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (f : (ℝ × ℝ) → UnitAddCircle) (g : I → (ℝ × ℝ) → ℝ)
    {x : ℝ × ℝ} (hx : ∀ i, x ∉ D i)
    (hagree : ∀ i, x ∈ frontier (D i) →
      (fun y => (g i y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    circleGradient (patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f) x =
      circleGradient f x :=
  circleGradient_congr_of_eventuallyEq
    (patchOpenRegions_eventuallyEq_outside D (fun i x => (g i x : UnitAddCircle)) f hD hx hagree)

/-- Rank-one real extensions retain their zero-wedge property after
projection and patching into the original circle coordinates. -/
theorem circle_patch_wedges_eq_zero_inside
    {I L : Type*} (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D))
    (f : L → (ℝ × ℝ) → UnitAddCircle) (g : I → L → (ℝ × ℝ) → ℝ)
    (hg : ∀ i l, ContDiff ℝ ∞ (g i l))
    (hzero : ∀ i l m, l ≠ m → ∀ x ∈ D i,
      planarWedge (planarGradient (g i l) x) (planarGradient (g i m) x) = 0)
    {i : I} {x : ℝ × ℝ} (hx : x ∈ D i) (l m : L) (hlm : l ≠ m) :
    planarWedge
      (circleGradient (patchOpenRegions D (fun i x => (g i l x : UnitAddCircle)) (f l)) x)
      (circleGradient (patchOpenRegions D (fun i x => (g i m x : UnitAddCircle)) (f m)) x) = 0 := by
  rw [circleGradient_patchOpenRegions_inside D hD hdisj (f l) (fun i => g i l)
      (fun i => hg i l) hx,
    circleGradient_patchOpenRegions_inside D hD hdisj (f m) (fun i => g i m)
      (fun i => hg i m) hx]
  exact hzero i l m hlm x hx

end CircleDomainRigidity.FiniteTransfer

end

end OAI
