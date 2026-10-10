import Mathlib

namespace OAI

/-! Combine the finitely many crossing adjustments on pairwise disjoint
neighborhoods. The patched field agrees exactly with the selected local field. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.VelocityFrame
variable {E F ι : Type*}

def finiteDisjointAdjustment [AddCommGroup F] (s : Finset ι) (n : E → F) (g : ι → E → F) : E → F :=
  fun x => n x + ∑ i ∈ s, (g i x - n x)

lemma finiteDisjointAdjustment_smoothOn
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Finset ι} {n : E → F}
    {g : ι → E → F} {U : Set E} (hn : ContDiffOn ℝ ∞ n U)
    (hg : ∀ i ∈ s, ContDiffOn ℝ ∞ (g i) U) :
    ContDiffOn ℝ ∞ (finiteDisjointAdjustment s n g) U := by
  exact hn.add (ContDiffOn.sum fun i hi => (hg i hi).sub hn)

lemma finiteDisjointAdjustment_of_mem [AddCommGroup F] [DecidableEq ι] {s : Finset ι} {n : E → F}
    {g : ι → E → F} {O : ι → Set E}
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (O i) (O j))
    (hext : ∀ i ∈ s, ∀ x ∉ O i, g i x = n x)
    {i : ι} (hi : i ∈ s) {x : E} (hx : x ∈ O i) :
    finiteDisjointAdjustment s n g x = g i x := by
  have hz : ∀ j ∈ s, j ≠ i → g j x-n x = 0 := by
    intro j hj hji
    apply sub_eq_zero.mpr
    apply hext j hj x
    intro hxj
    exact Set.disjoint_left.mp (hdisj hj hi hji) hxj hx
  unfold finiteDisjointAdjustment
  rw [Finset.sum_eq_single i (fun j hj hji => hz j hj hji) (by simp [hi])]
  abel

lemma finiteDisjointAdjustment_of_exterior [AddCommGroup F] {s : Finset ι} {n : E → F}
    {g : ι → E → F} {O : ι → Set E}
    (hext : ∀ i ∈ s, ∀ x ∉ O i, g i x = n x)
    {x : E} (hx : ∀ i ∈ s, x ∉ O i) :
    finiteDisjointAdjustment s n g x = n x := by
  unfold finiteDisjointAdjustment
  have hz : ∑ i ∈ s, (g i x-n x) = 0 := Finset.sum_eq_zero fun i hi => by
    rw [hext i hi x (hx i hi),sub_self]
  rw [hz,add_zero]

lemma finiteDisjointAdjustment_property [AddCommGroup F] [DecidableEq ι] {s : Finset ι} {n : E → F}
    {g : ι → E → F} {O : ι → Set E} {U : Set E} {P : E → F → Prop}
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (O i) (O j))
    (hext : ∀ i ∈ s, ∀ x ∉ O i, g i x = n x)
    (hn : ∀ x ∈ U, P x (n x))
    (hg : ∀ i ∈ s, ∀ x ∈ U ∩ O i, P x (g i x)) :
    ∀ x ∈ U, P x (finiteDisjointAdjustment s n g x) := by
  intro x hx
  by_cases hex : ∃ i ∈ s, x ∈ O i
  · obtain ⟨i,hi,hxi⟩ := hex
    rw [finiteDisjointAdjustment_of_mem hdisj hext hi hxi]
    exact hg i hi x ⟨hx,hxi⟩
  · have hout : ∀ i ∈ s, x ∉ O i := by
      intro i hi hxi
      exact hex ⟨i,hi,hxi⟩
    rw [finiteDisjointAdjustment_of_exterior hext hout]
    exact hn x hx

end ClosedSurfaceR4.VelocityFrame

end

end OAI
