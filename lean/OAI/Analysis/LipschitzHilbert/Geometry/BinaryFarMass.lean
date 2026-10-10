import OAI.Analysis.LipschitzHilbert.Trees.BadStripMass
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! Finite binary stopping argument for the far-family mass. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert.SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

theorem binary_mass_bound (F : SelectedFarFamily ι) (leaf : ℝ)
    (hsmall : ∀ j ∈ F.members, 8*leaf ≤ (F.rectangles j).long) :
    ∀ n c l, 0 < l → l ≤ leaf*(2:ℝ)^n →
      stripMass F.rectangles (F.longMembers l) F.refRect c l ≤ 4*volume (F.refRect.stripSlab c l) →
      stripMass F.rectangles F.members F.refRect c l ≤ 10*volume (F.refRect.stripSlab c l) := by
  let good := fun n c l => l ≤ leaf*(2:ℝ)^n ∧
    stripMass F.rectangles (F.longMembers l) F.refRect c l ≤ 4*volume (F.refRect.stripSlab c l)
  have hzero : ∀ c l, 0 < l → good 0 c l →
      stripMass F.rectangles F.members F.refRect c l ≤ 10*volume (F.refRect.stripSlab c l) := by
    intro c l _ hg
    have hl : l ≤ leaf := by simpa only [pow_zero,mul_one] using hg.1
    have he : F.longMembers l = F.members := by
      apply Finset.filter_eq_self.mpr
      intro j hj
      exact le_trans (by linarith) (hsmall j hj)
    calc
      _ = stripMass F.rectangles (F.longMembers l) F.refRect c l := by rw [he]
      _ ≤ 4*volume (F.refRect.stripSlab c l) := hg.2
      _ ≤ _ := mul_le_mul' (by norm_num) le_rfl
  have hbad : ∀ n c l, 0 < l → good (n+1) c l → ∀ b,
      ¬good n (binaryChildCenter c l b) (l/2) →
      stripMass F.rectangles F.members F.refRect (binaryChildCenter c l b) (l/2) ≤
        10*volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) := by
    intro n c l hl hg b hb
    have hlength : l/2 ≤ leaf*(2:ℝ)^n := by
      have hh := hg.1
      rw [pow_succ] at hh
      linarith
    have hstrict : 4*volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) <
        stripMass F.rectangles (F.longMembers (l/2)) F.refRect (binaryChildCenter c l b) (l/2) := by
      apply lt_of_not_ge
      intro hm
      exact hb ⟨hlength,hm⟩
    have hdense : volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) ≤
        stripMass F.rectangles (F.longMembers (l/2)) F.refRect (binaryChildCenter c l b) (l/2) :=
      (show _ ≤ 4*volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) by
        calc
          _ = 1*volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) := (one_mul _).symm
          _ ≤ _ := mul_le_mul' (by norm_num) le_rfl).trans hstrict.le
    apply F.bad_strip_mass (binaryChildCenter c l b) (l/2) c (half_pos hl)
    · simpa only [show 2*(l/2)=l by ring] using stripSlab_child_subset F.refRect c l b
    · exact hdense
    · simpa only [show 2*(l/2)=l by ring] using hg.2
  have hbound := binary_density_bound (stripMass F.rectangles F.members F.refRect)
    (fun c l => volume (F.refRect.stripSlab c l)) 10 good
    (fun c l _ => stripMass_children F.rectangles F.members F.refRect c l)
    (fun c l _ => by
      have hh := F.refRect.intersection_stripSlab_children MeasurableSet.univ c l
      simpa only [univ_inter] using hh) hzero hbad
  intro n c l hl hlen hg
  exact hbound n c l hl ⟨hlen,hg⟩

/-- A finite far family has uniformly bounded mass in every strip whose
length is at least every member's length. -/
theorem strip_mass_bound (F : SelectedFarFamily ι) (c l : ℝ) (hl : 0 < l)
    (hmax : ∀ j ∈ F.members, (F.rectangles j).long ≤ l) :
    stripMass F.rectangles F.members F.refRect c l ≤ 10*volume (F.refRect.stripSlab c l) := by
  by_cases hn : F.members.Nonempty
  · obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image F.members (fun j => (F.rectangles j).long) hn
    let leaf := (F.rectangles j).long/8
    have hleaf : 0 < leaf := div_pos (F.rectangles j).long_pos (by norm_num)
    have hsmall : ∀ k ∈ F.members, 8*leaf ≤ (F.rectangles k).long := by
      intro k hk
      have hh := hmin k hk
      dsimp [leaf]
      linarith
    obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (l/leaf) (by norm_num : (1:ℝ) < 2)
    have hlen : l ≤ leaf*(2:ℝ)^N := by
      have hh := (div_lt_iff₀ hleaf).mp hN
      linarith
    have he : F.longMembers l = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hh := Finset.mem_filter.mp hk
      have hm := hmax k hh.1
      linarith
    apply F.binary_mass_bound leaf hsmall N c l hl hlen
    simp only [he,stripMass,Finset.sum_empty]
    exact zero_le
  · have he : F.members = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he,stripMass,Finset.sum_empty]
    exact zero_le

end LipschitzHilbert.SelectedFarFamily

end

end OAI
