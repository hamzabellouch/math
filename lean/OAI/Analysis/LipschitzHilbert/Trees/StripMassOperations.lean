import OAI.Analysis.LipschitzHilbert.Estimates.StripSubdivision

namespace OAI

/-! Finite mass operations for the strip stopping argument. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*}

theorem stripSlab_mono_length (S : Rectangle) (c l l' : ℝ) (h : l ≤ l') :
    S.stripSlab c l ⊆ S.stripSlab c l' := by
  intro x hx
  have hx' := (S.mem_stripSlab c l x).mp hx
  exact (S.mem_stripSlab c l' x).mpr ⟨hx'.1.trans (by linarith),hx'.2⟩

theorem stripMass_mono_family (R : ι → Rectangle) (s t : Finset ι) (hst : s ⊆ t)
    (S : Rectangle) (c l : ℝ) : stripMass R s S c l ≤ stripMass R t S c l := by
  unfold stripMass
  exact Finset.sum_le_sum_of_subset hst

theorem stripMass_mono_region (R : ι → Rectangle) (s : Finset ι) (S : Rectangle)
    (c l c' l' : ℝ) (hsub : S.stripSlab c l ⊆ S.stripSlab c' l') :
    stripMass R s S c l ≤ stripMass R s S c' l' := by
  unfold stripMass
  apply Finset.sum_le_sum
  intro j _
  exact measure_mono (inter_subset_inter_right _ hsub)

theorem stripSlab_child_subset (S : Rectangle) (c l : ℝ) (b : Bool) :
    S.stripSlab (binaryChildCenter c l b) (l/2) ⊆ S.stripSlab c l := by
  rw [S.stripSlab_children c l]
  cases b
  · exact subset_union_left
  · exact subset_union_right

theorem stripMass_filter_meets (R : ι → Rectangle) (s : Finset ι) (S : Rectangle) (c l : ℝ) :
    stripMass R (s.filter (fun j => ((R j).carrier ∩ S.stripSlab c l).Nonempty)) S c l =
      stripMass R s S c l := by
  classical
  unfold stripMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · rfl
  · rw [Set.not_nonempty_iff_eq_empty.mp hj,measure_empty]

theorem stripMass_filter_zero (R : ι → Rectangle) (s : Finset ι) (S : Rectangle) (c l : ℝ)
    (p : ι → Prop) [DecidablePred p]
    (hzero : ∀ j ∈ s, ¬p j → volume ((R j).carrier ∩ S.stripSlab c l) = 0) :
    stripMass R (s.filter p) S c l = stripMass R s S c l := by
  unfold stripMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hp
  · rfl
  · exact (hzero j hj hp).symm

theorem stripMass_filter_partition (R : ι → Rectangle) (s : Finset ι) (S : Rectangle) (c l : ℝ)
    (p : ι → Prop) [DecidablePred p] :
    stripMass R s S c l = stripMass R (s.filter p) S c l+
      stripMass R (s.filter (fun j => ¬p j)) S c l := by
  exact (Finset.sum_filter_add_sum_filter_not s p _).symm

theorem stripSlab_volume_parent (S : Rectangle) (c l c' : ℝ) :
    volume (S.stripSlab c l) = 2*volume (S.stripSlab c' (l/2)) := by
  rw [S.volume_stripSlab,S.volume_stripSlab]
  have he : ENNReal.ofReal l = 2*ENNReal.ofReal (l/2) := by
    rw [show (2:ℝ≥0∞)=ENNReal.ofReal 2 by norm_num,←ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [he,mul_assoc]

end LipschitzHilbert

end

end OAI
