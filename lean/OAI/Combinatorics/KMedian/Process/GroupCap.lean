import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyRound

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

 theorem integral_next_subset (A erased : Finset (Copy (F := F) Δ)) (O : Finset F) :
    integral Δ (next Δ A erased O) ⊆ integral Δ A ∪ O := by
  intro f hf
  by_cases ho : f ∈ O
  · exact mem_union_right _ ho
  · apply mem_union_left
    apply (mem_integral _ _ _).mpr
    intro i hi
    have hh := (mem_integral _ _ _).mp hf hi
    rcases mem_union.mp hh with hh | hh
    · exact (mem_sdiff.mp hh).1
    · have hh' := (mem_resets _ _ _).mp hh
      rw [(mem_slots _ _ _).mp hi] at hh'
      exact False.elim (ho hh')

 theorem round_integral_eq (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (FixedBatch.HeavyAction (FixedBatch.graphActions G) H))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
    integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))=
      integral Δ A ∪ roundOpened A G H Z := by
  apply Subset.antisymm (integral_next_subset Δ A _ _)
  exact union_subset (round_integral_persists A G H Z hG hown) (reset_integral Δ A _ _)

end MetricKMedian.CopyState

namespace MetricKMedian.GroupCap
open Finset
variable {F E : Type*}

noncomputable def cap (R : ℝ) (d : F → ℝ) (O : Finset F) : ℝ := O.fold min (5*R) d

 theorem le_cap (R : ℝ) (d : F → ℝ) (O : Finset F) (c : ℝ) :
    c ≤ cap R d O ↔ c ≤ 5*R ∧ ∀ f ∈ O, c ≤ d f := le_fold_min _

 theorem cap_le_radius (R : ℝ) (d : F → ℝ) (O : Finset F) : cap R d O ≤ 5*R :=
  (fold_min_le _).mpr (Or.inl le_rfl)

 theorem cap_le_member (R : ℝ) (d : F → ℝ) (O : Finset F) {f : F} (hf : f ∈ O) :
    cap R d O ≤ d f := (fold_min_le _).mpr (Or.inr ⟨f,hf,le_rfl⟩)

 theorem cap_nonneg {R : ℝ} (d : F → ℝ) (O : Finset F)
    (hR : 0 ≤ R) (hd : ∀ f, 0 ≤ d f) : 0 ≤ cap R d O :=
  (le_cap R d O 0).mpr ⟨by positivity,fun f _ => hd f⟩

 theorem cap_antitone (R : ℝ) (d : F → ℝ) {O O' : Finset F} (hO : O ⊆ O') :
    cap R d O' ≤ cap R d O :=
  (le_cap R d O _).mpr ⟨cap_le_radius R d O',fun _ hf => cap_le_member R d O' (hO hf)⟩

theorem cap_union_image [DecidableEq F] (R : ℝ) (d : F → ℝ) (O : Finset F) (Z : Finset E) (s : E → F) :
    cap R d (O ∪ Z.image s)=Z.fold min (cap R d O) (fun e => d (s e)) := by
  apply le_antisymm
  · apply (le_fold_min _).mpr
    exact ⟨cap_antitone R d subset_union_left,fun e he =>
      cap_le_member R d _ (mem_union_right _ (mem_image.mpr ⟨e,he,rfl⟩))⟩
  · have hh := (le_fold_min _).mp (show Z.fold min (cap R d O) (fun e => d (s e)) ≤
        Z.fold min (cap R d O) (fun e => d (s e)) from le_rfl)
    apply (le_cap R d _ _).mpr
    refine ⟨hh.1.trans (cap_le_radius R d O),?_⟩
    intro f hf
    rcases mem_union.mp hf with hf | hf
    · exact hh.1.trans (cap_le_member R d O hf)
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hf
      exact hh.2 e he

 theorem cap_mono_distance {R : ℝ} {d d' : F → ℝ} (O : Finset F)
    (hd : ∀ f ∈ O, d f ≤ d' f) : cap R d O ≤ cap R d' O := by
  apply (le_cap R d' O _).mpr
  exact ⟨cap_le_radius R d O,fun f hf => (cap_le_member R d O hf).trans (hd f hf)⟩

end MetricKMedian.GroupCap
end
end

end OAI
