import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalInstanceCost
import OAI.Combinatorics.KMedian.Reduction.RationalThreshold

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def deletionValues (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : Finset ℚ :=
  (deletionChoices T c).biUnion (fun D => T.image (fun i =>
    rationalCost I ((T \ D).erase i)-rationalCost I (T \ D)))

theorem deletion_value_mem (I : Instance) (T U : Finset (Fin I.n)) (c : ℕ)
    (hUT : U ⊆ T) (hcount : T.card-U.card ≤ c) {i : Fin I.n} (hi : i ∈ U) :
    rationalCost I (U.erase i)-rationalCost I U ∈ deletionValues I T c := by
  have hd : T \ U ∈ deletionChoices T c := (mem_deletionChoices T (T \ U) c).mpr
    ⟨sdiff_subset,by rw [card_sdiff_of_subset hUT]; exact hcount⟩
  have he : T \ (T \ U)=U := by
    ext a
    simp only [mem_sdiff]
    exact ⟨fun h => by tauto,fun h => ⟨hUT h,by tauto⟩⟩
  exact mem_biUnion.mpr ⟨T \ U,hd,mem_image.mpr ⟨i,hUT hi,by rw [he]⟩⟩

theorem card_deletionValues (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    (deletionValues I T c).card ≤ (c+1)*(T.card+1)^(c+1) := by
  calc
    _ ≤ ∑ _D ∈ deletionChoices T c, T.card :=
      (card_biUnion_le).trans (sum_le_sum (fun _ _ => card_image_le))
    _ = (deletionChoices T c).card*T.card := by simp
    _ ≤ ((c+1)*(T.card+1)^c)*(T.card+1) :=
      Nat.mul_le_mul (card_deletionChoices T c) (Nat.le_succ _)
    _ = _ := by rw [pow_succ]; ac_rfl

noncomputable def eligible (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) : Finset (Fin I.n) := by
  classical
  exact U.filter (fun i => ((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B)

noncomputable def deleteStep (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  if I.k < U.card then
    if h : (eligible I B U).Nonempty then U.erase ((eligible I B U).min' h) else U
  else U

theorem deleteStep_cases (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    deleteStep I B U=U ∨ ∃ i ∈ U, deleteStep I B U=U.erase i := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · right
    refine ⟨_,?_,rfl⟩
    exact (mem_filter.mp (min'_mem _ he)).1
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem deleteStep_subset (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    deleteStep I B U ⊆ U := by
  rcases deleteStep_cases I B U with he | ⟨i,_,he⟩
  · rw [he]
  · rw [he]; exact erase_subset _ _

theorem deleteStep_card (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    U.card ≤ (deleteStep I B U).card+1 := by
  rcases deleteStep_cases I B U with he | ⟨i,hi,he⟩
  · rw [he]; omega
  · rw [he,card_erase_add_one hi]

theorem deleteStep_congr (I : Instance) (B B' : ℝ) (U : Finset (Fin I.n))
    (htest : ∀ i ∈ U,
      (((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B ↔
       ((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B')) :
    deleteStep I B U=deleteStep I B' U := by
  classical
  have he : eligible I B U=eligible I B' U := by
    ext i
    simp only [eligible,mem_filter]
    exact and_congr_right (htest i)
  unfold deleteStep
  rw [he]

noncomputable def deletionHistory (I : Instance) (B : ℝ) (T : Finset (Fin I.n)) :
    ℕ → Finset (Fin I.n)
  | 0 => T
  | t+1 => deleteStep I B (deletionHistory I B T t)

theorem history_bounds (I : Instance) (B : ℝ) (T : Finset (Fin I.n)) (t : ℕ) :
    deletionHistory I B T t ⊆ T ∧ T.card ≤ (deletionHistory I B T t).card+t := by
  induction t with
  | zero => exact ⟨Subset.rfl,le_rfl⟩
  | succ t ih =>
    refine ⟨(deleteStep_subset I B _).trans ih.1,?_⟩
    have hc := deleteStep_card I B (deletionHistory I B T t)
    change T.card ≤ (deleteStep I B (deletionHistory I B T t)).card+(t+1)
    omega

theorem enumerate_ideal_history (I : Instance) (T : Finset (Fin I.n)) (c : ℕ)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ∈ insert 0 (deletionValues I T c),
      ∀ t ≤ c, deletionHistory I B T t=deletionHistory I (r:ℝ) T t := by
  obtain ⟨r,hr,_,_,htest⟩ := representative_threshold (deletionValues I T c) hB
  refine ⟨r,hr,?_⟩
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro htc
    have ht : t ≤ c := by omega
    have hist := ih ht
    simp only [deletionHistory]
    apply (deleteStep_congr I B (r:ℝ) (deletionHistory I B T t) ?_).trans
      (congrArg (deleteStep I (r:ℝ)) hist)
    intro i hi
    have hb := history_bounds I B T t
    have hm := deletion_value_mem I T (deletionHistory I B T t) c hb.1 (by omega) hi
    exact (htest _ hm).trans (by exact_mod_cast (Iff.rfl :
      rationalCost I ((deletionHistory I B T t).erase i)-rationalCost I (deletionHistory I B T t) ≤ r ↔
      rationalCost I ((deletionHistory I B T t).erase i)-rationalCost I (deletionHistory I B T t) ≤ r))

end MetricKMedian.Reduction
end
end

end OAI
