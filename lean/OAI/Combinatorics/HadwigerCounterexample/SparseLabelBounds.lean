import OAI.Combinatorics.HadwigerCounterexample.BooleanLabels

namespace OAI

/-! # Sparse Label Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset Submodule
variable {p : Shape} {n : ℕ}

abbrev LabVals (p : Shape) (n : ℕ) := Label p.b → Vec (AIdx p.g n)

def labcomb (p : Shape) (n : ℕ) (L : Finset (Label p.b)) :
    LabVals p n →ₗ[F] Ray p n :=
  ∑ i∈L, putLab p n i ∘ₗ LinearMap.proj i

theorem labcomb_eval (L : Finset (Label p.b)) (z : LabVals p n) :
    labcomb p n L z= ∑ i∈L, putLab p n i (z i) := by simp [labcomb,LinearMap.sum_apply]

def labV (p : Shape) (n : ℕ) (L : Finset (Label p.b)) : Space (Ray p n) :=
  LinearMap.range (labcomb p n L)

def withinL (p : Shape) (L : Finset (Label p.b)) (z : LabVals p n) : LabVals p n :=
  fun i => if i ∈ L then z i else 0

theorem within_eq {L B : Finset (Label p.b)} (h : B ⊆ L) (z : LabVals p n) :
    labcomb p n B z = labcomb p n L (withinL p B z) := by
  classical
  rw [labcomb_eval,labcomb_eval]
  refine (sum_congr (g:=fun i => putLab p n i (withinL p B z i)) rfl fun i hi => ?_).trans
    (sum_subset h fun i _ hi => ?_)
  · simp [withinL,hi]
  simp [withinL,hi]

theorem labV_mono {L B : Finset (Label p.b)} (h : B ⊆ L) : labV p n B ≤ labV p n L := by
  rintro x ⟨y,rfl⟩
  exact ⟨_,(within_eq h y).symm⟩

theorem labV_unique {L B : Finset (Label p.b)} {z : LabVals p n}
    (h : labcomb p n B z∈labV p n L) (hj : (B∪L).card≤p.j+1) :
    ∀ i∈B,i∉L → z i=0 := by
  intro i hi hL
  obtain ⟨x,hx⟩ := h
  rw [within_eq (B:=L) (L:=B∪L) subset_union_right,
    within_eq (B:=B) (L:=B∪L) subset_union_left] at hx
  have he :
      labcomb p n (B∪L) ((withinL p B z)-(withinL p L x))=0 := by rw [map_sub,hx,sub_self]
  rw [labcomb_eval] at he
  have hg := ray_indep _ _ hj he i (mem_union_left L hi)
  simpa [withinL,hL,hi] using hg

/-- L is the set excluded at this projected space. -/
def protectedBy (p : Shape) {n} (S : Space (Ray p n)) (q : ℕ) (L : Finset (Label p.b)) :=
  ∀ (B : Finset (Label p.b)) (z : LabVals p n),
    labcomb p n B z∈S → B.card≤q → ∀ i∈B,i∉L → z i=0

theorem protect_labels (p : Shape) {n} (S : Space (Ray p n)) (q : ℕ)
    (hq : (dim S+1)*q≤p.j+1) :
    ∃ L : Finset (Label p.b), L.card≤dim S * q ∧ protectedBy p S q L := by
  classical
  let T : Set ℕ := {t | ∃ (A : Space (Ray p n)) (L : Finset (Label p.b)), A ≤ S ∧
    A ≤ labV p n L ∧ L.card ≤ t*q ∧ t = dim A}
  have he : BddAbove T := ⟨dim S, by
    rintro x ⟨A,L, hA,hL,_,rfl⟩
    exact Submodule.finrank_mono hA⟩
  have hn : T.Nonempty := ⟨0, ⊥,∅, bot_le, bot_le, by simp, (finrank_bot ..).symm⟩
  obtain ⟨A,L,hA,hL,hsize,hd⟩ := (show sSup T∈T from Nat.sSup_mem hn he)
  have hi := finrank_mono hA
  rw [hd] at hsize
  have hsc : L.card ≤ dim S*q := hsize.trans (Nat.mul_le_mul_right _ hi)
  refine ⟨L,hsc,fun B z hz hB => ?_⟩
  have hh : (B∪L).card≤p.j+1 := by
    refine (card_union_le _ _).trans ((add_le_add hB hsc).trans ?_)
    simpa [Nat.add_mul, Nat.add_comm] using hq
  let x := labcomb p n B z
  apply labV_unique _ hh
  by_cases hx : x∈A
  · exact hL hx
  let V : Space (Ray p n) := Submodule.span F ({x}:Set _)
  have hv : dim A < dim (A⊔V : Submodule _ _) := by
    apply Nat.lt_of_le_of_ne (Submodule.finrank_mono (show A≤A⊔V from le_sup_left)) (fun h => hx ?_)
    have hh : A=A⊔V := Submodule.eq_of_le_of_finrank_eq le_sup_left h
    exact (show V≤A from le_trans le_sup_right hh.symm.le) (show x ∈ V from
      Submodule.subset_span (Set.mem_singleton _))
  have hk : dim (A⊔V : Submodule _ _)∈ T := by
    refine ⟨A⊔V,B∪L,sup_le hA ((Submodule.span_singleton_le_iff_mem x S).mpr hz),
      sup_le (hL.trans (labV_mono subset_union_right)) ?_, ?_,rfl⟩
    · refine le_trans ((Submodule.span_singleton_le_iff_mem x _).mpr (show x∈labV p n B from
        ⟨z,rfl⟩)) (labV_mono subset_union_left)
    exact (card_union_le _ _).trans ((Nat.add_le_add hB hsize).trans (by
      simpa [Nat.add_mul,add_comm q] using Nat.mul_le_mul_right q hv))
  have hg := le_csSup he hk
  exact (not_le_of_gt hv (by rwa [← hd])).elim

end HadwigerCounterexample

end

end OAI
