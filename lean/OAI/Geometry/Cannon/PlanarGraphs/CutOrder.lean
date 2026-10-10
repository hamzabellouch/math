import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Next

namespace OAI

section
section
section
noncomputable section
namespace CannonCycleOrder

def cutOrder {n : ℕ} (hn : 0<n) (o : Fin n) (k : ℕ) : Fin n :=
  ⟨(o.val+1+k)%n,Nat.mod_lt _ hn⟩

lemma cutOrder_next {n : ℕ} (hn : 0<n) (o : Fin n) (k : ℕ) :
    cutOrder hn o (k+1)=next hn (cutOrder hn o k) := by
  apply Fin.ext
  rw [next_mod]
  dsimp [cutOrder]
  rw [←Nat.add_assoc (o.val+1) k 1,Nat.add_mod (o.val+1+k) 1,
    Nat.add_mod ((o.val+1+k)%n) 1,Nat.mod_mod]

lemma cutOrder_last {n : ℕ} (hn : 0<n) (o : Fin n) : cutOrder hn o (n-1)=o := by
  apply Fin.ext
  change (o.val+1+(n-1))%n=o.val
  rw [show o.val+1+(n-1)=n+o.val by omega,Nat.add_mod]
  simp [Nat.mod_eq_of_lt o.isLt]

lemma cutOrder_first {n : ℕ} (hn : 0<n) (o : Fin n) : cutOrder hn o 0=next hn o := by
  apply Fin.ext
  rw [next_mod]
  simp [cutOrder]

lemma cutOrder_ne {n : ℕ} (hn : 0<n) (o : Fin n) {k : ℕ} (hk : k<n-1) :
    cutOrder hn o k≠o := by
  intro hh
  have he := congrArg Fin.val hh
  change (o.val+1+k)%n=o.val at he
  by_cases h : o.val+1+k<n
  · rw [Nat.mod_eq_of_lt h] at he; omega
  · have hm : (o.val+1+k)%n=o.val+1+k-n := Nat.mod_eq_sub_mod (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
    rw [hm] at he; omega

lemma cutOrder_inj {n : ℕ} (hn : 0<n) (o : Fin n) {k l : ℕ} (hk : k<n) (hl : l<n)
    (he : cutOrder hn o k=cutOrder hn o l) : k=l := by
  have hh := congrArg Fin.val he
  change (o.val+1+k)%n=(o.val+1+l)%n at hh
  have hm (j : ℕ) (hj : j<n) (hh : n≤o.val+1+j) :
      (o.val+1+j)%n=o.val+1+j-n := Nat.mod_eq_sub_mod hh |>.trans (Nat.mod_eq_of_lt (by omega))
  by_cases h1 : o.val+1+k<n <;> by_cases h2 : o.val+1+l<n
  · rw [Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2] at hh; omega
  · rw [Nat.mod_eq_of_lt h1,hm l hl (by omega)] at hh; omega
  · rw [hm k hk (by omega),Nat.mod_eq_of_lt h2] at hh; omega
  · rw [hm k hk (by omega),hm l hl (by omega)] at hh; omega

lemma cutOrder_cover {n : ℕ} (hn : 0<n) (o i : Fin n) (hi : i≠o) :
    ∃ k,k<n-1 ∧ cutOrder hn o k=i := by
  have hne : i.val≠o.val := fun h=>hi (Fin.ext h)
  by_cases h : o.val < i.val
  · refine ⟨i.val-o.val-1,by omega,?_⟩
    apply Fin.ext
    change (o.val+1+(i.val-o.val-1))%n=i.val
    rw [show o.val+1+(i.val-o.val-1)=i.val by omega,Nat.mod_eq_of_lt i.isLt]
  · refine ⟨n-o.val-1+i.val,by omega,?_⟩
    apply Fin.ext
    change (o.val+1+(n-o.val-1+i.val))%n=i.val
    rw [show o.val+1+(n-o.val-1+i.val)=n+i.val by omega,Nat.add_mod]
    simp [Nat.mod_eq_of_lt i.isLt]

lemma sum_cutOrder {n : ℕ} (hn : 0<n) (o : Fin n) (f : Fin n → ℝ) (ho : f o=0) :
    ∑ k∈Finset.range (n-1),f (cutOrder hn o k)=∑ i,f i := by
  classical
  have he : (∑ k∈Finset.range (n-1),f (cutOrder hn o k))=∑ i∈Finset.univ.erase o,f i := by
    apply Finset.sum_bij (fun k _=>cutOrder hn o k)
    · intro k hk; exact Finset.mem_erase.mpr ⟨cutOrder_ne hn o (Finset.mem_range.mp hk),Finset.mem_univ _⟩
    · intro k hk l hl he
      exact cutOrder_inj hn o (by have := Finset.mem_range.mp hk; omega) (by have := Finset.mem_range.mp hl; omega) he
    · intro i hi
      obtain ⟨k,hk,he⟩:=cutOrder_cover hn o i (Finset.mem_erase.mp hi).1
      exact ⟨k,Finset.mem_range.mpr hk,he⟩
    · intro k hk; rfl
  rw [he]
  have hh:=Finset.sum_erase_add Finset.univ f (Finset.mem_univ o)
  rw [ho,add_zero] at hh
  exact hh

end CannonCycleOrder

end
end
end
end

end OAI
