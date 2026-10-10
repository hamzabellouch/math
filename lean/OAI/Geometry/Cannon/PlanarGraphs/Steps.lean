import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Next

namespace OAI

section
section
section
noncomputable section
namespace CannonCycleOrder

theorem eq_of_steps {n : ℕ} (hn : 0<n) {X : Type*} (z : Fin n → X)
    (hstep : ∀ i,z i=z (next hn i)) (i j : Fin n) : z i=z j := by
  have hc (k : ℕ) (hk : k<n) : z ⟨k,hk⟩=z ⟨0,hn⟩ := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hnx : next hn ⟨k,by omega⟩=(⟨k+1,hk⟩ : Fin n) := by
        simp only [next,dite_eq_left hk]
      have he : z (⟨k+1,hk⟩ : Fin n)=z ⟨k,by omega⟩ := by
        rw [←hnx]
        exact (hstep ⟨k,by omega⟩).symm
      exact he.trans (ih (by omega))
  exact (hc i.val i.isLt).trans (hc j.val j.isLt).symm

theorem eq_of_steps_except {n : ℕ} (hn : 0 < n) {X : Type*} (z : Fin n → X)
    (o : Fin n) (hstep : ∀ i,i≠o → next hn i≠o → z i=z (next hn i))
    {i j : Fin n} (hi : i≠o) (hj : j≠o) : z i=z j := by
  let rot (k : ℕ) : Fin n := ⟨(o.val+1+k)%n,Nat.mod_lt _ hn⟩
  have hrnext (k : ℕ) : rot (k+1)=next hn (rot k) := by
    apply Fin.ext
    rw [next_mod]
    dsimp [rot]
    rw [←Nat.add_assoc (o.val+1) k 1, Nat.add_mod (o.val+1+k) 1,
      Nat.add_mod ((o.val+1+k)%n) 1, Nat.mod_mod]
  have hrne (k : ℕ) (hk : k < n-1) : rot k≠o := by
    intro hh
    have he := congrArg Fin.val hh
    change (o.val+1+k)%n=o.val at he
    by_cases h : o.val+1+k < n
    · rw [Nat.mod_eq_of_lt h] at he; omega
    · have hb : o.val+1+k < 2*n := by omega
      have hm : (o.val+1+k)%n=o.val+1+k-n := Nat.mod_eq_sub_mod (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
      rw [hm] at he
      omega
  have hcover (i : Fin n) (hi : i≠o) : ∃ k,k < n-1 ∧ rot k=i := by
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
  have hconst (k : ℕ) (hk : k < n-1) : z (rot k)=z (rot 0) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hrnext]
      exact (hstep (rot k) (hrne k (by omega)) (by rw [←hrnext]; exact hrne (k+1) hk)).symm.trans (ih (by omega))
  obtain ⟨a,ha,hra⟩ := hcover i hi
  obtain ⟨b,hb,hrb⟩ := hcover j hj
  rw [←hra,←hrb]
  exact (hconst a ha).trans (hconst b hb).symm

end CannonCycleOrder

end
end
end
end

end OAI
