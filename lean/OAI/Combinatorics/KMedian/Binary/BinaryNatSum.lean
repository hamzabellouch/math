import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras
import OAI.Combinatorics.KMedian.Binary.BinaryFloor

namespace OAI


                                    
section
namespace MetricKMedian.Binary.Automatic.Poly
@[fun_prop] theorem nat_list_sum : Poly (List.sum : List ℕ → ℕ) := by
  have hm : Poly (fun xs : List ℕ => xs.map (fun n : ℕ => (n:ℚ))) := by
    apply list_map <;> fun_prop
  have h : Poly (fun xs : List ℕ => ⌊(xs.map (fun n : ℕ => (n:ℚ))).sum⌋₊) :=
    comp rat_floor (comp rat_sum hm)
  have he : (fun xs : List ℕ => ⌊(xs.map (fun n : ℕ => (n:ℚ))).sum⌋₊)=List.sum := by
    funext xs
    change ⌊(xs.map (Nat.cast : ℕ → ℚ)).sum⌋₊ = xs.sum
    rw [← Nat.cast_list_sum]
    exact Nat.floor_natCast xs.sum
  rw [he] at h
  exact h
@[fun_prop] theorem nat_min : Poly (fun x : ℕ × ℕ => min x.1 x.2) := by
  have h : Poly (fun x : ℕ × ℕ => if decide (x.1≤x.2) then x.1 else x.2) := by fun_prop
  have he : (fun x : ℕ × ℕ => if decide (x.1≤x.2) then x.1 else x.2)=(fun x => min x.1 x.2) := by
    funext x
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (le_of_not_ge h)).symm
  rw [he] at h
  exact h
end MetricKMedian.Binary.Automatic.Poly
end

end OAI
