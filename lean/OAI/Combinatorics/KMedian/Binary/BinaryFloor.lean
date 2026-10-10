import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutomatic

namespace OAI


                                   
section
namespace MetricKMedian.Binary.Automatic.Poly
@[fun_prop] theorem int_natAbs : Poly Int.natAbs := by
  exact ⟨(PolyProgram.snd encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem rat_num : Poly Rat.num := by
  exact ⟨(PolyProgram.fst Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem rat_den : Poly Rat.den := by
  exact ⟨(PolyProgram.snd Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)⟩
 theorem natFloor_eq (q : ℚ) : ⌊q⌋₊=if q<0 then 0 else q.num.natAbs/q.den := by
  by_cases h : q<0
  · simp only [ite_eq_left h,Nat.floor_of_nonpos h.le]
  · rw [ite_eq_right h]
    have hn : 0≤q.num := Rat.num_nonneg.mpr (le_of_not_gt h)
    have he : ((q.num.natAbs:ℕ):ℚ)/(q.den:ℚ)=q := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_nonneg hn,Rat.num_div_den]
    calc
      ⌊q⌋₊=⌊((q.num.natAbs:ℕ):ℚ)/(q.den:ℚ)⌋₊ := congrArg Nat.floor he.symm
      _ = _ := Rat.natFloor_natCast_div_natCast _ _
@[fun_prop] theorem rat_floor : Poly (fun q : ℚ => ⌊q⌋₊) := by
  have division : Poly (fun values : ℕ × ℕ => values.1 / values.2) :=
    ⟨PolyProgram.natDiv⟩
  have floorProgram : Poly (fun rational : ℚ =>
      if decide (rational < 0) then 0 else rational.num.natAbs / rational.den) :=
    ite (rat_lt_comp identity (const 0)) (const 0)
      (comp division (pair (comp int_natAbs rat_num) rat_den))
  simpa only [decide_eq_true_eq,← natFloor_eq] using floorProgram
end MetricKMedian.Binary.Automatic.Poly
end

end OAI
