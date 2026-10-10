import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionShape

namespace OAI

noncomputable section
namespace Ostmann.Conclusion
open Construction

@[simp] theorem currentBulkPositionEquiv_fst_val (m k l : ℕ)
    (x : BulkPosition (Template.current (Template.initial m k) l)) :
    (currentBulkPositionEquiv m k l x).1.val=
      x.val.val/(bulkLeafTemplate m k l).length := rfl

@[simp] theorem currentBulkPositionEquiv_snd_val (m k l : ℕ)
    (x : BulkPosition (Template.current (Template.initial m k) l)) :
    (currentBulkPositionEquiv m k l x).2.val=
      x.val.val%(bulkLeafTemplate m k l).length := rfl

theorem currentBulkPositionEquiv_leaf_iff (m k l : ℕ)
    (x : BulkPosition (Template.current (Template.initial m k) l)) (b : Fin (2^l)) :
    (currentBulkPositionEquiv m k l x).1=b ↔
      b.val*(bulkLeafTemplate m k l).length ≤ x.val.val ∧
      x.val.val<(b.val+1)*(bulkLeafTemplate m k l).length := by
  have hm : 0 < m := Nat.zero_lt_of_lt (currentBulkPositionEquiv m k l x).2.isLt
  have hn : 0 < (bulkLeafTemplate m k l).length := hm.trans_le (bulkLeafTemplate_length_ge m k l)
  rw [Fin.ext_iff,currentBulkPositionEquiv_fst_val,Nat.div_eq_iff hn,Nat.add_mul,Nat.one_mul]
  omega

theorem currentBulkPositionEquiv_slot_lt_iff (m k l : ℕ) (b : Fin (2^l)) (i j : Fin m) :
    ((currentBulkPositionEquiv m k l).symm (b,i)).val.val <
      ((currentBulkPositionEquiv m k l).symm (b,j)).val.val ↔ i.val<j.val := by
  simp only [currentBulkPositionEquiv_symm_val,Nat.add_lt_add_iff_left]

theorem currentBulkPositionEquiv_leaf_lt (m k l : ℕ) (b c : Fin (2^l))
    (hbc : b.val<c.val) (i j : Fin m) :
    ((currentBulkPositionEquiv m k l).symm (b,i)).val.val <
      ((currentBulkPositionEquiv m k l).symm (c,j)).val.val := by
  rw [currentBulkPositionEquiv_symm_val,currentBulkPositionEquiv_symm_val]
  have hi := i.isLt.trans_le (bulkLeafTemplate_length_ge m k l)
  have hmul := Nat.mul_le_mul_right (bulkLeafTemplate m k l).length hbc
  nlinarith

theorem current_remainder_eq_bulkLeafBlocks (m k l : ℕ) :
    Template.remainder (l+1) (Template.current (Template.initial m k) l)=
      (List.replicate (2^l) (bulkLeafTemplate m k (l+1))).flatten := by
  rw [current_eq_bulkLeafBlocks]
  simp only [Template.remainder,List.filter_flatten,List.map_replicate]
  have he := (bulkLeafTemplate_succ m k l).symm
  unfold Template.remainder at he
  rw [he]

@[simp] theorem current_remainder_bulk_block_length (m k l : ℕ) :
    (Template.remainder (l+1) (Template.current (Template.initial m k) l)).length=
      2^l*(bulkLeafTemplate m k (l+1)).length := by
  rw [current_remainder_eq_bulkLeafBlocks]
  simp [List.length_flatten,List.map_replicate]

theorem currentBulkPositionEquiv_left_half_iff (m k l : ℕ)
    (x : BulkPosition (Template.current (Template.initial m k) (l+1))) :
    (currentBulkPositionEquiv m k (l+1) x).1.val<2^l ↔
      x.val.val<(Template.remainder (l+1) (Template.current (Template.initial m k) l)).length := by
  have hm : 0 < m := Nat.zero_lt_of_lt (currentBulkPositionEquiv m k (l+1) x).2.isLt
  have hn := hm.trans_le (bulkLeafTemplate_length_ge m k (l+1))
  rw [currentBulkPositionEquiv_fst_val,current_remainder_bulk_block_length,
    Nat.div_lt_iff_lt_mul hn]

theorem currentBulkPositionEquiv_right_half_iff (m k l : ℕ)
    (x : BulkPosition (Template.current (Template.initial m k) (l+1))) :
    2^l ≤ (currentBulkPositionEquiv m k (l+1) x).1.val ↔
      (Template.remainder (l+1) (Template.current (Template.initial m k) l)).length ≤ x.val.val := by
  simpa only [not_lt] using not_congr (currentBulkPositionEquiv_left_half_iff m k l x)

end Ostmann.Conclusion

end

end OAI
