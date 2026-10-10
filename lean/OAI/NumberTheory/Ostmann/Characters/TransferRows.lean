import OAI.NumberTheory.Ostmann.Characters.TransferAlgebra

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
variable {H Y G:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [CommGroup G]

def rowProduct {ι:Type*} [Fintype ι] (e:ι→ℤ) (z:ι→G) : G := ∏j,z j^e j

theorem transferGraph_row (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (i:H) (t:Bool) (z:((H×Bool)⊕Y)→G)
    (hself:b (some (.inl i)) (some (.inl i))=0) :
    rowProduct (transferGraph b (.inl (i,t))) z =
      (∏h:H,z (.inl (h,t))^b (some (.inl i)) (some (.inl h)))^copySign t *
      (∏h:H,z (.inl (h,!t)))^(copySign t*b (some (.inl i)) none) *
      (∏y:Y,z (.inr y)^b (some (.inl i)) (some (.inr y)))^copySign t := by
  have hdiag (h:H) : (if i=h then 0 else b (some (.inl i)) (some (.inl h))) =
      b (some (.inl i)) (some (.inl h)) := by
    split_ifs with hi
    · subst h; exact hself.symm
    · rfl
  have hdiagneg (h:H) : (if i=h then 0 else -b (some (.inl i)) (some (.inl h))) =
      -b (some (.inl i)) (some (.inl h)) := by
    split_ifs with hi
    · subst h; simp only [hself,neg_zero]
    · rfl
  cases t <;>
    simp only [rowProduct,Fintype.prod_sum_type,Fintype.prod_prod_type,
      Fintype.prod_bool,transferGraph,copySign,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,hdiag,hdiagneg,
      Int.one_mul,Int.neg_mul,zpow_one,zpow_neg,Finset.prod_mul_distrib,
      Finset.prod_inv_distrib,← Finset.prod_zpow]
  ac_rfl

theorem transferGraph_shared_row (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (y:Y) (z:((H×Bool)⊕Y)→G) :
    rowProduct (transferGraph b (.inr y)) z =
      (∏h:H,z (.inl (h,true))^b (some (.inr y)) (some (.inl h))) /
      (∏h:H,z (.inl (h,false))^b (some (.inr y)) (some (.inl h))) := by
  simp only [rowProduct,Fintype.prod_sum_type,Fintype.prod_prod_type,
    Fintype.prod_bool,transferGraph,copySign,Bool.false_eq_true,ite_true,ite_false,Int.one_mul,
    Int.neg_mul,zpow_neg,zpow_zero,Finset.prod_const_one,mul_one,
    Finset.prod_mul_distrib,Finset.prod_inv_distrib,div_eq_mul_inv]

omit [DecidableEq H] in
theorem incoming_pivot_substitution [DecidableEq H] (P u:G) (z:H→G) (e:ℤ)
    (hP:P=u*∏h,z h) : P^e=u^e*∏h,z h^e := by
  rw [hP,mul_zpow,Finset.prod_zpow]

end Ostmann.Characters

end

end OAI
