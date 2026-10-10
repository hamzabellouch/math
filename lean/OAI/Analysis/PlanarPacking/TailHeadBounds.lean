import OAI.Analysis.PlanarPacking.TailRationalBase
import OAI.Analysis.PlanarPacking.TailHead

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def signedHeadC (a : Bool) (i : HeadNodeIndex) : ℝ :=
  (if a then 1 else -1)*headC (tableData a) i
noncomputable def signedHeadD (a : Bool) (i : HeadNodeIndex) : ℝ :=
  (if a then 1 else -1)*headD (tableData a) i
noncomputable def headLowerRat (a : Bool) : ℚ :=
  let σ : ℚ := if a then 1 else -1
  σ*tableConstant a+
    min (∑ i : HeadNodeIndex, σ*tableD a (headNodeNat i)) 0/(83/2)+
    ∑ i : HeadNodeIndex,(min (σ*tableC a (headNodeNat i)) 0/(83/2-headNodeNat i)^2+
      min (σ*tableD a (headNodeNat i)) 0*headNodeNat i/((83/2)*(83/2-headNodeNat i)))
lemma headLowerRat_check (a : Bool) : (12:ℚ)/1000<headLowerRat a := by
  cases a <;> decide +kernel
lemma table_head_C (a : Bool) (i : HeadNodeIndex) :
    headC (tableData a) i=(tableC a (headNodeNat i):ℝ) := by
  cases i <;> rfl
lemma table_head_D (a : Bool) (i : HeadNodeIndex) :
    headD (tableData a) i=(tableD a (headNodeNat i):ℝ) := by
  cases i <;> rfl
lemma table_head_lower (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    (12:ℝ)/1000<(if a then 1 else -1)*headRational (tableData a) s := by
  have hh:=rational_finite_lower (signedHeadC a) (signedHeadD a) (fun i => (headNodeNat i:ℝ))
    ((if a then 1 else -1)*(tableData a).C) ((83:ℝ)/2) s
    (fun i => Nat.cast_nonneg _) (fun i => by
      have hl : (headNodeNat i:ℝ)≤40 := by exact_mod_cast headNodeNat_le i
      linarith) (by norm_num) hs
  have he : (headLowerRat a:ℝ)=
    (if a then 1 else -1)*(tableData a).C+min (∑ i,signedHeadD a i) 0/(83/2)+
      ∑ i,(min (signedHeadC a i) 0/(83/2-headNodeNat i)^2+
      min (signedHeadD a i) 0*headNodeNat i/((83/2)*(83/2-headNodeNat i))) := by
    simp only [headLowerRat,signedHeadC,signedHeadD,table_head_C,table_head_D,
      Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sum,Rat.cast_min,Rat.cast_zero,
      Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast,Rat.cast_sub,apply_ite,
      Rat.cast_one,Rat.cast_neg]
    rfl
  rw [← he] at hh
  have hl : ((12/1000:ℚ):ℝ)<(headLowerRat a:ℝ) := Rat.cast_lt.mpr (headLowerRat_check a)
  norm_num at hl
  have ht:=hl.trans_le hh
  have heq : (if a then 1 else -1)*headRational (tableData a) s =
      (if a then 1 else -1)*(tableData a).C+
        ∑ i,(signedHeadC a i/(s-headNodeNat i)^2+signedHeadD a i/(s-headNodeNat i)) := by
    rw [headRational,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [signedHeadC,signedHeadD]
    ring
  rw [heq]
  linarith
end SharpPlanar

end OAI
