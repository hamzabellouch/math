import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundPositive
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundProduct

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction

lemma natProduct_intSize_le {B : ℝ} (hB : 0≤B) (xs : List ℕ)
    (hx : ∀q∈xs,(q:ℝ)≤B) : intSize (xs.prod:ℤ)≤B^xs.length := by
  induction xs with
  | nil => simp [intSize]
  | cons q qs ih =>
    simp only [List.prod_cons,List.length_cons,Nat.cast_mul,intSize_mul]
    have hq : intSize (q:ℤ)≤B := by
      simpa only [intSize,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg q : (0:ℝ)≤(q:ℝ))]
        using hx q List.mem_cons_self
    simpa only [pow_succ,mul_comm] using mul_le_mul hq
      (ih (fun r hr => hx r (List.mem_cons_of_mem q hr))) (intSize_nonneg _) hB

theorem pairModulus_le {N : ℕ} {B : ℝ} (hB : 1≤B) {l : ℕ}
    (h k : History l) (hh : factorBound N B h) (hk : factorBound N B k)
    (outside : List ℕ) (hout : ∀q∈outside,(q:ℝ)≤B) :
    (pairModulus h k outside:ℝ) ≤
      B^(l*(divisorCost h+divisorCost k)+testCost h+testCost k+outside.length) := by
  have hB0 : 0≤B := le_trans (by norm_num) hB
  have hd := divisorProduct_intSize_le hB h hh
  have kd := divisorProduct_intSize_le hB k hk
  have ht := testProduct_intSize_le hB h hh
  have kt := testProduct_intSize_le hB k hk
  have ho := natProduct_intSize_le hB0 outside hout
  calc
    _ = (intSize (divisorProduct h)*intSize (divisorProduct k))^l*
        (intSize (testProduct h)*intSize (testProduct k)*intSize (outside.prod:ℤ)) := by
      simp only [pairModulus,pairPrecision,pairTestProduct,pairedDivisorProduct,
        Nat.cast_natAbs,Int.cast_abs,intSize,Int.cast_mul,Int.cast_pow,
        abs_mul,abs_pow]
    _ ≤ (B^divisorCost h*B^divisorCost k)^l*
        (B^testCost h*B^testCost k*B^outside.length) := by
      gcongr <;> first | assumption | (unfold intSize; positivity)
    _ = _ := by
      rw [←pow_add,←pow_mul]
      simp only [pow_add]
      ring

theorem log_pairModulus_le {N : ℕ} {B : ℝ} (hB : 1≤B) {l : ℕ}
    (h k : History l) (hh : factorBound N B h) (hk : factorBound N B k)
    (outside : List ℕ) (hout : ∀q∈outside,(q:ℝ)≤B)
    (hpos : 0<pairModulus h k outside) :
    Real.log (pairModulus h k outside) ≤
      (l*(divisorCost h+divisorCost k)+testCost h+testCost k+outside.length)*Real.log B := by
  have hm : (0:ℝ)<pairModulus h k outside := by exact_mod_cast hpos
  have he := Real.log_le_log hm (pairModulus_le hB h k hh hk outside hout)
  simpa only [Real.log_pow,Nat.cast_add,Nat.cast_mul] using he

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
