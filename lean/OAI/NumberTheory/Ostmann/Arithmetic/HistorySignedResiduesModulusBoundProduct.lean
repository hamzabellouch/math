import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction

theorem divisorProduct_intSize_le {N : ℕ} {B : ℝ} (hB:1≤B) {l : ℕ}
    (h : History l) (hb : factorBound N B h) : intSize (divisorProduct h)≤B^divisorCost h := by
  have hB0 : 0≤B := le_trans (by norm_num) hB
  induction h with
  | leaf a => simp [divisorProduct,divisorCost,intSize]
  | node a p u hp hm left right il ir =>
    have hf : intSize a.frequency≤B := hb.1
    have hu := smallProduct_intSize_le hB0 u hb.2.2.2.2.1
    have hl := il hb.2.2.2.2.2.1
    have hr := ir hb.2.2.2.2.2.2
    calc
      _ = (intSize a.frequency*intSize ((u.map SmallSlot.value).prod:ℤ))*
          intSize (divisorProduct left)*intSize (divisorProduct right) := by
        simp only [divisorProduct,intSize_mul]
      _ ≤ (B*B^u.length)*B^divisorCost left*B^divisorCost right := by
        gcongr <;> first | assumption | exact intSize_nonneg _
      _ = _ := by simp only [divisorCost,pow_add,pow_one]

theorem testProduct_intSize_le {N : ℕ} {B : ℝ} (hB:1≤B) {l : ℕ}
    (h : History l) (hb : factorBound N B h) : intSize (testProduct h)≤B^testCost h := by
  have hB0 : 0≤B := le_trans (by norm_num) hB
  induction h with
  | leaf a =>
    have hf : intSize a.frequency≤B := hb.1
    have ha := smallProduct_intSize_le hB0 a.small hb.2.2
    calc
      _ = intSize a.frequency*intSize ((a.small.map SmallSlot.value).prod:ℤ) := by
        simp only [testProduct,intSize_mul]
      _ ≤ B*B^a.small.length := by gcongr; first | assumption | exact intSize_nonneg _
      _ = _ := by simp only [testCost,pow_add,pow_one]
  | node a p u hp hm left right il ir =>
    have hf : intSize a.frequency≤B := hb.1
    have hfreq := intSize_list_prod_le hB0 (History.node a p u hp hm left right).frequencies
      (factorBound_frequencies _ hb)
    have ha := smallProduct_intSize_le hB0 a.small hb.2.2.1
    have hu := smallProduct_intSize_le hB0 u hb.2.2.2.2.1
    have hl := il hb.2.2.2.2.2.1
    have hr := ir hb.2.2.2.2.2.2
    calc
      _ = intSize (History.node a p u hp hm left right).frequencies.prod*
          intSize ((a.small.map SmallSlot.value).prod:ℤ)*
          ((intSize a.frequency*intSize ((u.map SmallSlot.value).prod:ℤ))*
            intSize ((u.map SmallSlot.value).prod:ℤ)^2*
            intSize (testProduct left)*intSize (testProduct right)) := by
        simp only [testProduct,intSize_mul,intSize_pow]
      _ ≤ B^(History.node a p u hp hm left right).frequencies.length*B^a.small.length*
          ((B*B^u.length)*(B^u.length)^2*B^testCost left*B^testCost right) := by
        gcongr <;> first | assumption | exact intSize_nonneg _ | (unfold intSize; positivity)
      _ = _ := by
        simp only [testCost,pow_add,pow_mul,pow_one]
        ring

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
