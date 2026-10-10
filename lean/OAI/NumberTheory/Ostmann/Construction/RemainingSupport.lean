import OAI.NumberTheory.Ostmann.Construction.RemainingRows
import OAI.NumberTheory.Ostmann.Construction.SourcePositive

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem remainingProduct_pos (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (y : RemainingSample sources T giant) : 0<remainingProduct sources T giant y :=
  mul_pos (giant.prime _ y.1.property).pos (assignedSlots_product_pos sources T y.2)

theorem remainingIntegrand_root_support (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : AllowedFrequency V l)
    (hf : remainingIntegrand d P sources seed V giant X G bins outside l p u y v≠0) :
    let a := remainingState sources (Template.current seed l) (l+1) giant p u y v.val
    a.Positive ∧ a.PrimeSmall ∧ a.TemplateAt l ∧ a.Coprime outside ∧
      a.frequency≠0 ∧ a.frequency.natAbs≤V l := by
  apply actualCoefficient_root_support
  exact (mul_ne_zero_iff.mp hf).2

theorem remainingIntegrand_denominator_coprime (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : AllowedFrequency V l)
    (hf : remainingIntegrand d P sources seed V giant X G bins outside l p u y v≠0) :
    (remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y).Coprime
      (halfProduct p (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u)) := by
  have hroot := remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u y v hf
  exact (state_coprime_halves _ _ _ outside
    (Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _))
    hroot.2.2.2.1).2.2

def remainingExactTag (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (y : RemainingSample sources T giant) (v : ℤ) : ℚ :=
  (v:ℚ)/(remainingProduct sources T giant y:ℚ)

theorem remainingExactTag_refines (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l)
    (hfx : remainingIntegrand d P sources seed V giant X G bins outside l p u x v≠0)
    (hfy : remainingIntegrand d P sources seed V giant X G bins outside l p u y w≠0)
    (htag : remainingExactTag sources (Template.remainder (l+1) (Template.current seed l)) giant y w.val=
      remainingExactTag sources (Template.remainder (l+1) (Template.current seed l)) giant x v.val) :
    modFraction (halfProduct p (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))
      w.val (remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y)=
    modFraction (halfProduct p (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))
      v.val (remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x) := by
  have hx := remainingProduct_pos sources (Template.remainder (l+1) (Template.current seed l)) giant x
  have hy := remainingProduct_pos sources (Template.remainder (l+1) (Template.current seed l)) giant y
  have hc := (div_eq_div_iff (by exact_mod_cast hy.ne' :
      (remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y:ℚ)≠0)
    (by exact_mod_cast hx.ne' :
      (remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x:ℚ)≠0)).mp htag
  rw [modFraction_eq_iff_reversal_dvd _ _ _ _ _
    (remainingIntegrand_denominator_coprime d P sources seed V giant X G bins outside l p u y w hfy)
    (remainingIntegrand_denominator_coprime d P sources seed V giant X G bins outside l p u x v hfx)]
  have hz : Arithmetic.reversalNumerator w.val v.val
      (remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y:ℤ)
      (remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x:ℤ)=0 := by
    unfold Arithmetic.reversalNumerator
    apply sub_eq_zero.mpr
    exact_mod_cast hc
  rw [hz]
  exact dvd_zero _

end Ostmann.Construction

end

end OAI
