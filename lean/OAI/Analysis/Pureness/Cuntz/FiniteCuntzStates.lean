import OAI.Analysis.Pureness.Cuntz.FiniteCuntzAlmostUnperforation
import OAI.Analysis.Pureness.Cuntz.SemigroupComparisonArithmetic
import OAI.Analysis.Pureness.Cuntz.SemigroupStateBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ENNReal
open OrderedSemigroup
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance sharedCuntz_isOrderedAddMonoid : IsOrderedAddMonoid (CuntzClass (MatrixLimit A)) where
  add_le_add_left _ _ h _ := CuntzClass.matrixAdd_mono h le_rfl

lemma sharedCuntz_zero_le (x : CuntzClass (MatrixLimit A)) : 0 ≤ x := by
  induction x using Quotient.inductionOn with
  | h a => exact CuntzTrace.CuntzBelow.zero a

instance finiteCuntz_isOrderedAddMonoid : IsOrderedAddMonoid (finiteCuntzSubmonoid (A := A)) where
  add_le_add_left _ _ h _ := CuntzClass.matrixAdd_mono h le_rfl

lemma finiteCuntz_zero_le (x : finiteCuntzSubmonoid (A := A)) : 0 ≤ x :=
  sharedCuntz_zero_le x.1

def finitePositiveClass (n : ℕ) (M : Positive (FinMatrix A n)) :
    finiteCuntzSubmonoid (A := A) :=
  ⟨CuntzClass.mk (Positive.map (matrixLimitStage n) M), ⟨n,M,rfl⟩⟩

lemma finitePositiveClass_le_iff (n : ℕ) (M N : Positive (FinMatrix A n)) :
    finitePositiveClass n M ≤ finitePositiveClass n N ↔ CuntzSubequiv M.1 N.1 :=
  shared_finiteClass_order_iff n M N

lemma finitePositiveClass_inclusion {n m : ℕ} (h : n ≤ m) (M : Positive (FinMatrix A n)) :
    finitePositiveClass m (Positive.map (matrixInclusion h) M) = finitePositiveClass n M := by
  apply Subtype.ext
  apply congrArg CuntzClass.mk
  exact Subtype.ext (matrixLimitStage_compatible h M.1)

lemma finitePositiveClass_zero (n : ℕ) :
    finitePositiveClass n (Positive.zero : Positive (FinMatrix A n)) = 0 := by
  apply Subtype.ext
  apply congrArg CuntzClass.mk
  exact Subtype.ext (map_zero (matrixLimitStage n))

lemma finitePositiveClass_add (n : ℕ) (M N : Positive (FinMatrix A n)) :
    finitePositiveClass (n*2) (Positive.map (matrixInterleave n) (positiveProduct M N)) =
      finitePositiveClass n M + finitePositiveClass n N := by
  apply Subtype.ext
  exact (congrArg CuntzClass.mk (matrixBlockPositive_stage n M N)).symm

theorem finiteCuntz_compare_of_buffer
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (L : ℕ) (M N : Positive (FinMatrix A L))
    (c : finiteCuntzSubmonoid (A := A)) (m n k : ℕ) (hmn : m < n)
    (h : n • finitePositiveClass L M + c ≤ m • finitePositiveClass L N + c)
    (hc : c ≤ k • finitePositiveClass L N) : CuntzSubequiv M.1 N.1 := by
  apply (finitePositiveClass_le_iff L M N).mp
  exact strict_multiples_le_of_buffer finiteCuntz_zero_le
    (finiteCuntz_almostUnperforated hAU) hmn h hc

theorem finiteCuntz_state_gap_uniform (u a : finiteCuntzSubmonoid (A := A))
    (h : ∀ f : StateSpace u, f.1 a < 1) :
    ∃ r : ℝ≥0∞, r < 1 ∧ ∀ f : StateSpace u, f.1 a ≤ r :=
  uniform_state_gap u a h
end CuntzPureness

end

end OAI
