import OAI.Algebra.Finitistic.Bar.SuffixParityFaces
import OAI.Algebra.Finitistic.Bar.PatternTensorCoherence

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]
local notation "A" => TrivSqZeroExt D X
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

omit [IsScalarTower k D N] [IsScalarTower k A N] in
/-- Every literal recursive suffix has its original D action. -/
theorem patternEmbed_smul (p : List Bool)
    (hbase : ∀ (d : D) (v : N), (inl d : A) • v = d • v)
    (d : D) (v : patternTerm k D X N p) :
    embed k D X N p (d • v) = (inl d : A) • embed k D X N p v := by
  cases p with
  | nil => exact (hbase d v).symm
  | cons b p =>
    cases b <;> induction v using TensorProduct.inductionOn with
    | tmul a v =>
      first
      | change (inl (d*a) : A) ⊗ₜ[k] _ = ((inl d : A)*inl a) ⊗ₜ[k] _
        rw [inl_mul_inl]
      | change (inr (d • a) : A) ⊗ₜ[k] _ = ((inl d : A)*inr a) ⊗ₜ[k] _
        rw [inl_mul_inr]
    | add v w hv hw => simp only [smul_add, map_add, hv, hw]

omit [Module D N] [IsScalarTower k D N] [IsScalarTower k A N] in
/-- The leading X annihilates any X-leading suffix, irrespective of later blocks. -/
theorem patternEmbed_ideal_zero (p : List Bool) (x : X)
    (v : patternTerm k D X N (true :: p)) :
    (inr x : A) • embed k D X N (true :: p) v = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul y v =>
    change ((inr x : A)*inr y) ⊗ₜ[k] _ = 0
    rw [inr_mul_inr, TensorProduct.zero_tmul]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw, add_zero]

omit [Module D N] [IsScalarTower k D N] [IsScalarTower k A N] in
/-- Compatibility of every X-leading recursive suffix needs no condition at N. -/
theorem idealPatternEmbed_smul (p : List Bool) (d : D)
    (v : patternTerm k D X N (true :: p)) :
    embed k D X N (true :: p) (d • v) =
      (inl d : A) • embed k D X N (true :: p) v := by
  induction v using TensorProduct.inductionOn with
  | tmul x v =>
    change (inr (d • x) : A) ⊗ₜ[k] _ = ((inl d : A)*inr x) ⊗ₜ[k] _
    rw [inl_mul_inr]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw]

omit [Module D N] [IsScalarTower k D N] in
/-- All later X and D blocks are admitted literally, with no assumed chain comparison. -/
theorem parity_recursiveSuffix (p : List Bool) (n : ℕ)
    (v : X ⊗[k] term k D (patternTerm k D X N (true :: p)) (n+1)) :
    let M := patternTerm k D X N (true :: p)
    let e := embed k D X N (true :: p)
    SquareZero.multibarAugmentedDifferential k D X N (((p.length+1)+n)+1)
      (idealSuffixEmbed k D X N M (p.length+1) (n+1) e v) =
    -idealSuffixEmbed k D X N M (p.length+1) n e (BimoduleTensor.barDifferential k D X M n v) +
      (-1 : k)^(n+1) • termCast k D X N
        (show (p.length+(n+1))+1=((p.length+1)+n)+1 by omega)
        (idealSuffixEmbed k D X N M p.length (n+1)
          ((SquareZero.multibarAugmentedDifferential k D X N p.length).comp e) v) := by
  exact parity_idealSuffixEmbed k D X N _ p.length n _
    (idealPatternEmbed_smul k D X N p) v

omit [Module D N] [IsScalarTower k D N] in
/-- Empty intervening D blocks retain exactly the later suffix differential. -/
theorem parity_recursiveSuffix_zero (p : List Bool)
    (v : X ⊗[k] patternTerm k D X N (true :: p)) :
    SquareZero.multibarAugmentedDifferential k D X N (p.length+1)
      (idealSuffixEmbed k D X N _ (p.length+1) 0 (embed k D X N (true :: p)) v) =
    idealSuffixEmbed k D X N _ p.length 0
      ((SquareZero.multibarAugmentedDifferential k D X N p.length).comp
        (embed k D X N (true :: p))) v := by
  exact parity_idealSuffixEmbed_zero k D X N _ p.length _
    (patternEmbed_ideal_zero k D X N p) v
end DerivedBar.ParityBridge

end

end OAI
