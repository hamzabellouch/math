import OAI.NumberTheory.Ostmann.Tree.PairCoordinates
import OAI.NumberTheory.Ostmann.Tree.PairMellin

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

abbrev ValidUnitPair (p : ℕ) := {dt : (ZMod p)ˣ × (ZMod p)ˣ // dt.2 ≠ 1}

def unitPairArguments (v : ValidUnitPair p) : ZMod p × ZMod p :=
  (pairMobiusValue v.1.1 v.1.2, (v.1.1:ZMod p)/((v.1.2:ZMod p)-1))

theorem unitPairArguments_difference (v : ValidUnitPair p) :
    (unitPairArguments v).1-(unitPairArguments v).2=(v.1.1:ZMod p) := by
  have ht : (v.1.2:ZMod p) ≠ 1 := fun h => v.property (Units.ext h)
  have hh := pair_difference (1:(ZMod p)ˣ) (v.1.1:ZMod p) (v.1.2:ZMod p) ht
  simpa only [unitPairArguments, pairMobiusValue, pairFirst, pairSecond, Units.val_one, one_mul] using hh

theorem unitPairArguments_ratio (v : ValidUnitPair p) :
    (unitPairArguments v).1/(unitPairArguments v).2=(v.1.2:ZMod p) := by
  have ht : (v.1.2:ZMod p) ≠ 1 := fun h => v.property (Units.ext h)
  have hh := pair_ratio (1:(ZMod p)ˣ) (v.1.1:ZMod p) (v.1.2:ZMod p) (Units.ne_zero _) ht
  simpa only [unitPairArguments, pairMobiusValue, pairFirst, pairSecond, Units.val_one, one_mul] using hh

theorem unitPairArguments_injective : Function.Injective (unitPairArguments (p := p)) := by
  intro v w h
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    rw [← unitPairArguments_difference v, ← unitPairArguments_difference w, h]
  · apply Units.ext
    rw [← unitPairArguments_ratio v, ← unitPairArguments_ratio w, h]

theorem bottomPair_total_energy (g : ZMod p → ℂ) (hg0 : g 0=0) :
    (∑ d : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, ‖bottomPair g d t‖^2) ≤
      (∑ x : ZMod p, ‖g x‖^2)^2 := by
  classical
  have hs : (∑ v : ValidUnitPair p, ‖bottomPair g v.1.1 v.1.2‖^2) =
      ∑ dt : (ZMod p)ˣ × (ZMod p)ˣ, ‖bottomPair g dt.1 dt.2‖^2 := by
    apply Fintype.sum_of_injective (fun v : ValidUnitPair p => v.1) Subtype.val_injective
    · intro dt hdt
      have ht : dt.2=1 := by
        by_contra h
        exact hdt ⟨⟨dt,h⟩,rfl⟩
      simp [bottomPair,pairMobiusValue,ht,hg0]
    · intro _
      rfl
  rw [← Fintype.sum_prod_type (f := fun dt : (ZMod p)ˣ × (ZMod p)ˣ => ‖bottomPair g dt.1 dt.2‖^2), ← hs]
  calc
    _ ≤ ∑ xy : ZMod p × ZMod p, ‖g xy.1‖^2*‖g xy.2‖^2 := by
      apply Finset.sum_le_sum_of_injOn unitPairArguments unitPairArguments_injective.injOn
      · exact Finset.subset_univ _
      · intro v _
        simp only [bottomPair, unitPairArguments, norm_mul, Complex.norm_conj, mul_pow, le_refl]
      · intro _ _ _
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]

end
end Ostmann.FiniteField

end OAI
