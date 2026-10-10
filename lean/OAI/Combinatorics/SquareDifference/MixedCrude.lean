import OAI.Combinatorics.SquareDifference.ExceptionalBudget

namespace OAI

section

open Finset Filter

open scoped BigOperators Topology

namespace SquareDifference

open LiftTheory.SquareDifference

lemma crude_rpow_identity (d N : ℕ) (C b η : ℝ) :
    η*(2*(C*(N:ℝ)^b)^(2*d))=η*((2*C^(2*d))*(N:ℝ)^(2*(d:ℝ)*b)) := by
  rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  have he : b*((2*d:ℕ):ℝ)=2*(d:ℝ)*b := by push_cast; ring
  rw [he]
  ring

lemma source_mixed_crude (M : ℕ) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective p → (∀j,tupleMassThreshold≤(p j:ℝ)) →
      ∀(B : Finset J) (A : Finset ℕ) (s : TupleVertex → ZMod M),
      |multilinearIntegral (actualMixedLaw p B)
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v)))|≤
      exceptionalProduct p B*(C*(N:ℝ)^(2*(Fintype.card TupleVertex:ℝ)*sourceLoss (Fintype.card TupleVertex))) := by
  let d := Fintype.card TupleVertex
  obtain ⟨C,hC,hb⟩ := uniform_partial_lift_moments (sourceLoss d) (sourceLoss_pos d)
  let C' := C*(M:ℝ)+1
  have hC' : 1≤C' := by dsimp [C']; nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  refine ⟨2*C'^(2*d),mul_pos (by norm_num) (pow_pos (lt_of_lt_of_le zero_lt_one hC') _),?_⟩
  filter_upwards [eventual_cutoff_size sourceBeta sourceBeta_pos (by norm_num [sourceBeta]),eventually_ge_atTop 1] with N hsz hN
  intro J _ _ p _ hinj hp B A s
  have hR : 1≤C'*(N:ℝ)^(sourceLoss d) := one_le_mul_of_one_le_of_one_le hC'
    (Real.one_le_rpow (by exact_mod_cast hN) (sourceLoss_pos d).le)
  have hm (v : TupleVertex) (r : ℕ) (hr : r+1=d) :
      (𝔼 x,actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v)) x^(2*r))≤
      (C'*(N:ℝ)^(sourceLoss d))^(2*r) := by
    apply (hb p hinj N (powerCutoff N sourceBeta) N hsz
      (powerCutoff_le_self N hN sourceBeta sourceBeta_le) _ M (Nat.cast_nonneg _)
      (fun n _ => smallResidueInput_bound M A (s v) n) _ (Subset.refl _) r (Or.inr hr)).trans
    apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    dsimp [C']; linarith
  have hh := actualMixedLaw_crude p hp B _ _ hR hm
  exact hh.trans_eq (crude_rpow_identity d N C' (sourceLoss d) (exceptionalProduct p B))

end SquareDifference

end

end OAI
