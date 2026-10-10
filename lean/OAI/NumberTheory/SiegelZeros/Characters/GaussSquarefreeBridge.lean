import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.GaussMinimalPolynomial

namespace OAI


namespace SiegelZeros.W56

theorem exists_squarefree_int_factor (D : ℤ) (hD : D ≠ 0) :
    ∃ d k : ℤ, Squarefree d ∧ 0 < k ∧ D = k ^ 2 * d := by
  obtain ⟨a, b, ha, hb, hab, hsa⟩ :=
    Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hD)
  have habZ : (b : ℤ) ^ 2 * (a : ℤ) = (D.natAbs : ℤ) := by
    exact_mod_cast hab
  have hbZ : 0 < (b : ℤ) := by exact_mod_cast hb
  by_cases hpos : 0 ≤ D
  · refine ⟨(a : ℤ), (b : ℤ), Int.squarefree_natCast.mpr hsa, hbZ, ?_⟩
    rw [Int.natCast_natAbs, abs_of_nonneg hpos] at habZ
    exact habZ.symm
  · refine ⟨-(a : ℤ), (b : ℤ), ?_, hbZ, ?_⟩
    · apply Int.squarefree_natAbs.mp
      simpa using hsa
    · rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hpos)] at habZ
      rw [mul_neg, habZ, neg_neg]

theorem squarefree_factor_natAbs_le (D d k : ℤ) (hk : k ≠ 0)
    (hD : D = k ^ 2 * d) : d.natAbs ≤ D.natAbs := by
  rw [hD, Int.natAbs_mul, Int.natAbs_pow]
  exact Nat.le_mul_of_pos_left _ (pow_pos (Int.natAbs_pos.mpr hk) _)

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

omit [Algebra ℚ K] in
theorem normalized_root_sq (D d k : ℤ) (a : K)
    (hk : k ≠ 0) (hD : D = k ^ 2 * d) (ha : a ^ 2 = (D : K)) :
    (a / (k : K)) ^ 2 = (d : K) := by
  have hkK : (k : K) ≠ 0 := Int.cast_ne_zero.mpr hk
  rw [div_pow, ha, hD]
  push_cast
  field_simp

theorem adjoin_normalized_root_eq (a : K) (k : ℤ) (hk : k ≠ 0) :
    IntermediateField.adjoin ℚ ({a / (k : K)} : Set K) =
      IntermediateField.adjoin ℚ ({a} : Set K) := by
  have hkK : (k : K) ≠ 0 := Int.cast_ne_zero.mpr hk
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    exact (IntermediateField.adjoin ℚ ({a} : Set K)).div_mem
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton a))
      ((IntermediateField.adjoin ℚ ({a} : Set K)).intCast_mem k)
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    have hn := (IntermediateField.adjoin ℚ ({a / (k : K)} : Set K)).mul_mem
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton (a / (k : K))))
      ((IntermediateField.adjoin ℚ ({a / (k : K)} : Set K)).intCast_mem k)
    simpa [div_mul_cancel₀ _ hkK] using hn

theorem exists_squarefree_root_same_field (D : ℤ) (hD : D ≠ 0)
    (a : K) (ha : a ^ 2 = (D : K)) :
    ∃ (d k : ℤ) (b : K), Squarefree d ∧ k ≠ 0 ∧ D = k ^ 2 * d ∧
      b = a / (k : K) ∧ b ^ 2 = (d : K) ∧
      IntermediateField.adjoin ℚ ({b} : Set K) =
        IntermediateField.adjoin ℚ ({a} : Set K) := by
  obtain ⟨d, k, hd, hk, hfact⟩ := exists_squarefree_int_factor D hD
  exact ⟨d, k, a / (k : K), hd, ne_of_gt hk, hfact, rfl,
    normalized_root_sq D d k a (ne_of_gt hk) hfact ha,
    adjoin_normalized_root_eq a k (ne_of_gt hk)⟩

end SiegelZeros.W56



namespace SiegelZeros.W56

open SiegelZerosAwei.W09

theorem root_radicand_ne_one {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (b : K) (d : ℤ) (hb : b ^ 2 = (d : K))
    (hdegree : Module.finrank ℚ (IntermediateField.adjoin ℚ ({b} : Set K)) = 2) :
    d ≠ 1 := by
  intro hd
  have hs : b ^ 2 = 1 := by simpa [hd] using hb
  have hbot : IntermediateField.adjoin ℚ ({b} : Set K) = ⊥ := by
    apply IntermediateField.adjoin_simple_eq_bot_iff.mpr
    rcases sq_eq_one_iff.mp hs with h | h
    · rw [h]
      exact (⊥ : IntermediateField ℚ K).one_mem
    · rw [h]
      exact (⊥ : IntermediateField ℚ K).neg_mem (⊥ : IntermediateField ℚ K).one_mem
  rw [hbot, IntermediateField.finrank_bot] at hdegree
  norm_num at hdegree

theorem characterField_squarefree_radicand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    ∃ (d k : ℤ) (b : ℂ), Squarefree d ∧ d ≠ 1 ∧ k ≠ 0 ∧
      signedConductor χ = k ^ 2 * d ∧ d.natAbs ≤ q ∧
      b = characterGaussSum χ / (k : ℂ) ∧ b ^ 2 = (d : ℂ) ∧
      IntermediateField.adjoin ℚ ({b} : Set ℂ) = characterField χ := by
  obtain ⟨d, k, b, hd, hk, hfact, hbdef, hb, hfield⟩ :=
    exists_squarefree_root_same_field (signedConductor χ) (signedConductor_ne_zero χ)
      (characterGaussSum χ) (characterGaussSum_sq_signedConductor χ hp hq)
  have hf : IntermediateField.adjoin ℚ ({b} : Set ℂ) = characterField χ := hfield
  have hdegree : Module.finrank ℚ (IntermediateField.adjoin ℚ ({b} : Set ℂ)) = 2 := by
    rw [hf]
    exact characterField_finrank χ hp hq hn
  refine ⟨d, k, b, hd, root_radicand_ne_one b d hb hdegree, hk, hfact, ?_,
    hbdef, hb, hf⟩
  simpa [signedConductor_natAbs] using
    squarefree_factor_natAbs_le (signedConductor χ) d k hk hfact

end SiegelZeros.W56

end OAI
