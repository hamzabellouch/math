import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughDyadic

namespace OAI

/-! # The least constant for an actual finite set of quadratic rows -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticRowEnergy (S : Finset ℕ) (N : ℕ) (v : ℕ → ℂ) : ℝ :=
  ∑ m ∈ S, ‖quadraticTransposeSum N v m‖ ^ 2

def QuadraticRowBound (S : Finset ℕ) (N : ℕ) (T : ℝ) : Prop :=
  ∀ v : ℕ → ℂ, quadraticRowEnergy S N v ≤ T * quadraticSieveEnergy N v

noncomputable def quadraticRowNorm (S : Finset ℕ) (N : ℕ) : ℝ :=
  sSup (Set.range fun v : ℕ → ℂ => quadraticRowEnergy S N v / quadraticSieveEnergy N v)

theorem quadraticRowEnergy_nonneg (S : Finset ℕ) (N : ℕ) (v : ℕ → ℂ) :
    0 ≤ quadraticRowEnergy S N v := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem quadraticRowEnergy_trivial (S : Finset ℕ) (N : ℕ) (v : ℕ → ℂ) :
    quadraticRowEnergy S N v ≤ (S.card : ℝ) * N * quadraticSieveEnergy N v := by
  calc
    _ ≤ ∑ _m ∈ S, (N : ℝ) * quadraticSieveEnergy N v :=
      Finset.sum_le_sum (fun _ _ => quadraticTransposeSum_trivial N v _)
    _ = _ := by simp [mul_assoc]

theorem quadraticRow_ratios_bounded (S : Finset ℕ) (N : ℕ) :
    BddAbove (Set.range fun v : ℕ → ℂ =>
      quadraticRowEnergy S N v / quadraticSieveEnergy N v) := by
  refine ⟨(S.card : ℝ) * N, ?_⟩
  rintro y ⟨v, rfl⟩
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hzero : quadraticSieveEnergy N v = 0
  · simp only [hzero, div_zero]
    positivity
  · exact (div_le_iff₀ (lt_of_le_of_ne hE (Ne.symm hzero))).mpr (quadraticRowEnergy_trivial S N v)

theorem quadraticRowNorm_nonneg (S : Finset ℕ) (N : ℕ) : 0 ≤ quadraticRowNorm S N := by
  have hh := le_csSup (quadraticRow_ratios_bounded S N)
    (Set.mem_range_self (f := fun v : ℕ → ℂ =>
      quadraticRowEnergy S N v / quadraticSieveEnergy N v) (fun _ => 0))
  simpa only [quadraticRowNorm, quadraticRowEnergy, quadraticTransposeSum, zero_mul, Finset.sum_const_zero,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] using hh

theorem quadraticRowNorm_bound (S : Finset ℕ) (N : ℕ) :
    QuadraticRowBound S N (quadraticRowNorm S N) := by
  intro v
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hzero : quadraticSieveEnergy N v = 0
  · have ht := quadraticRowEnergy_trivial S N v
    simpa only [hzero, mul_zero] using ht
  · exact (div_le_iff₀ (lt_of_le_of_ne hE (Ne.symm hzero))).mp
      (le_csSup (quadraticRow_ratios_bounded S N) (Set.mem_range_self v))

theorem quadraticRowNorm_le {S : Finset ℕ} {N : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (h : QuadraticRowBound S N T) : quadraticRowNorm S N ≤ T := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨v, rfl⟩
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hzero : quadraticSieveEnergy N v = 0
  · simpa only [hzero, div_zero] using hT
  · exact (div_le_iff₀ (lt_of_le_of_ne hE (Ne.symm hzero))).mpr (h v)

theorem QuadraticRowBound.mono_constant {S : Finset ℕ} {N : ℕ} {T U : ℝ}
    (h : QuadraticRowBound S N T) (hTU : T ≤ U) : QuadraticRowBound S N U := by
  intro v
  exact (h v).trans (mul_le_mul_of_nonneg_right hTU (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end Ostmann

end OAI
