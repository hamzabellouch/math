import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBiasSmallness

namespace OAI

/-! # Maximizing translating residues and the little-o conclusion -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

noncomputable def maximizingQuadraticTranslate (S : Finset ℕ) (p : ℕ) : ℕ :=
  Classical.choose (Finset.exists_max_image (Finset.range (p + 1))
    (fun t : ℕ => |residueTestMean S (quadraticResidueTest p t)|)
    (Finset.nonempty_range_iff.mpr (by omega)))

noncomputable def maximalQuadraticBias (S : Finset ℕ) (p : ℕ) : ℝ :=
  |residueTestMean S (quadraticResidueTest p (maximizingQuadraticTranslate S p))|

noncomputable def quadraticBandMass (A : Set ℕ) (N : ℕ) (T : ℝ) : ℝ :=
  ∑ p ∈ logPrimeBand T, (Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p

theorem quadraticResidueTest_translate_congr (p : ℕ) [NeZero p] (t u : ℤ)
    (htu : (t : ZMod p) = (u : ZMod p)) :
    quadraticResidueTest p t = quadraticResidueTest p u := by
  funext r
  rw [quadraticResidueTest_eq_character, quadraticResidueTest_eq_character, htu]

theorem translated_quadratic_bias_le_maximal (S : Finset ℕ) (p : ℕ) [NeZero p] (t : ℤ) :
    |residueTestMean S (quadraticResidueTest p t)| ≤ maximalQuadraticBias S p := by
  have hm := (Classical.choose_spec (Finset.exists_max_image (Finset.range (p + 1))
    (fun t : ℕ => |residueTestMean S (quadraticResidueTest p t)|)
    (Finset.nonempty_range_iff.mpr (by omega)))).2
  have he : (t : ZMod p) = (((t : ZMod p).val : ℕ) : ℤ) := by simp
  rw [quadraticResidueTest_translate_congr p t _ he]
  exact hm _ (Finset.mem_range.mpr (by have := ZMod.val_lt (t : ZMod p); omega))

theorem maximalQuadraticBias_nonneg (S : Finset ℕ) (p : ℕ) : 0 ≤ maximalQuadraticBias S p :=
  abs_nonneg _

theorem maximalQuadraticBias_le_one (S : Finset ℕ) (p : ℕ) : maximalQuadraticBias S p ≤ 1 :=
  residueTestMean_abs_le_one S _ (fun r _ => quadraticResidueTest_abs_le p _ r)

theorem quadraticBandMass_nonneg (A : Set ℕ) (N : ℕ) (T : ℝ) : 0 ≤ quadraticBandMass A N T := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (logPrimeBand_mem hp).1
  exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg _))
    (maximalQuadraticBias_nonneg _ _)

theorem quadraticBandMass_isLittleO
    (hBonami : PublishedBonamiBound) (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C₀ : ℝ) (hM : MertensEstimate C₀)
    (cψ Bψ : ℝ) (hcψ : 0 < cψ) (hBψ : 3 ≤ Bψ) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, Bψ ^ 2 < |x| → 𝓕 ψ x = 0) :
    (fun T => quadraticBandMass A N T) =o[atTop] (fun T : ℝ => T) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hδ : 0 < min c 1 := lt_min hc (by norm_num)
  have hh := eventual_translated_quadratic_bias_lt hBonami P₀ H hSiegel sieve hsize
    hA hB h N hN C₀ hM cψ Bψ hcψ hBψ ψ hreal hψ0 hψ1 hsupp (min c 1) hδ (min_le_right _ _)
  filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with T hh hT
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticBandMass_nonneg A N T), Real.norm_eq_abs, abs_of_nonneg hT]
  exact (hh (fun p => maximizingQuadraticTranslate (tailSupport A N p) p)).le.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hT)

end Ostmann

end OAI
