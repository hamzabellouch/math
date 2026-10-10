import OAI.NumberTheory.Ostmann.Supply.ResidueKernelNormBounds
import OAI.NumberTheory.Ostmann.Characters.SparseKernelScalar

namespace OAI

/-! # Bounds for the actual balanced-support local kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem balanced_uniform_norms {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3) :
    residueVectorNorm (uniformResidueVector S) ≤ 2 / Real.sqrt (p : ℝ) ∧
      residueVectorNorm (uniformResidueVector (Finset.univ \ S)) ≤ 2 / Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hScard : (p : ℝ) / 3 ≤ S.card := by
    rw [residueDensity, le_div_iff₀ hp] at hlo
    linarith
  have hTcard : ((Finset.univ \ S).card : ℝ) = (p : ℝ) - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card,
      Nat.cast_sub hSp.le]
  have hT : (Finset.univ \ S).Nonempty := by
    rw [← Finset.card_pos]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card]
    omega
  refine ⟨uniformResidueVector_norm_le S hS hScard, uniformResidueVector_norm_le _ hT ?_⟩
  rw [hTcard]
  rw [residueDensity, div_le_iff₀ hp] at hhi
  linarith

theorem residue_side_norm_of_energy {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (henergy : (∑ x, ‖f x‖ ^ 2) ≤ 2 * ε ^ 2 / p) :
    residueVectorNorm f ≤ 2 * ε / Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (residueVectorNorm_le_iff _ _ (by positivity)).mpr
  apply henergy.trans
  rw [div_pow, Real.sq_sqrt hp.le, mul_pow]
  apply (div_le_div_iff_of_pos_right hp).mpr
  nlinarith [sq_nonneg ε]

theorem residueProjection_side_norms {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : (∑ x, ‖normalizedResidueIndicator S x -
      finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ ε ^ 2 * p) :
    residueVectorNorm (centeredSupportProjection (Finset.univ \ S)
      (finiteSpectralProjection E (uniformResidueVector S))) ≤ 2 * ε / Real.sqrt (p : ℝ) ∧
    residueVectorNorm (centeredSupportProjection S
      (finiteSpectralProjection E (uniformResidueVector (Finset.univ \ S)))) ≤
        2 * ε / Real.sqrt (p : ℝ) := by
  obtain ⟨ha, hb⟩ := residueProjection_side_energy S E hS hSp hE hlo hhi ε herr
  exact ⟨residue_side_norm_of_energy _ ε hε ha, residue_side_norm_of_energy _ ε hε hb⟩

/-- The squared kernel's scalar contribution is O(epsilon/p), rather than
O(epsilon). This retains both uniform-support normalization factors. -/
theorem squareKernel_scalar_norm_le {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (t ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p) :
    ‖residueKernelScalar S (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x)‖ ≤
      4 * t ^ 2 * ε / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨ha, hb⟩ := balanced_uniform_norms S hS hSp hlo hhi
  unfold residueKernelScalar
  apply (residueVectorNorm_inner_le _ _).trans
  have hraw := residueVectorNorm_raw_le
    (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x)
    (uniformResidueVector (Finset.univ \ S)) (t ^ 2 * ε) (mul_nonneg (sq_nonneg _) hε)
    (sparseAdditiveKernel_square_multiplier_le E t ε hE)
  calc
    _ ≤ (2 / Real.sqrt (p : ℝ)) * ((t ^ 2 * ε) * (2 / Real.sqrt (p : ℝ))) :=
      mul_le_mul ha (hraw.trans (mul_le_mul_of_nonneg_left hb (by positivity)))
        (residueVectorNorm_nonneg _) (by positivity)
    _ = _ := by
      have hs := Real.sq_sqrt hp.le
      field_simp
      rw [hs]
      ring

end Ostmann

end OAI
