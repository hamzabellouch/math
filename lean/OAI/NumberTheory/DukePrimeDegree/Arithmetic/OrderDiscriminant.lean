import OAI.NumberTheory.DukePrimeDegree.Arithmetic.FullLattice
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.Arithmetic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-!
# The multiplier-order index

The conductor inclusion bounds the index of the multiplier order by
`q^n`. This is the integer-index part of the discriminant-scale bound in
Section 2 of paper 031-01. The discriminant is expressed by the usual
index formula `|disc K| [O_K : O(M)]²`.
-/

open scoped NumberField

namespace DukePrimeDegree

variable {K : Type*} [Field K] [NumberField K]

/-- The multiplier order as a submodule of the maximal order. -/
def integralMultiplierLattice (M : Submodule ℤ K) : Submodule ℤ (𝓞 K) :=
  (multiplierOrder M).toSubmodule.comap
    (algebraMap (𝓞 K) K).toAddMonoidHom.toIntLinearMap

/-- Index of the multiplier order inside the maximal order. -/
noncomputable def multiplierIndex (M : Submodule ℤ K) : ℕ :=
  (integralMultiplierLattice M).toAddSubgroup.index

omit [NumberField K] in
lemma range_nsmul_le_integralMultiplierLattice (M : Submodule ℤ K) :
    (nsmulAddMonoidHom (α := 𝓞 K) (saturationIndex M)).range ≤
      (integralMultiplierLattice M).toAddSubgroup := by
  rintro a ⟨r, rfl⟩
  change ((saturationIndex M • r : 𝓞 K) : K) ∈ multiplierOrder M
  simpa using
    saturationIndex_mul_integer_mem_multiplierOrder M r

/-- The index bound does not require an invertible module over the
multiplier order. It uses only the full-lattice property. -/
lemma FullLattice.multiplierIndex_le (M : FullLattice K) :
    multiplierIndex M.toSubmodule ≤
      saturationIndex M.toSubmodule ^ Module.finrank ℚ K := by
  have hq : saturationIndex M.toSubmodule ≠ 0 := M.saturationIndex_pos.ne'
  have hdiv := AddSubgroup.index_dvd_of_le
    (range_nsmul_le_integralMultiplierLattice M.toSubmodule)
  rw [AddSubgroup.index_range_nsmul, NumberField.RingOfIntegers.rank] at hdiv
  exact Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hq) _) hdiv

lemma FullLattice.multiplierIndex_pos (M : FullLattice K) :
    0 < multiplierIndex M.toSubmodule := by
  have hdiv := AddSubgroup.index_dvd_of_le
    (range_nsmul_le_integralMultiplierLattice M.toSubmodule)
  rw [AddSubgroup.index_range_nsmul] at hdiv
  exact Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero
    (pow_ne_zero _ M.saturationIndex_pos.ne') hdiv)

/-- The absolute order discriminant in the index convention. -/
noncomputable def multiplierDiscriminant (M : Submodule ℤ K) : ℕ :=
  (NumberField.discr K).natAbs * multiplierIndex M ^ 2

lemma FullLattice.multiplierDiscriminant_le (M : FullLattice K) :
    multiplierDiscriminant M.toSubmodule ≤
      (NumberField.discr K).natAbs *
        saturationIndex M.toSubmodule ^ (2 * Module.finrank ℚ K) := by
  unfold multiplierDiscriminant
  apply Nat.mul_le_mul_left
  calc
    multiplierIndex M.toSubmodule ^ 2 ≤
        (saturationIndex M.toSubmodule ^ Module.finrank ℚ K) ^ 2 :=
      Nat.pow_le_pow_left M.multiplierIndex_le 2
    _ = saturationIndex M.toSubmodule ^ (2 * Module.finrank ℚ K) := by
      rw [← pow_mul, Nat.mul_comm]

/-- The unfolding scale `Q = [O_K M : M] √|disc K|`. -/
noncomputable def arithmeticScale (M : Submodule ℤ K) : ℝ :=
  (saturationIndex M : ℝ) * Real.sqrt (NumberField.discr K).natAbs

lemma FullLattice.arithmeticScale_pos (M : FullLattice K) :
    0 < arithmeticScale M.toSubmodule := by
  apply mul_pos (Nat.cast_pos.mpr M.saturationIndex_pos)
  apply Real.sqrt_pos_of_pos
  exact Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))

/-- The discriminant grows no faster than the `2n`th power of the
unfolding scale. No discriminant lower bound beyond nonvanishing is used. -/
lemma FullLattice.multiplierDiscriminant_le_scale (M : FullLattice K) :
    (multiplierDiscriminant M.toSubmodule : ℝ) ≤
      arithmeticScale M.toSubmodule ^ (2 * Module.finrank ℚ K) := by
  let d : ℝ := (NumberField.discr K).natAbs
  let q : ℝ := saturationIndex M.toSubmodule
  have hd : 1 ≤ d := by
    change (1 : ℝ) ≤ (NumberField.discr K).natAbs
    exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hd_pow : d ≤ d ^ Module.finrank ℚ K := le_self_pow₀ hd hn.ne'
  have hbound : (multiplierDiscriminant M.toSubmodule : ℝ) ≤
      d * q ^ (2 * Module.finrank ℚ K) := by
    dsimp only [d, q]
    exact_mod_cast M.multiplierDiscriminant_le
  calc
    (multiplierDiscriminant M.toSubmodule : ℝ) ≤
        d * q ^ (2 * Module.finrank ℚ K) := hbound
    _ ≤ d ^ Module.finrank ℚ K * q ^ (2 * Module.finrank ℚ K) :=
      mul_le_mul_of_nonneg_right hd_pow (pow_nonneg (Nat.cast_nonneg _) _)
    _ = arithmeticScale M.toSubmodule ^ (2 * Module.finrank ℚ K) := by
      change d ^ Module.finrank ℚ K * q ^ (2 * Module.finrank ℚ K) =
        (q * Real.sqrt d) ^ (2 * Module.finrank ℚ K)
      rw [mul_pow, pow_mul (Real.sqrt d) 2, Real.sq_sqrt (zero_le_one.trans hd)]
      ring

open Filter in
/-- For a fixed degree, divergence of order discriminants forces the
unfolding scale to diverge, including sequences in a fixed number field. -/
theorem arithmeticScale_tendsto_atTop
    (K : ℕ → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    (M : ∀ i, FullLattice (K i)) (n : ℕ)
    (hn : ∀ i, Module.finrank ℚ (K i) = n)
    (hD : Tendsto (fun i => (multiplierDiscriminant (M i).toSubmodule : ℝ)) atTop atTop) :
    Tendsto (fun i => arithmeticScale (M i).toSubmodule) atTop atTop := by
  apply scale_tendsto_atTop (k := 2 * n)
    (fun i => (M i).arithmeticScale_pos.le)
  · intro i
    simpa only [hn i] using (M i).multiplierDiscriminant_le_scale
  · exact hD

end DukePrimeDegree

end OAI
