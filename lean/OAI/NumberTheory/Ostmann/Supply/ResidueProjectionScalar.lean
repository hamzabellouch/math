import OAI.NumberTheory.Ostmann.Supply.SpectralProjectionAffine

namespace OAI

/-! # The negative scalar block between complementary residue supports -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def uniformResidueVector {p : ℕ} (S : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  (((if x ∈ S then 1 else 0) / (S.card : ℝ) : ℝ) : ℂ)

theorem uniformResidueVector_affine {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    uniformResidueVector S x =
      ((Real.sqrt (residueVariance S) / S.card : ℝ) : ℂ) * normalizedResidueIndicator S x +
        ((1 / (p : ℝ) : ℝ) : ℂ) := by
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hv : Real.sqrt (residueVariance S) ≠ 0 :=
    (Real.sqrt_pos.mpr (residueVariance_pos S hS hSp)).ne'
  unfold uniformResidueVector normalizedResidueIndicator centeredDensity
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
  apply congrArg Complex.ofReal
  field_simp
  ring

theorem uniformResidueVector_compl_affine {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    uniformResidueVector (Finset.univ \ S) x =
      ((-Real.sqrt (residueVariance S) / ((p : ℝ) - S.card) : ℝ) : ℂ) *
        normalizedResidueIndicator S x + ((1 / (p : ℝ) : ℝ) : ℂ) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hd : (p : ℝ) - S.card ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hSp.ne')
  have hv : Real.sqrt (residueVariance S) ≠ 0 :=
    (Real.sqrt_pos.mpr (residueVariance_pos S hS hSp)).ne'
  have hc : ((Finset.univ \ S).card : ℝ) = (p : ℝ) - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card,
      Nat.cast_sub hSp.le]
  unfold uniformResidueVector normalizedResidueIndicator centeredDensity
  rw [hc]
  have he : (if x ∈ Finset.univ \ S then (1 : ℝ) else 0) =
      1 - (if x ∈ S then 1 else 0) := by
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
  apply congrArg Complex.ofReal
  field_simp
  ring

theorem finiteSpectralProjection_affine_pairing {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (f : ZMod p → ℂ) (a b c d : ℂ) :
    (∑ x, conj (a * f x + c) *
      finiteSpectralProjection E (fun x => b * f x + d) x) =
      conj a * b * ((∑ x, ‖finiteSpectralProjection E f x‖ ^ 2 : ℝ) : ℂ) := by
  have he := finiteSpectralProjection_selfAdjoint E (fun x => a * f x + c)
    (finiteSpectralProjection E (fun x => b * f x + d))
  rw [finiteSpectralProjection_idempotent] at he
  rw [he, finiteSpectralProjection_affine E hE, finiteSpectralProjection_affine E hE]
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  have hn : conj (finiteSpectralProjection E f x) * finiteSpectralProjection E f x =
      ((‖finiteSpectralProjection E f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
  calc
    _ = conj a * b * (conj (finiteSpectralProjection E f x) * finiteSpectralProjection E f x) := by ring
    _ = _ := by rw [hn]

/-- The raw projection's scalar block is negative with the exact coefficient
`-1/p^2` appearing in the proof of Lemma 5.2. -/
theorem residueProjection_scalar {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E) :
    (∑ x, conj (uniformResidueVector S x) *
      finiteSpectralProjection E (uniformResidueVector (Finset.univ \ S)) x) =
      -((p : ℂ) ^ 2)⁻¹ *
        ((∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 : ℝ) : ℂ) := by
  have hleft : uniformResidueVector S = fun x =>
      ((Real.sqrt (residueVariance S) / S.card : ℝ) : ℂ) * normalizedResidueIndicator S x +
        ((1 / (p : ℝ) : ℝ) : ℂ) := funext (uniformResidueVector_affine S hS hSp)
  have hright : uniformResidueVector (Finset.univ \ S) = fun x =>
      ((-Real.sqrt (residueVariance S) / ((p : ℝ) - S.card) : ℝ) : ℂ) *
        normalizedResidueIndicator S x + ((1 / (p : ℝ) : ℝ) : ℂ) :=
    funext (uniformResidueVector_compl_affine S hS hSp)
  rw [hleft, hright]
  rw [finiteSpectralProjection_affine_pairing E hE]
  congr 1
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hd : (p : ℝ) - S.card ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hSp.ne')
  have hv := Real.sq_sqrt (residueVariance_pos S hS hSp).le
  have he : (Real.sqrt (residueVariance S) / S.card) *
      (-Real.sqrt (residueVariance S) / ((p : ℝ) - S.card)) = -((p : ℝ) ^ 2)⁻¹ := by
    rw [div_mul_div_comm, mul_neg, ← pow_two, hv]
    unfold residueVariance residueDensity
    field_simp
  rw [he]
  push_cast
  rfl

end Ostmann

end OAI
