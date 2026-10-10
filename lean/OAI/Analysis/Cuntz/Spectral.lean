import OAI.Analysis.Cuntz.SquareCutoff
import OAI.Analysis.Cuntz.Translation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

namespace OAI

noncomputable section

/-! Spectral candidates on squares, orthogonal elements, and complex elements. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

local instance matrixNonUnitalRealFunctionalCalculus {ν : Type*} [Fintype ν] [DecidableEq ν] :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ν ν A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance matrixNonnegSpectrum {ν : Type*} [Fintype ν] [DecidableEq ν] :
    NonnegSpectrumClass ℝ (CStarMatrix ν ν A) := CStarAlgebra.instNonnegSpectrumClass'

namespace CuntzDimensionState

/-- The spectral distributions of rectangular Gram matrices agree at
all strictly positive thresholds, not just on the uncut matrices. -/
theorem distribution_rectangular_gram (d : CuntzDimensionState A) {n m : ℕ}
    (x : Matrix (Fin n) (Fin m) A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) {t : ℝ} (ht : 0 < t) :
    d.distribution ⟨n, x*x.conjTranspose, ha⟩ t =
      d.distribution ⟨m, x.conjTranspose*x, hb⟩ t :=
  d.regularized_eq (cuntzEquivalent_cutoff_rectangular_gram x ha hb ht)

/-- The spectral integral satisfies square swapping in unequal sizes. -/
theorem spectralValue_rectangular_gram (d : CuntzDimensionState A) {n m : ℕ}
    (x : Matrix (Fin n) (Fin m) A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) :
    d.spectralValue ⟨n, x*x.conjTranspose, ha⟩ =
      d.spectralValue ⟨m, x.conjTranspose*x, hb⟩ := by
  let a : CuntzPositiveMatrix A := ⟨n, x*x.conjTranspose, ha⟩
  let b : CuntzPositiveMatrix A := ⟨m, x.conjTranspose*x, hb⟩
  let R := ‖CStarMatrix.ofMatrix a.matrix‖ + ‖CStarMatrix.ofMatrix b.matrix‖
  have hR : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ R := le_add_of_nonneg_right (norm_nonneg _)
  have hR' : ‖CStarMatrix.ofMatrix b.matrix‖ ≤ R := le_add_of_nonneg_left (norm_nonneg _)
  rw [d.spectralValue_eq_integral a hR, d.spectralValue_eq_integral b hR']
  apply intervalIntegral.integral_congr_Ioo_of_le (le_trans (norm_nonneg _) hR)
  intro t ht
  exact d.distribution_rectangular_gram x ha hb ht.1

/-- In particular, the original square-swap axiom holds on the positive squares. -/
theorem spectralValue_square_swap (d : CuntzDimensionState A) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (x*star x), mul_star_self_nonneg x⟩ =
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (star x*x), star_mul_self_nonneg x⟩ :=
  d.spectralValue_rectangular_gram (CStarMatrix.ofMatrix.symm x) _ _

end CuntzDimensionState

/-- An orthogonal positive sum and its diagonal block form are exactly the two
Gram matrices of a rectangular matrix of square roots. -/
theorem exists_orthogonal_sum_gram {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a*b = 0) :
    ∃ v : Matrix (Fin n) (Fin (n+n)) A,
      v*v.conjTranspose = CStarMatrix.ofMatrix.symm (a+b) ∧
      v.conjTranspose*v =
        (CuntzPositiveMatrix.add ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩
          ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩).matrix := by
  let S := CFC.sqrt a
  let T := CFC.sqrt b
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hT : star T = T := (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have hST : S*T = 0 := sqrt_mul_sqrt_eq_zero_of_mul_eq_zero ha hb hab
  have hTS : T*S = 0 := by simpa only [star_mul, hS, hT, star_zero] using congrArg star hST
  let w := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
  have hl : w*w.conjTranspose = CStarMatrix.ofMatrix.symm (a+b) := by
    dsimp [w]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
    have he : S * star S + T * star T = a + b := by
      rw [hS, hT, CFC.sqrt_mul_sqrt_self a ha, CFC.sqrt_mul_sqrt_self b hb]
    exact he
  have hr : w.conjTranspose*w = cuntzBlock (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b) := by
    dsimp [w]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols]
    have hSS : star S * S = a := by rw [hS]; exact CFC.sqrt_mul_sqrt_self a ha
    have hTT : star T * T = b := by rw [hT]; exact CFC.sqrt_mul_sqrt_self b hb
    have hST' : star S * T = 0 := by rw [hS]; exact hST
    have hTS' : star T * S = 0 := by rw [hT]; exact hTS
    have he := congrArg₂ (fun u v : CStarMatrix (Fin n) (Fin n) A =>
      Matrix.fromBlocks (CStarMatrix.ofMatrix.symm u) (0 : Matrix (Fin n) (Fin n) A)
        (0 : Matrix (Fin n) (Fin n) A) (CStarMatrix.ofMatrix.symm v)) hSS hTT
    change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm (star S * S))
      (CStarMatrix.ofMatrix.symm (star S * T)) (CStarMatrix.ofMatrix.symm (star T * S))
      (CStarMatrix.ofMatrix.symm (star T * T)) = _
    rw [hST', hTS']
    exact he
  refine ⟨w.submatrix (Equiv.refl _) finSumFinEquiv.symm, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hl]
    rfl
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hr]
    rfl

/-- Orthogonal additivity for the spectral integral follows from its proved
rectangular square swap and block additivity. -/
theorem CuntzDimensionState.spectralValue_orthogonal_add (d : CuntzDimensionState A) {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a*b = 0) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ =
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  let pa : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩
  let pb : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩
  obtain ⟨v, hv, hw⟩ := exists_orthogonal_sum_gram a b ha hb hab
  have hp : 0 ≤ CStarMatrix.ofMatrix (v*v.conjTranspose) := by rw [hv]; exact add_nonneg ha hb
  have hq : 0 ≤ CStarMatrix.ofMatrix (v.conjTranspose*v) := by rw [hw]; exact (pa.add pb).nonneg
  have h := d.spectralValue_rectangular_gram v hp hq
  rw [← d.spectralValue_add pa pb]
  simpa only [hv, hw, pa, pb, CuntzPositiveMatrix.add] using h

namespace CuntzDimensionState

/-- The spectral value in a fixed matrix size, on the genuine positive cone. -/
def positiveValue (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) : ℝ :=
  d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩

@[simp] theorem positiveValue_zero (d : CuntzDimensionState A) (n : ℕ) :
    d.positiveValue (0 : CStarMatrix (Fin n) (Fin n) A) le_rfl = 0 := by
  simp [positiveValue, spectralValue]

/-- The same positive construction gives a canonical signed value by positive
and negative parts. Additivity on general commuting elements is not assumed. -/
def signedValue (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) : ℝ :=
  d.positiveValue a⁺ (CFC.posPart_nonneg a) - d.positiveValue a⁻ (CFC.negPart_nonneg a)

theorem signedValue_of_nonneg (d : CuntzDimensionState A) {n : ℕ}
    {a : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) :
    d.signedValue a = d.positiveValue a ha := by
  unfold signedValue
  simp only [(CFC.posPart_eq_self a).mpr ha, (CFC.negPart_eq_zero_iff a ha.isSelfAdjoint).mpr ha,
    d.positiveValue_zero, sub_zero]

@[simp] theorem signedValue_zero (d : CuntzDimensionState A) (n : ℕ) :
    d.signedValue (0 : CStarMatrix (Fin n) (Fin n) A) = 0 := by
  rw [d.signedValue_of_nonneg le_rfl, d.positiveValue_zero]

@[simp] theorem signedValue_neg (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) : d.signedValue (-a) = -d.signedValue a := by
  simp only [signedValue, CFC.posPart_neg, CFC.negPart_neg, neg_sub]

/-- Real scalar homogeneity holds for the signed construction. -/
theorem signedValue_smul (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) (r : ℝ) : d.signedValue (r • a) = r*d.signedValue a := by
  have hp (b : CStarMatrix (Fin n) (Fin n) A) (hb : 0 ≤ b) (s : ℝ) (hs : 0 ≤ s) :
      d.positiveValue (s • b) (smul_nonneg hs hb) = s*d.positiveValue b hb :=
    d.spectralValue_scale ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ s hs
  rcases le_total 0 r with hr | hr
  · simp only [signedValue, CFC.posPart_smul_of_nonneg hr, CFC.negPart_smul_of_nonneg hr,
      hp a⁺ (CFC.posPart_nonneg a) r hr, hp a⁻ (CFC.negPart_nonneg a) r hr,
      mul_sub]
  · simp only [signedValue, CFC.posPart_smul_of_nonpos hr, CFC.negPart_smul_of_nonpos hr,
      hp a⁺ (CFC.posPart_nonneg a) (-r) (neg_nonneg.mpr hr),
      hp a⁻ (CFC.negPart_nonneg a) (-r) (neg_nonneg.mpr hr)]
    ring

/-- A sharp size times norm bound, since both positive-part values lie in
[0, size times norm]. -/
theorem abs_signedValue_le (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) : |d.signedValue a| ≤ ‖a‖ * n := by
  have hp := d.spectralValue_nonneg ⟨n, CStarMatrix.ofMatrix.symm a⁺, CFC.posPart_nonneg a⟩
  have hn := d.spectralValue_nonneg ⟨n, CStarMatrix.ofMatrix.symm a⁻, CFC.negPart_nonneg a⟩
  have hp' := d.spectralValue_le_norm_mul_size ⟨n, CStarMatrix.ofMatrix.symm a⁺, CFC.posPart_nonneg a⟩
  have hn' := d.spectralValue_le_norm_mul_size ⟨n, CStarMatrix.ofMatrix.symm a⁻, CFC.negPart_nonneg a⟩
  have hpp := mul_le_mul_of_nonneg_right (CStarAlgebra.norm_posPart_le a) (Nat.cast_nonneg (α := ℝ) n)
  have hnn := mul_le_mul_of_nonneg_right (CStarAlgebra.norm_negPart_le a) (Nat.cast_nonneg (α := ℝ) n)
  change |d.positiveValue a⁺ _ - d.positiveValue a⁻ _| ≤ _
  change 0 ≤ d.positiveValue a⁺ _ at hp
  change 0 ≤ d.positiveValue a⁻ _ at hn
  change d.positiveValue a⁺ _ ≤ ‖a⁺‖ * n at hp'
  change d.positiveValue a⁻ _ ≤ ‖a⁻‖ * n at hn'
  apply abs_le.mpr
  constructor
  · simpa only [zero_sub] using sub_le_sub hp (hn'.trans hnn)
  · simpa only [sub_zero] using sub_le_sub (hp'.trans hpp) hn


/-- A single complex-valued extension of the spectral construction in every
finite matrix size. Abelian linearity is not asserted by this definition. -/
def complexValue (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) : ℂ :=
  (d.signedValue (ℜ a : CStarMatrix (Fin n) (Fin n) A) : ℂ) +
    Complex.I * (d.signedValue (ℑ a : CStarMatrix (Fin n) (Fin n) A) : ℂ)

theorem complexValue_selfAdjoint (d : CuntzDimensionState A) {n : ℕ}
    {a : CStarMatrix (Fin n) (Fin n) A} (ha : IsSelfAdjoint a) :
    d.complexValue a = (d.signedValue a : ℂ) := by
  simp [complexValue, ha.coe_realPart, ha.imaginaryPart]

theorem complexValue_of_nonneg (d : CuntzDimensionState A) {n : ℕ}
    {a : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) :
    d.complexValue a = (d.positiveValue a ha : ℂ) := by
  rw [d.complexValue_selfAdjoint ha.isSelfAdjoint, d.signedValue_of_nonneg ha]

@[simp] theorem complexValue_zero (d : CuntzDimensionState A) (n : ℕ) :
    d.complexValue (0 : CStarMatrix (Fin n) (Fin n) A) = 0 := by
  simp [complexValue]

/-- The original real/imaginary axiom, without assuming that h and k commute. -/
theorem complexValue_real_imag (d : CuntzDimensionState A) {n : ℕ}
    (h k : CStarMatrix (Fin n) (Fin n) A) (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k) :
    d.complexValue (h + Complex.I • k) = d.complexValue h + Complex.I * d.complexValue k := by
  rw [d.complexValue_selfAdjoint hh, d.complexValue_selfAdjoint hk]
  simp [complexValue, map_add, hh.coe_realPart, hh.imaginaryPart, hk.coe_realPart, hk.imaginaryPart]

/-- Nonnegativity of squares for the single whole-matrix construction. -/
theorem complexValue_square_nonneg (d : CuntzDimensionState A) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) : 0 ≤ d.complexValue (star x*x) := by
  rw [d.complexValue_of_nonneg (star_mul_self_nonneg x)]
  exact_mod_cast d.spectralValue_nonneg ⟨n, CStarMatrix.ofMatrix.symm (star x*x), star_mul_self_nonneg x⟩

/-- Square swapping for the same whole-matrix construction. -/
theorem complexValue_square_swap (d : CuntzDimensionState A) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) :
    d.complexValue (star x*x) = d.complexValue (x*star x) := by
  rw [d.complexValue_of_nonneg (star_mul_self_nonneg x), d.complexValue_of_nonneg (mul_star_self_nonneg x)]
  exact congrArg (fun r : ℝ => (r : ℂ)) (d.spectralValue_square_swap x).symm

theorem complexValue_one (d : CuntzDimensionState A) (n : ℕ) :
    d.complexValue (1 : CStarMatrix (Fin n) (Fin n) A) = (n : ℂ) := by
  rw [d.complexValue_of_nonneg zero_le_one]
  change (d.spectralValue (.unit n) : ℂ) = _
  rw [d.spectralValue_unit]
  norm_cast

/-- The uniform bound needed for compact finite-constraint candidates. -/
theorem norm_complexValue_le (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) : ‖d.complexValue a‖ ≤ 2*‖a‖*n := by
  have hr := d.abs_signedValue_le (ℜ a : CStarMatrix (Fin n) (Fin n) A)
  have hi := d.abs_signedValue_le (ℑ a : CStarMatrix (Fin n) (Fin n) A)
  have hr' : ‖(ℜ a : CStarMatrix (Fin n) (Fin n) A)‖ * (n : ℝ) ≤ ‖a‖ * n :=
    mul_le_mul_of_nonneg_right (realPart.norm_le a) (Nat.cast_nonneg n)
  have hi' : ‖(ℑ a : CStarMatrix (Fin n) (Fin n) A)‖ * (n : ℝ) ≤ ‖a‖ * n :=
    mul_le_mul_of_nonneg_right (imaginaryPart.norm_le a) (Nat.cast_nonneg n)
  have hn := norm_add_le (d.signedValue (ℜ a : CStarMatrix (Fin n) (Fin n) A) : ℂ)
    (Complex.I * (d.signedValue (ℑ a : CStarMatrix (Fin n) (Fin n) A) : ℂ))
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at hn
  change ‖d.complexValue a‖ ≤ _ at hn
  linarith

end CuntzDimensionState
end Kaplansky

end

end OAI
