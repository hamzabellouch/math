import OAI.Analysis.TracialSplitting.SpectralLayers

namespace OAI

universe uA uD uI uι uκ

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section MatrixTools

variable {ι : Type uι} {κ : Type uκ} {D : Type uD} [Fintype ι] [Fintype κ]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

open CStarMatrix WithCStarModule in

lemma matrix_norm_le_sum (M : CStarMatrix ι κ D) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [toCLM_apply_eq_sum, Finset.sum_mul]
  apply pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v j

lemma matrix_norm_le_card_mul {M : CStarMatrix ι κ D} {ε : ℝ}
    (h : ∀ i j, ‖M i j‖ ≤ ε) :
    ‖M‖ ≤ Fintype.card ι * Fintype.card κ * ε := by
  refine (matrix_norm_le_sum M).trans ?_
  calc
    _ ≤ ∑ _ : κ, ∑ _ : ι, ε := by gcongr with j _ i _; exact h i j
    _ = _ := by simp; ring

end MatrixTools

section MatrixPos

open scoped MatrixOrder

variable {ι : Type uι} {D : Type uD} [Fintype ι] [DecidableEq ι]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

local instance : IsometricContinuousFunctionalCalculus ℝ (CStarMatrix ι ι D)
    IsSelfAdjoint := IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ (CStarMatrix ι ι D) :=
  CStarAlgebra.instNonnegSpectrumClass

lemma positiveFunctional_matrix_nonneg (f : D →ₚ[ℂ] ℂ)
    {M : CStarMatrix ι ι D} (hM : 0 ≤ M) : 0 ≤ M.mapₗ (f : D →ₗ[ℂ] ℂ) := by
  obtain ⟨X, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
  have hG (k : ι) : 0 ≤ CStarMatrix.ofMatrix
      (Matrix.gram ℂ (fun i => f.toPreGNS (X k i))) := by
    apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_gram ℂ _)
  have heq : (star X * X).mapₗ (f : D →ₗ[ℂ] ℂ) =
      ∑ k, CStarMatrix.ofMatrix (Matrix.gram ℂ (fun i => f.toPreGNS (X k i))) := by
    apply (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective
    ext i j
    change f (∑ k, star (X k i) * X k j) =
      ((CStarMatrix.ofMatrixₗ (R := ℂ)).symm
        (∑ k, CStarMatrix.ofMatrix (Matrix.gram ℂ (fun i => f.toPreGNS (X k i))))) i j
    rw [map_sum]
    change (∑ k, f (star (X k i) * X k j)) =
      (∑ k, Matrix.gram ℂ (fun i => f.toPreGNS (X k i))) i j
    simp only [Matrix.sum_apply, Matrix.gram_apply, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [heq]
  exact Finset.sum_nonneg fun k _ => hG k

def positiveFunctional_matrix (f : D →ₚ[ℂ] ℂ) :
    CStarMatrix ι ι D →ₚ[ℂ] CStarMatrix ι ι ℂ where
  toLinearMap := CStarMatrix.mapₗ (f : D →ₗ[ℂ] ℂ)
  monotone' := by
    intro M N hMN
    rw [← sub_nonneg] at hMN ⊢
    change 0 ≤ (CStarMatrix.mapₗ (f : D →ₗ[ℂ] ℂ)) N -
      (CStarMatrix.mapₗ (f : D →ₗ[ℂ] ℂ)) M
    rw [← map_sub]
    exact positiveFunctional_matrix_nonneg f hMN

end MatrixPos

variable {ι : Type uι} {D : Type uD} [Fintype ι] [DecidableEq ι]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma positiveFunctional_matrix_one (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    positiveFunctional_matrix (ι := ι) f 1 = 1 := by
  ext i j
  change f (if i = j then (1 : D) else 0) = if i = j then 1 else 0
  by_cases h : i = j <;> simp [h, hf]

lemma positiveFunctional_matrix_pos_contraction (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    {M : CStarMatrix ι ι D} (hM : 0 ≤ M) (hM1 : M ≤ 1) :
    0 ≤ positiveFunctional_matrix f M ∧ positiveFunctional_matrix f M ≤ 1 := by
  refine ⟨(positiveFunctional_matrix f).map_nonneg hM, ?_⟩
  have h : positiveFunctional_matrix f M ≤ positiveFunctional_matrix f 1 :=
    (positiveFunctional_matrix f).monotone hM1
  rwa [positiveFunctional_matrix_one f hf] at h

end CurrentMain

namespace Pureness

open scoped ComplexOrder ComplexStarModule

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def selfAdjointFunctionalComplex (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (ℜ a) : ℂ) + Complex.I * (f (ℑ a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointFunctionalComplex_apply (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (a : selfAdjoint A) : selfAdjointFunctionalComplex f a = (f a : ℂ) := by
  have hr : ℜ (a : A) = a := Subtype.ext a.property.coe_realPart
  simp [selfAdjointFunctionalComplex, hr, a.property.imaginaryPart]

lemma selfAdjointFunctional_nonneg (f : selfAdjoint A →L[ℝ] ℝ)
    (hn : ‖f‖ ≤ 1) (h1 : f 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ f a := by
  by_cases hz : a = 0
  · simp [hz]
  have hp : 0 < ‖(a : A)‖ := norm_pos_iff.mpr (fun h => hz (Subtype.ext h))
  let b : selfAdjoint A := ‖(a : A)‖⁻¹ • a
  have hb0 : 0 ≤ (b : A) := smul_nonneg (by positivity) ha
  have hbn : ‖(b : A)‖ ≤ 1 := by
    change ‖‖(a : A)‖⁻¹ • (a : A)‖ ≤ 1
    simp [norm_smul, inv_mul_cancel₀ hp.ne']
  have hb1 : (b : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp hbn
  have hsub : ‖(1 : selfAdjoint A) - b‖ ≤ 1 := by
    change ‖(1 : A) - (b : A)‖ ≤ 1
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hb1)).mpr
      (sub_le_self _ hb0)
  have hf : ‖f (1 - b)‖ ≤ 1 :=
    (f.le_opNorm _).trans ((mul_le_mul hn hsub (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hfb : 0 ≤ f b := by
    have := le_abs_self (f (1 - b))
    rw [map_sub, h1] at hf this
    change |1 - f b| ≤ 1 at hf
    linarith
  change 0 ≤ f (‖(a : A)‖⁻¹ • a) at hfb
  rw [map_smul, smul_eq_mul] at hfb
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hp)).mp hfb

theorem exists_normalizedPositiveState [Nontrivial A] :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 := by
  have hn1 : ‖(1 : selfAdjoint A)‖ = 1 := norm_one (α := A)
  obtain ⟨f, hfn, hf1⟩ := exists_dual_vector ℝ (1 : selfAdjoint A) (by rw [hn1]; norm_num)
  have hf1' : f 1 = 1 := by simpa [hn1] using hf1
  let g := selfAdjointFunctionalComplex f.toLinearMap
  have hg : ∀ a : A, 0 ≤ a → 0 ≤ g a := by
    intro a ha
    have h := selfAdjointFunctional_nonneg f hfn.le hf1' ⟨a, .of_nonneg ha⟩ ha
    change 0 ≤ selfAdjointFunctionalComplex f.toLinearMap (⟨a, .of_nonneg ha⟩ : selfAdjoint A)
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast h
  refine ⟨{ toLinearMap := g, monotone' := ?_ }, ?_⟩
  · intro a b hab
    change g a ≤ g b
    have := hg (b - a) (sub_nonneg.mpr hab)
    simpa only [map_sub, sub_nonneg] using this
  · change selfAdjointFunctionalComplex f.toLinearMap ((1 : selfAdjoint A) : A) = 1
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast hf1'

end Pureness

namespace CurrentMain

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def rowGram (a : I → D) : CStarMatrix I I D :=
  CStarMatrix.ofMatrix (fun i j => star (a i) * a j)

def rowMul (a : I → D) (Z : CStarMatrix I I D) : I → D :=
  fun i => ∑ j, a j * Z j i

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma rowGram_mul (a : I → D) (Z : CStarMatrix I I D) :
    rowGram (rowMul a Z) = star Z * rowGram a * Z := by
  ext i j
  change star (∑ k, a k * Z k i) * (∑ l, a l * Z l j) =
    ∑ l, (∑ k, star (Z k i) * (star (a k) * a l)) * Z l j
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [mul_assoc]

omit [PartialOrder D] [StarOrderedRing D] in
lemma rowMul_one (a : I → D) : rowMul a 1 = a := by
  ext i
  simp [rowMul, CStarMatrix.one_apply]

local instance : IsometricContinuousFunctionalCalculus ℝ (CStarMatrix I I D)
    IsSelfAdjoint := IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ (CStarMatrix I I D) :=
  CStarAlgebra.instNonnegSpectrumClass

lemma selfAdjoint_near_one_strictlyPositive {a : D} (ha : IsSelfAdjoint a)
    {δ : ℝ} (hδ : ‖a - 1‖ ≤ δ) (hδhalf : δ ≤ 1 / 2) : IsStrictlyPositive a := by
  apply CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
  refine ⟨ha, fun t ht => ?_⟩
  have h := (abs_le.mp (selfAdjoint_spectrum_near_one ha hδ ht)).1
  linarith

omit [PartialOrder D] [StarOrderedRing D] [Fintype I] [DecidableEq I] in
lemma rowGram_isSelfAdjoint (a : I → D) : IsSelfAdjoint (rowGram a) := by
  apply CStarMatrix.ext
  intro i j
  change star (star (a j) * a i) = star (a i) * a j
  simp only [star_mul, star_star]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma rowMul_norm_sub_le (a : I → D) (Z W : CStarMatrix I I D) {δ : ℝ}
    (h : ∀ i j, ‖Z i j - W i j‖ ≤ δ) (i : I) :
    ‖rowMul a Z i - rowMul a W i‖ ≤ (∑ j, ‖a j‖) * δ := by
  rw [rowMul, rowMul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖a j * Z j i - a j * W j i‖ := norm_sum_le _ _
    _ = ∑ j, ‖a j * (Z j i - W j i)‖ := by simp only [mul_sub]
    _ ≤ ∑ j, ‖a j‖ * δ := Finset.sum_le_sum fun j _ =>
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (h j i) (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

theorem normalize_almost_row {q : D} (hq : IsStarProjection q) (a : I → D)
    (ha : ∀ i, a i * q = a i) {ε : ℝ}
    (hg : ∀ i j, ‖star (a i) * a j - (if i = j then q else 0)‖ ≤ ε)
    (hε : (Fintype.card I : ℝ) ^ 2 * ε ≤ 1 / 2) :
    ∃ U : ProjectionRow I q, ∀ i,
      ‖U.entry i - a i‖ ≤ 2 * (∑ j, ‖a j‖) * (Fintype.card I : ℝ) ^ 2 * ε := by
  let F := ProjectionCorner hq
  let X : CStarMatrix I I F := CStarMatrix.ofMatrix fun i j =>
    ⟨star (a i) * a j, by
      have hleft : q * star (a i) = star (a i) := by
        simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star (ha i)
      simp only [← mul_assoc, hleft], by simp only [mul_assoc, ha]⟩
  let ι : CStarMatrix I I F →⋆ₙₐ[ℂ] CStarMatrix I I D :=
    CStarMatrix.mapₙₐ (ProjectionCorner.inclusion hq)
  have hXmap : ι X = rowGram a := rfl
  have hXsa : IsSelfAdjoint X := by
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    change star (star (a j) * a i) = star (a i) * a j
    simp only [star_mul, star_star]
  let δ : ℝ := (Fintype.card I : ℝ) ^ 2 * ε
  have hXnorm : ‖X - 1‖ ≤ δ := by
    have hb (i j : I) : ‖(X - 1) i j‖ ≤ ε := by
      have heq : ((X - 1) i j : D) = star (a i) * a j -
          (if i = j then q else 0) := by
        change star (a i) * a j - ↑((1 : CStarMatrix I I F) i j) = _
        rw [CStarMatrix.one_apply]
        split_ifs <;> rfl
      change ‖((X - 1) i j : D)‖ ≤ ε
      rw [heq]
      exact hg i j
    simpa only [δ, pow_two, mul_assoc] using matrix_norm_le_card_mul hb
  have hXp : IsStrictlyPositive X :=
    selfAdjoint_near_one_strictlyPositive hXsa hXnorm hε
  have hXZ := inv_sqrt_near_one hXp.nonneg hXnorm hε
  let Z : CStarMatrix I I F := CFC.rpow X (-(1 / 2) : ℝ)
  have hZsa : IsSelfAdjoint Z := .of_nonneg CFC.rpow_nonneg
  have hZXZ : star Z * X * Z = 1 := by
    rw [hZsa.star_eq]
    exact CFC.conjugate_rpow_neg_one_half X hXp
  let u := rowMul a (ι Z)
  have hug : rowGram u = ι 1 := by
    rw [rowGram_mul, ← hXmap, ← map_star, ← map_mul, ← map_mul, hZXZ]
  have hu (i j : I) : star (u i) * u j = if i = j then q else 0 := by
    have h := congrArg (fun T : CStarMatrix I I D => T i j) hug
    change star (u i) * u j = ((1 : CStarMatrix I I F) i j : D) at h
    rw [CStarMatrix.one_apply] at h
    split_ifs at h ⊢ <;> exact h
  refine ⟨⟨hq, u, fun i => by simpa using hu i i,
    fun i j hij => by simpa [hij] using hu i j⟩, ?_⟩
  intro i
  change ‖rowMul a (ι Z) i - a i‖ ≤ _
  have hunit : rowMul a (ι 1) = a := by
    ext i
    simp only [rowMul]
    change (∑ j, a j * ((1 : CStarMatrix I I F) j i : D)) = a i
    simp only [CStarMatrix.one_apply, mul_ite, mul_zero,
      apply_ite (fun t : F => (t : D)), ProjectionCorner.coe_one,
      ZeroMemClass.coe_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left, ha]
  have hzentry (i j : I) : ‖ι Z i j - ι 1 i j‖ ≤ 2 * δ := by
    change ‖((Z - 1) i j : D)‖ ≤ 2 * δ
    have h := CStarMatrix.norm_entry_le_norm (M := Z - 1) (i := i) (j := j)
    exact h.trans hXZ.2
  have h := rowMul_norm_sub_le a _ _ hzentry i
  rw [hunit] at h
  convert h using 1
  dsimp [δ]
  ring

end

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma state_norm_le (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1) (a : D) : ‖f a‖ ≤ ‖a‖ := by
  have hone : ‖f.toPreGNS 1‖ = 1 := by
    change Real.sqrt (f (star (1 : D) * 1)).re = 1
    simp [hf]
  have hop : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  have hgns : ‖f.toPreGNS a‖ ≤ ‖a‖ := by
    calc
      _ = ‖f.leftMulMapPreGNS a (f.toPreGNS 1)‖ := by simp
      _ ≤ ‖f.leftMulMapPreGNS a‖ * ‖f.toPreGNS 1‖ := (f.leftMulMapPreGNS a).le_opNorm _
      _ ≤ ‖a‖ := by rw [hone, mul_one]; exact hop
  have h := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS 1) (f.toPreGNS a)
  have h' : ‖f a‖ ≤ ‖f.toPreGNS a‖ := by
    simpa only [PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, hone, one_mul] using h
  exact h'.trans hgns

namespace ProjectionCorner

variable {q : D} (hq : IsStarProjection q)

def compressPositive : D →ₚ[ℂ] ProjectionCorner hq where
  toFun := compress hq
  map_add' a b := Subtype.ext (by simp [coe_compress, mul_add, add_mul])
  map_smul' r a := Subtype.ext (by simp [coe_compress])
  monotone' := by
    intro a b hab
    change q * a * q ≤ q * b * q
    simpa only [hq.isSelfAdjoint.star_eq] using star_left_conjugate_le_conjugate hab q

lemma compressPositive_one : compressPositive hq 1 = 1 := by
  apply Subtype.ext
  change q * 1 * q = q
  simp only [mul_one, hq.isIdempotentElem.eq]

lemma compressPositive_self : compressPositive hq q = 1 := by
  apply Subtype.ext
  change q * q * q = q
  simp only [hq.isIdempotentElem.eq]

end ProjectionCorner

lemma exists_state_at_projection {q : D} (hq : IsStarProjection q) (hne : q ≠ 0) :
    ∃ f : D →ₚ[ℂ] ℂ, f 1 = 1 ∧ f q = 1 := by
  have : Nontrivial (ProjectionCorner hq) := by
    apply nontrivial_of_ne (1 : ProjectionCorner hq) 0
    intro h
    exact hne (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ := Pureness.exists_normalizedPositiveState (A := ProjectionCorner hq)
  refine ⟨f.comp (ProjectionCorner.compressPositive hq), ?_, ?_⟩
  · change f (ProjectionCorner.compressPositive hq 1) = 1
    rw [ProjectionCorner.compressPositive_one, hf]
  · change f (ProjectionCorner.compressPositive hq q) = 1
    rw [ProjectionCorner.compressPositive_self, hf]

lemma state_scalar_error (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1) {q : D}
    (hq : IsStarProjection q) (hfq : f q = 1) (a : D) (c : ℂ) :
    ‖a - f a • q‖ ≤ 2 * ‖a - c • q‖ := by
  have hcoeff : ‖f a - c‖ ≤ ‖a - c • q‖ := by
    simpa only [map_sub, map_smul, hfq, smul_eq_mul, mul_one] using
      state_norm_le f hf (a - c • q)
  calc
    _ = ‖(a - c • q) - ((f a - c) • q)‖ := by congr 1; rw [sub_smul]; abel
    _ ≤ ‖a - c • q‖ + ‖(f a - c) • q‖ := norm_sub_le _ _
    _ ≤ ‖a - c • q‖ + ‖a - c • q‖ := by
      gcongr
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left hq.norm_le (norm_nonneg _)).trans
        (by simpa only [mul_one] using hcoeff)
    _ = _ := by ring

end

open scoped ComplexOrder

section RowRotate

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I] [CStarAlgebra D]

def rotateRow (a : I → D) (Z : Matrix I I ℂ) : I → D := fun i => ∑ j, Z j i • a j

def rowPair (a : I → D) (x : D) (i j : I) : D := star (a i) * x * a j

omit [DecidableEq I] in
lemma rowPair_rotate (a : I → D) (Z : Matrix I I ℂ) (x : D) (i j : I) :
    rowPair (rotateRow a Z) x i j =
      ∑ k, ∑ l, (star (Z k i) * Z l j) • rowPair a x k l := by
  simp only [rowPair, rotateRow, star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  congr 1; ring

omit [DecidableEq I] in
lemma rotateRow_right_support {q : D} (a : I → D) (ha : ∀ i, a i * q = a i)
    (Z : Matrix I I ℂ) (i : I) : rotateRow a Z i * q = rotateRow a Z i := by
  simp only [rotateRow, Finset.sum_mul, smul_mul_assoc, ha]

lemma rotateRow_norm_le (a : I → D) (Z : Matrix.unitaryGroup I ℂ) (i : I) :
    ‖rotateRow a Z i‖ ≤ ∑ j, ‖a j‖ := by
  calc
    _ ≤ ∑ j, ‖Z j i • a j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖a j‖ := Finset.sum_le_sum fun j _ => by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (entry_norm_bound_of_unitary Z.property j i)
        (norm_nonneg _)).trans_eq (one_mul _)

lemma rotateRow_covariance (a : I → D) (Z : Matrix.unitaryGroup I ℂ) :
    ∑ i, rotateRow a Z i * star (rotateRow a Z i) = ∑ i, a i * star (a i) := by
  have hZ (k l : I) : ∑ i, Z k i * star (Z l i) = if k = l then 1 else 0 := by
    have h := congrArg (fun M : Matrix I I ℂ => M k l) Z.property.2
    simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.one_apply] using h
  calc
    _ = ∑ i, ∑ k, ∑ l, (Z k i * star (Z l i)) • (a k * star (a l)) := by
      simp only [rotateRow, star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
        smul_mul_smul_comm]
      apply Finset.sum_congr rfl; intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ l, (∑ i, Z k i * star (Z l i)) • (a k * star (a l)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = _ := by
      simp only [hZ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]

lemma rowPair_rotate_error {q : D} (a : I → D) (Z : Matrix.unitaryGroup I ℂ)
    (x : D) (H : Matrix I I ℂ) {δ : ℝ}
    (h : ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ δ) (i j : I) :
    ‖rowPair (rotateRow a Z) x i j - (star (Z : Matrix I I ℂ) * H * Z) i j • q‖ ≤
      (Fintype.card I : ℝ) ^ 2 * δ := by
  have he : (star (Z : Matrix I I ℂ) * H * Z) i j • q =
      ∑ k, ∑ l, (star (Z k i) * Z l j) • (H k l • q) := by
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Finset.sum_mul, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    congr 1; ring
  rw [rowPair_rotate, he, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← smul_sub]
  calc
    _ ≤ ∑ k, ∑ l, ‖(star (Z k i) * Z l j) • (rowPair a x k l - H k l • q)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ _k : I, ∑ _l : I, δ := Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
      rw [norm_smul, norm_mul, norm_star]
      have hcoeff : ‖Z k i‖ * ‖Z l j‖ ≤ 1 :=
        (mul_le_of_le_one_left (norm_nonneg _) (entry_norm_bound_of_unitary Z.property k i)).trans
          (entry_norm_bound_of_unitary Z.property l j)
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans
        (by simpa only [one_mul] using h k l)
    _ = _ := by simp [pow_two]; ring

end RowRotate

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def scalarRowGram (f : D →ₚ[ℂ] ℂ) (a : I → D) : Matrix I I ℂ :=
  fun i j => f (star (a i) * a j)

omit [DecidableEq I] in
lemma scalarRowGram_posSemidef (f : D →ₚ[ℂ] ℂ) (a : I → D) :
    (scalarRowGram f a).PosSemidef := by
  have he : scalarRowGram f a = Matrix.gram ℂ (fun i => f.toPreGNS (a i)) := by
    ext i j
    simp only [scalarRowGram, Matrix.gram_apply, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [he]
  exact Matrix.posSemidef_gram ℂ _

omit [DecidableEq I] in
lemma scalarRowGram_trace_le (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1) (a : I → D) :
    ((scalarRowGram f a).trace).re ≤ ∑ i, ‖a i‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, scalarRowGram, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ‖f (star (a i) * a i)‖ := Complex.re_le_norm _
    _ ≤ ‖star (a i) * a i‖ := state_norm_le f hf _
    _ = _ := by rw [CStarRing.norm_star_mul_self]; ring

lemma scalarRowGram_eigenvalue_le_one (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    (a : I → D) (ha : ∑ i, ‖a i‖ ^ 2 ≤ 1) (i : I) :
    (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i ≤ 1 := by
  let hG := scalarRowGram_posSemidef f a
  have he : ∑ j, hG.isHermitian.eigenvalues j = ((scalarRowGram f a).trace).re := by
    rw [hG.isHermitian.trace_eq_sum_eigenvalues]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  calc
    _ ≤ ∑ j, hG.isHermitian.eigenvalues j := Finset.single_le_sum
      (fun j _ => hG.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = _ := he
    _ ≤ _ := scalarRowGram_trace_le f hf a
    _ ≤ _ := ha

end CurrentMain

end

end OAI
