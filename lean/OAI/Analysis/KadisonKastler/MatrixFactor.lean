import OAI.Analysis.KadisonKastler.MatrixVonNeumann
import OAI.Analysis.KadisonKastler.MatrixCorners
import OAI.Analysis.FactorGeneration.ProjectionComparison
import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

/-! # Factor and finite properties of the represented matrix algebra -/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {B : Type*} [CStarAlgebra B]

theorem projection_map_equiv {A B : Type*} [Add A] [Add B] [Mul A] [Mul B]
    [Star A] [Star B] [SMul ℂ A] [SMul ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} (hx : IsStarProjection x) : IsStarProjection (e x) :=
  hx.map e

theorem equiv_smul_one {A B : Type*} [Add A] [Add B]
    [MulOneClass A] [MulOneClass B] [Star A] [Star B] [SMul ℂ A] [SMul ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) (z : ℂ) : e (z • (1 : A)) = z • (1 : B) := by
  rw [map_smul, map_one]

theorem isometry_coisometry_of_faithfulTrace (τ : FaithfulTracialState B)
    (v : B) (hv : star v * v = 1) : v * star v = 1 := by
  have hproj : (v * star v) * (v * star v) = v * star v := by
    calc
      _ = v * (star v * v) * star v := by noncomm_ring
      _ = _ := by rw [hv, mul_one]
  let q := 1 - v * star v
  have hqstar : star q = q := by simp [q, star_mul]
  have hqmul : q * q = q := by
    calc
      _ = 1 - v * star v - v * star v + (v * star v) * (v * star v) := by
        dsimp [q]
        noncomm_ring
      _ = q := by rw [hproj]; dsimp [q]; abel
  have hτq : τ.toLinearMap q = 0 := by
    dsimp [q]
    rw [map_sub, τ.map_one, τ.tracial v (star v), hv, τ.map_one, sub_self]
  have hq : q = 0 := τ.faithful q (by rw [hqstar, hqmul, hτq])
  exact (sub_eq_zero.mp hq).symm

/-- Pulling a proper split of the final projection back through its
partial isometry gives a proper split of the original larger projection. -/
theorem proper_projection_pullback (p v f r : B) (hp : IsStarProjection p)
    (hr : IsStarProjection r) (hvp : v * p = v) (hv : v * star v = f)
    (hfr : f * r = r) (hrf : r * f = r) (hr0 : r ≠ 0) (hrf' : r ≠ f) :
    ∃ q : B, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  let q := star v * r * v
  have hpv : p * star v = star v := by
    simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq] using congrArg star hvp
  have hq : IsStarProjection q := by
    constructor
    · change (star v * r * v) * (star v * r * v) = star v * r * v
      calc
        _ = star v * (r * (v * star v) * r) * v := by noncomm_ring
        _ = _ := by rw [hv, hrf, hr.isIdempotentElem.eq]
    · change star (star v * r * v) = star v * r * v
      simp only [star_mul, star_star, hr.isSelfAdjoint.star_eq, mul_assoc]
  have hrec : v * q * star v = r := by
    calc
      _ = (v * star v) * r * (v * star v) := by dsimp [q]; noncomm_ring
      _ = r := by rw [hv, hfr, hrf]
  refine ⟨q, hq, ?_, ?_, ?_, ?_⟩
  · intro hz
    rw [hz, mul_zero, zero_mul] at hrec
    exact hr0 hrec.symm
  · intro hqp
    apply hrf'
    rw [← hrec, hqp, hvp, hv]
  · change p * (star v * r * v) = star v * r * v
    rw [← mul_assoc, ← mul_assoc, hpv]
  · change (star v * r * v) * p = star v * r * v
    rw [mul_assoc, hvp]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_scalar_center
    (hfactor : ∀ b : B, (∀ a : B, a * b = b * a) → ∃ z : ℂ, b = z • (1 : B))
    (x : CStarMatrix ι ι B) (hx : ∀ y : CStarMatrix ι ι B, y * x = x * y) :
    ∃ z : ℂ, x = z • (1 : CStarMatrix ι ι B) := by
  let m : Matrix ι ι B := CStarMatrix.ofMatrix.symm x
  have hm : m ∈ Set.center (Matrix ι ι B) := by
    rw [Semigroup.mem_center_iff]
    intro a
    exact hx (CStarMatrix.ofMatrix a)
  rw [Matrix.center_eq_scalar_image] at hm
  obtain ⟨b, hb, hbm⟩ := hm
  obtain ⟨z, hz⟩ := hfactor b (Semigroup.mem_center_iff.mp hb)
  refine ⟨z, ?_⟩
  ext i j
  have he := congrArg (fun a : Matrix ι ι B => a i j) hbm
  change (if i = j then b else 0) = x i j at he
  rw [← he, hz]
  simp [CStarMatrix.smul_apply, CStarMatrix.one_apply, smul_ite]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem matrixVonNeumann_scalar_center (M : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (x : Algebra (matrixVonNeumann (ι := ι) M))
    (hx : ∀ y : Algebra (matrixVonNeumann (ι := ι) M), y * x = x * y) :
    ∃ z : ℂ, x = algebraMap ℂ (Algebra (matrixVonNeumann (ι := ι) M)) z := by
  let e := matrixAlgebraEquiv (ι := ι) M
  have hbase : ∀ b : Algebra M, (∀ a : Algebra M, a * b = b * a) →
      ∃ z : ℂ, b = z • (1 : Algebra M) := by
    intro b hb
    obtain ⟨z, hz⟩ := hM.factor b hb
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hm : ∀ y : CStarMatrix ι ι (Algebra M), y * e.symm x = e.symm x * y := by
    intro y
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm (hx (e y))
  obtain ⟨z, hz⟩ := matrix_scalar_center hbase (e.symm x) hm
  refine ⟨z, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  calc
    x = e (e.symm x) := (e.apply_symm_apply x).symm
    _ = e (z • 1) := congrArg e hz
    _ = z • 1 := equiv_smul_one (A := CStarMatrix ι ι (Algebra M))
      (B := Algebra (matrixVonNeumann (ι := ι) M)) e z

variable [Nonempty ι]

omit [Fintype ι] in
theorem matrixVonNeumann_nonzero (M : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    (0 : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H) ≠ 1 := by
  classical
  let i : ι := Classical.arbitrary ι
  intro h
  apply hM.nonzero
  ext ξ
  have hi := congrArg (fun T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H =>
    T (Generator.tupleSingle i ξ) i) h
  simpa [Generator.tupleSingle_apply, Pi.single_apply] using hi

omit [DecidableEq ι] [Nonempty ι] in
theorem matrixVonNeumann_weaklyClosed (M : VonNeumannAlgebra H) :
    Generator.WOTClosed (matrixVonNeumann (ι := ι) M).toStarSubalgebra :=
  Generator.Tracial.vonNeumann_wotClosed _

theorem matrixVonNeumann_finite (M : VonNeumannAlgebra H)
    (τ : FaithfulTracialState (Algebra M))
    (v : Algebra (matrixVonNeumann (ι := ι) M)) (hv : star v * v = 1) :
    v * star v = 1 :=
  isometry_coisometry_of_faithfulTrace (matrixVonNeumannTrace M τ) v hv

omit [Nonempty ι] in
/-- A nonzero projection has a nonzero partial-isometry link to a
coordinate corner. -/
theorem exists_matrix_corner_link (M : VonNeumannAlgebra H)
    (p : Algebra (matrixVonNeumann (ι := ι) M))
    (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ (i : ι) (v : Generator.Tracial.PartialIsometry (matrixVonNeumann (ι := ι) M)),
      v.val * p = v.val ∧
      matrixDiagonalProjection M i * v.target.val = v.target.val ∧ v.target.val ≠ 0 := by
  classical
  let Q := matrixDiagonalProjection (ι := ι) M
  have hQ : ∀ i, IsStarProjection (Q i) := matrixDiagonalProjection_isStarProjection M
  have hsum : ∑ i, Q i = 1 := by
    change ∑ i, (matrixAlgebraEquiv (ι := ι) M)
      ((coordinateMatrixUnits (B := Algebra M)).entry i i) = 1
    rw [← map_sum, (coordinateMatrixUnits (B := Algebra M)).total, map_one]
  have hex : ∃ i, Q i * p ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∑ i, Q i) * p = 0 := by simp only [Finset.sum_mul, h, Finset.sum_const_zero]
    rw [hsum, one_mul] at hz
    exact hp0 hz
  obtain ⟨i, hi⟩ := hex
  obtain ⟨v, hvp, hvQ, hv0⟩ := Generator.Tracial.exists_partialIsometry_of_link
    (⟨p, hp⟩ : Generator.Tracial.AlgebraProjection (matrixVonNeumann (ι := ι) M))
    ⟨Q i, hQ i⟩ (Q i * p)
    (by rw [mul_assoc, hp.isIdempotentElem.eq])
    (by rw [← mul_assoc, (hQ i).isIdempotentElem.eq]) hi
  refine ⟨i, v, (v.support_le_iff_mul ⟨p, hp⟩).mp hvp, hvQ, ?_⟩
  intro hz
  have hvz : v.val = 0 := (CStarRing.mul_star_self_eq_zero_iff _).mp hz
  exact hv0 (v.initial.symm.trans (by rw [hvz, star_zero, mul_zero]))

omit [Nonempty ι] in
/-- Splits in a diagonal matrix corner transport to the represented
algebra. -/
theorem matrix_corner_split (M : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (i : ι)
    (f : Algebra (matrixVonNeumann (ι := ι) M)) (hf : IsStarProjection f) (hf0 : f ≠ 0)
    (hleft : matrixDiagonalProjection M i * f = f) :
    ∃ r : Algebra (matrixVonNeumann (ι := ι) M), IsStarProjection r ∧ r ≠ 0 ∧
      r ≠ f ∧ f * r = r ∧ r * f = r := by
  let e := matrixAlgebraEquiv (ι := ι) M
  have hright : f * matrixDiagonalProjection M i = f := by
    simpa only [star_mul, (matrixDiagonalProjection_isStarProjection M i).isSelfAdjoint.star_eq,
      hf.isSelfAdjoint.star_eq] using congrArg star hleft
  let f' := e.symm f
  have hfp : IsStarProjection f' := by
    change IsStarProjection (e.symm f)
    exact projection_map_equiv (A := Algebra (matrixVonNeumann (ι := ι) M))
      (B := CStarMatrix ι ι (Algebra M)) e.symm hf
  have hf0' : f' ≠ 0 := fun h => hf0 (e.symm.injective (h.trans (map_zero e.symm).symm))
  have hfl : matrixCorner i 1 * f' = f' := by
    change e (matrixCorner i 1) * f = f at hleft
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hleft
  have hfr : f' * matrixCorner i 1 = f' := by
    change f * e (matrixCorner i 1) = f at hright
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hright
  obtain ⟨r, hr, hr0, hrf, hfr', hrf'⟩ :=
    matrixCorner_diffuse hM.diffuse i f' hfp hf0' hfl hfr
  refine ⟨e r, projection_map_equiv e hr, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hr0 (e.injective (h.trans (map_zero e).symm))
  · intro h
    exact hrf (e.injective (h.trans (e.apply_symm_apply _).symm))
  · have hh := congrArg e hfr'
    simpa only [map_mul, f', e.apply_symm_apply] using hh
  · have hh := congrArg e hrf'
    simpa only [map_mul, f', e.apply_symm_apply] using hh

omit [Nonempty ι] in
/-- Finite matrices over a diffuse represented algebra have no minimal
nonzero projections. -/
theorem matrixVonNeumann_diffuse (M : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (p : Algebra (matrixVonNeumann (ι := ι) M))
    (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : Algebra (matrixVonNeumann (ι := ι) M), IsStarProjection q ∧ q ≠ 0 ∧
      q ≠ p ∧ p * q = q ∧ q * p = q := by
  obtain ⟨i, v, hvp, hvQ, hv0⟩ := exists_matrix_corner_link M p hp hp0
  obtain ⟨r, hr, hr0, hrf, hfr, hrf'⟩ :=
    matrix_corner_split M hM i v.target.val v.target.property hv0 hvQ
  exact proper_projection_pullback p v.val v.target.val r hp hr hvp rfl hfr hrf' hr0 hrf

/-- The represented finite matrix amplification is again a II₁ factor. -/
theorem matrixVonNeumann_isII1Factor (M : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τ : FaithfulTracialState (Algebra M)) :
    Generator.IsII1Factor (matrixVonNeumann (ι := ι) M).toStarSubalgebra where
  nonzero := matrixVonNeumann_nonzero M hM
  weaklyClosed := matrixVonNeumann_weaklyClosed M
  factor := matrixVonNeumann_scalar_center M hM
  finite := matrixVonNeumann_finite M τ
  diffuse := matrixVonNeumann_diffuse M hM

end

end KadisonKastler

end OAI
