import OAI.Algebra.Determinantal.RowIdeals

namespace OAI

namespace PermanentBorder.Conductor
open Matrix Polynomial
section
variable {K S ι : Type*} [Field K] [CommRing S] [Algebra K S]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem charpoly_mem_adjugate_ideal (T : Matrix ι ι S) :
    T.charpoly ∈ matrixEntryIdeal T.charmatrix.adjugate := by
  classical
  rw [Matrix.charpoly, det_eq_sum_mul_adjugate_row _ (Classical.arbitrary ι)]
  exact Ideal.sum_mem _ fun j _ =>
    Ideal.mul_mem_left _ _ (entry_mem_matrixEntryIdeal _ j _)

noncomputable def polynomialCofactorQuotientEquiv (T : Matrix ι ι S) :
    (AdjoinRoot T.charpoly ⧸
      (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).restrictScalars S)
      ≃ₗ[K] S[X] ⧸ matrixEntryIdeal T.charmatrix.adjugate := by
  let J := matrixEntryIdeal T.charmatrix.adjugate
  have h : Ideal.span {T.charpoly} ≤ J :=
    Ideal.span_le.mpr fun _ hx => Set.mem_singleton_iff.mp hx ▸ charpoly_mem_adjugate_ideal T
  let e := (DoubleQuot.quotQuotEquivQuotOfLEₐ K h).toLinearEquiv
  have hm : J.map (Ideal.Quotient.mkₐ K (Ideal.span {T.charpoly})) =
      matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) :=
    matrixEntryIdeal_map (AdjoinRoot.mk T.charpoly) T.charmatrix.adjugate
  rw [hm] at e
  letI : IsScalarTower K (AdjoinRoot T.charpoly) (AdjoinRoot T.charpoly) :=
    AdjoinRoot.isScalarTower_right T.charpoly
  let e₀ := Submodule.Quotient.restrictScalarsEquiv K
    (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)))
  exact e₀.trans e

end
end PermanentBorder.Conductor

namespace PermanentBorder.PencilSeparability
open Polynomial Matrix
section Specialization
variable {R K L : Type*} [CommRing R] [Field K] [Field L]

theorem monic_generic_separable (f : R[X]) (hf : f.Monic)
    (σ : R →+* K) (φ : R →+* L) (hφ : Function.Injective φ)
    (hs : (f.map σ).Separable) : (f.map φ).Separable := by
  let g := f.derivative
  have hσd : (f.map σ).natDegree = f.natDegree := hf.natDegree_map σ
  have hφd : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  have hd : (g.map σ).natDegree ≤ g.natDegree := natDegree_map_le
  have hσ : σ (resultant f g) ≠ 0 := by
    rw [← resultant_map_map f g f.natDegree g.natDegree, ← hσd]
    conv_lhs => rw [show g.natDegree = (g.map σ).natDegree +
      (g.natDegree - (g.map σ).natDegree) by omega]
    rw [resultant_add_right_deg _ _ _ _ _ le_rfl]
    have hc : (f.map σ).coeff (f.map σ).natDegree = 1 := (hf.map σ).coeff_natDegree
    rw [hc, one_pow, one_mul]
    exact resultant_ne_zero _ _ (by simpa only [Separable, g, derivative_map] using hs)
  have hres : resultant f g ≠ 0 := fun h => hσ (h ▸ σ.map_zero)
  have hφg : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hφ g
  apply (isUnit_resultant_iff_isCoprime (hf.map φ)).mp
  apply isUnit_iff_ne_zero.mpr
  rw [derivative_map, hφd, hφg, resultant_map_map]
  exact fun h => hres (hφ (h.trans φ.map_zero.symm))

end Specialization
section Scaling
variable {K : Type*} [Field K]

theorem separable_comp_linear (f : K[X]) (hf : f.Separable) (a : K) (ha : a ≠ 0) :
    (f.comp (C a * X)).Separable := by
  obtain ⟨u,v,h⟩ := hf
  let p : K[X] := C a * X
  refine ⟨u.comp p, C a⁻¹ * v.comp p, ?_⟩
  have hc := congrArg (fun z : K[X] => z.comp p) h
  simp only [add_comp, mul_comp, one_comp] at hc
  have hd : derivative p = C a := by
    simp only [p, derivative_mul, derivative_C, zero_mul, derivative_X, mul_one, zero_add]
  change u.comp p * f.comp p + (C a⁻¹ * v.comp p) * derivative (f.comp p) = 1
  rw [derivative_comp, hd]
  have haC : C a⁻¹ * C a = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ ha, C_1]
  calc
    _ = u.comp p * f.comp p + (C a⁻¹ * C a) *
        (v.comp p * f.derivative.comp p) := by ring
    _ = 1 := by rw [haC, one_mul]; exact hc

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem charpoly_smul_eq_comp (A : Matrix ι ι K) (a : K) (ha : a ≠ 0) :
    (a • A).charpoly = C (a ^ Fintype.card ι) * A.charpoly.comp (C a⁻¹ * X) := by
  let φ : K[X] →+* K[X] := eval₂RingHom C (C a⁻¹ * X)
  have hm : (a • A).charmatrix = C a • A.charmatrix.map φ := by
    apply Matrix.ext
    intro i j
    by_cases h : i = j
    · subst j
      simp only [charmatrix_apply, diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul,
        Matrix.map_apply, φ, coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_C, map_mul]
      have hx : C a * C a⁻¹ = (1 : K[X]) := by
        rw [← C_mul, mul_inv_cancel₀ ha, C_1]
      rw [mul_sub, ← mul_assoc, hx, one_mul]
    · simp only [charmatrix_apply, diagonal_apply_ne _ h, Matrix.smul_apply, smul_eq_mul,
        Matrix.map_apply, zero_sub, φ, coe_eval₂RingHom, eval₂_neg,
        eval₂_C, map_mul, mul_neg]
  rw [Matrix.charpoly, hm, Matrix.det_smul]
  have hd : (A.charmatrix.map φ).det = φ A.charpoly := (φ.map_det _).symm
  rw [hd]
  simp only [map_pow, φ, coe_eval₂RingHom, Polynomial.comp]

theorem separable_charpoly_smul (A : Matrix ι ι K) (hA : A.charpoly.Separable)
    (a : K) (ha : a ≠ 0) : (a • A).charpoly.Separable := by
  rw [charpoly_smul_eq_comp A a ha]
  exact (separable_comp_linear A.charpoly hA a⁻¹ (inv_ne_zero ha)).unit_mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha)))
end Scaling

section Pencil
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem distinct_slope_pencil_separable (θ : ι → K) (hθ : Function.Injective θ)
    (A : Matrix ι ι K) :
    ((-((X : K[X]) • (Matrix.diagonal θ).map C + A.map C)).charpoly.map
      (algebraMap K[X] (FractionRing K[X]))).Separable := by
  let Q := FractionRing K[X]
  let t : Q := algebraMap K[X] Q X
  have ht : Transcendental K t :=
    (transcendental_algebraMap_iff (IsFractionRing.injective K[X] Q)).mpr
      (transcendental_X K)
  have hti : Transcendental K t⁻¹ := by
    simpa only [Transcendental, IsAlgebraic.inv_iff] using ht
  let φ : K[X] →+* Q := (aeval t⁻¹).toRingHom
  have hφ : Function.Injective φ := transcendental_iff_injective.mp hti
  let B : Matrix ι ι K[X] := -((Matrix.diagonal θ).map C + (X : K[X]) • A.map C)
  have hB : (B.charpoly.map (evalRingHom (0 : K))).Separable := by
    rw [← charpoly_map]
    have he : B.map (evalRingHom (0 : K)) = Matrix.diagonal (fun i => -θ i) := by
      apply Matrix.ext
      intro i j
      by_cases h : i = j <;> simp [B, h]
    rw [he, charpoly_diagonal, separable_prod_X_sub_C_iff]
    exact fun i j hij => hθ (neg_injective hij)
  have hs := monic_generic_separable B.charpoly B.charpoly_monic
    (evalRingHom (0 : K)) φ hφ hB
  rw [← charpoly_map] at hs
  have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  have hm : (-((X : K[X]) • (Matrix.diagonal θ).map C + A.map C)).map
      (algebraMap K[X] Q) = t • B.map φ := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, map_neg, map_add, map_mul, B]
    have hc (x : K) : algebraMap K[X] Q (C x) = algebraMap K Q x :=
      (IsScalarTower.algebraMap_apply K K[X] Q x).symm
    simp only [φ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, aeval_X, hc]
    change -(t * algebraMap K Q ((Matrix.diagonal θ) i j) + algebraMap K Q (A i j)) =
      t * -(algebraMap K Q ((Matrix.diagonal θ) i j) + t⁻¹ * algebraMap K Q (A i j))
    rw [mul_neg, mul_add, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
  rw [← charpoly_map, hm]
  exact separable_charpoly_smul (B.map φ) hs t ht0
end Pencil
end PermanentBorder.PencilSeparability

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Conductor
section
variable {K : Type*} [Field K] [Infinite K] {k : ℕ}

theorem charmatrix_neg_eq_pencil {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι R) : (-B).charmatrix = pencilMatrix B := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;>
    simp [pencilMatrix, h]

theorem cofactorIdeal_eq_matrixEntryIdeal {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (B : Matrix ι ι R) :
    cofactorIdeal B = matrixEntryIdeal (-B).charmatrix.adjugate := by
  rw [charmatrix_neg_eq_pencil]
  rfl

theorem critical_normalization_defect
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (q : ℕ) (hq : 3*q ≤ k)
    (hcrit : ∀ i j, (((pencilMatrix (pencilBase θ A)).adjugate i j).coeff q).coeff q = 0) :
    let T := -(pencilBase θ A)
    let Q := FractionRing K[X]
    let R := integralClosure K[X] (AdjoinRoot (T.charpoly.map (algebraMap K[X] Q)))
    ((q+2).choose 2 : ℕ∞) ≤ Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toLinearMap) := by
  let T := -(pencilBase θ A)
  have hs : (T.charpoly.map (algebraMap K[X] (FractionRing K[X]))).Separable :=
    PencilSeparability.distinct_slope_pencil_separable θ hθ A
  have h := critical_cofactor_length θ hθ A q hq hcrit
  rw [cofactorIdeal_eq_matrixEntryIdeal] at h
  have he := (polynomialCofactorQuotientEquiv (K := K) T).length_eq
  rw [← he] at h
  exact h.trans (normalization_adjugate_length_global (K := K) T hs)

end
end PermanentBorder.AdjugateAlgebra

end OAI
