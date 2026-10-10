import OAI.InformationTheory.SecretKey.Model

namespace OAI

noncomputable section

open scoped MatrixOrder ComplexOrder Kronecker

open Matrix

namespace ZeroKey

section MatrixPolar

universe v43_0

variable {ι : Type v43_0} [inst43_0 : Fintype ι] [inst43_1 : DecidableEq ι]

theorem exists_unitary_polar (A : Matrix ι ι ℂ) :
    ∃ U : Matrix.unitaryGroup ι ℂ, A = (U : Matrix ι ι ℂ) * CFC.sqrt (Aᴴ * A) := by
  apply exists_unitary_mul_of_gram_eq
  rw [(CFC.sqrt_nonneg (Aᴴ * A)).posSemidef.isHermitian.eq]
  exact (CFC.sqrt_mul_sqrt_self (Aᴴ * A)
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg).symm

end MatrixPolar

section TraceNorm

universe v84_0

variable {ι : Type v84_0} [inst84_0 : Fintype ι] [inst84_1 : DecidableEq ι]

omit inst84_1 in
lemma re_trace_nonneg [DecidableEq ι] {S : Matrix ι ι ℂ} (hS : S.PosSemidef) :
    0 ≤ (trace S).re := (RCLike.nonneg_iff.mp hS.trace_nonneg).1

lemma re_trace_mul_nonneg {S T : Matrix ι ι ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) : 0 ≤ (trace (S * T)).re := by
  let B := CFC.sqrt S
  have hB : Bᴴ = B := (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have h := re_trace_nonneg (hT.mul_mul_conjTranspose_same B)
  rwa [hB, Matrix.trace_mul_cycle, hBB] at h

omit inst84_1 in
lemma re_trace_star_mul [DecidableEq ι] {S W : Matrix ι ι ℂ} (hS : S.IsHermitian) :
    (trace (Wᴴ * S)).re = (trace (W * S)).re := by
  have h : Wᴴ * S = (S * W)ᴴ := by simp [hS.eq]
  rw [h, Matrix.trace_conjTranspose, Matrix.trace_mul_comm S W]
  rfl

lemma re_trace_unitary_mul_le {S : Matrix ι ι ℂ} (hS : S.PosSemidef)
    (W : Matrix.unitaryGroup ι ℂ) : (trace ((W : Matrix ι ι ℂ) * S)).re ≤ (trace S).re := by
  let V : Matrix ι ι ℂ := W
  have hV : Vᴴ * V = 1 := W.prop.1
  have hp := re_trace_mul_nonneg (Matrix.posSemidef_conjTranspose_mul_self (V - 1)) hS
  have hexp : (V - 1)ᴴ * (V - 1) * S = S + S - V * S - Vᴴ * S := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub,
      hV, one_mul, mul_one]
    noncomm_ring
  rw [hexp, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add,
    Complex.sub_re, Complex.sub_re, Complex.add_re, re_trace_star_mul hS.isHermitian] at hp
  change (trace (V * S)).re ≤ (trace S).re
  linarith

lemma traceNorm_nonneg (A : Matrix ι ι ℂ) : 0 ≤ traceNorm A :=
  re_trace_nonneg (CFC.sqrt_nonneg (Aᴴ * A)).posSemidef

lemma re_trace_unitary_mul_le_traceNorm (A : Matrix ι ι ℂ)
    (W : Matrix.unitaryGroup ι ℂ) :
    (trace ((W : Matrix ι ι ℂ) * A)).re ≤ traceNorm A := by
  obtain ⟨U, hU⟩ := exists_unitary_polar A
  have h := re_trace_unitary_mul_le (CFC.sqrt_nonneg (Aᴴ * A)).posSemidef (W * U)
  change (trace (((W : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)) * CFC.sqrt (Aᴴ * A))).re ≤ _ at h
  rw [Matrix.mul_assoc, ← hU] at h
  exact h

lemma exists_unitary_traceNorm (A : Matrix ι ι ℂ) :
    ∃ U : Matrix.unitaryGroup ι ℂ, (trace ((U : Matrix ι ι ℂ) * A)).re = traceNorm A := by
  obtain ⟨U, hU⟩ := exists_unitary_polar A
  refine ⟨star U, ?_⟩
  change (trace ((U : Matrix ι ι ℂ)ᴴ * A)).re = _
  nth_rw 1 [hU]
  rw [← Matrix.mul_assoc, show (U : Matrix ι ι ℂ)ᴴ * U = 1 from U.prop.1, one_mul]
  rfl

lemma traceNorm_add_le (A B : Matrix ι ι ℂ) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  obtain ⟨U, hU⟩ := exists_unitary_traceNorm (A + B)
  rw [← hU, mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (re_trace_unitary_mul_le_traceNorm A U)
    (re_trace_unitary_mul_le_traceNorm B U)

lemma trace_re_unitary_conjugate (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    trace ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) = trace A := by
  rw [Matrix.trace_mul_cycle, show (U : Matrix ι ι ℂ)ᴴ * U = 1 from U.prop.1, one_mul]

end TraceNorm

section Frobenius

universe v155_0 v155_1

variable {ι : Type v155_0} {κ : Type v155_1} [inst155_0 : Fintype ι] [inst155_1 : Fintype κ] [inst155_2 : DecidableEq ι]

omit inst155_2 in
lemma trace_mul_conjTranspose_eq_inner [DecidableEq ι] (A B : Matrix ι κ ℂ) :
    trace (A * Bᴴ) = inner ℂ (matrixVector B) (matrixVector A) := by
  simp [matrixVector, EuclideanSpace.inner_toLp_toLp, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Fintype.sum_prod_type]

lemma norm_matrixVector (A : Matrix ι κ ℂ) :
    ‖matrixVector A‖ = Real.sqrt (trace (A * Aᴴ)).re := by
  rw [trace_mul_conjTranspose_eq_inner]
  exact norm_eq_sqrt_re_inner (𝕜 := ℂ) (matrixVector A)

lemma re_trace_mul_conjTranspose_le (A B : Matrix ι κ ℂ) :
    (trace (A * Bᴴ)).re ≤ Real.sqrt ((trace (A * Aᴴ)).re * (trace (B * Bᴴ)).re) := by
  rw [trace_mul_conjTranspose_eq_inner A B, Real.sqrt_mul
    (re_trace_nonneg (Matrix.posSemidef_self_mul_conjTranspose A))]
  change RCLike.re (inner ℂ (matrixVector B) (matrixVector A)) ≤ _
  calc
    _ ≤ ‖matrixVector B‖ * ‖matrixVector A‖ := re_inner_le_norm _ _
    _ = _ := by rw [norm_matrixVector, norm_matrixVector, mul_comm]

lemma traceNorm_mul_conjTranspose_le (A B : Matrix ι κ ℂ) :
    traceNorm (A * Bᴴ) ≤ Real.sqrt ((trace (A * Aᴴ)).re * (trace (B * Bᴴ)).re) := by
  obtain ⟨U, hU⟩ := exists_unitary_traceNorm (A * Bᴴ)
  rw [← hU, ← Matrix.mul_assoc]
  have h := re_trace_mul_conjTranspose_le ((U : Matrix ι ι ℂ) * A) B
  have heq : trace (((U : Matrix ι ι ℂ) * A) * ((U : Matrix ι ι ℂ) * A)ᴴ) =
      trace (A * Aᴴ) := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (U : Matrix ι ι ℂ) A,
      trace_re_unitary_conjugate]
  rwa [heq] at h

end Frobenius

section PositiveBlock

universe v193_0 v193_1

variable {ι : Type v193_0} {κ : Type v193_1} [inst193_0 : Fintype ι] [inst193_1 : Fintype κ] [inst193_2 : DecidableEq ι] [inst193_3 : DecidableEq κ]

omit inst193_0 inst193_2 in
lemma sqrtRows_gram [Fintype ι] [DecidableEq ι] {R : Matrix κ κ ℂ} (hR : R.PosSemidef) (f g : ι → κ) :
    (CFC.sqrt R).submatrix f id * ((CFC.sqrt R).submatrix g id)ᴴ = R.submatrix f g := by
  rw [Matrix.conjTranspose_submatrix, (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq,
    ← Matrix.submatrix_mul _ _ f id g Function.bijective_id,
    CFC.sqrt_mul_sqrt_self R hR.nonneg]

lemma traceNorm_submatrix_le {R : Matrix κ κ ℂ} (hR : R.PosSemidef) (f g : ι → κ) :
    traceNorm (R.submatrix f g) ≤
      Real.sqrt ((trace (R.submatrix f f)).re * (trace (R.submatrix g g)).re) := by
  have h := traceNorm_mul_conjTranspose_le ((CFC.sqrt R).submatrix f id)
    ((CFC.sqrt R).submatrix g id)
  simpa only [sqrtRows_gram hR] using h

theorem positive_block_estimate (H Z J : Matrix ι ι ℂ)
    (h : (Matrix.fromBlocks H Z Zᴴ J).PosSemidef) :
    traceNorm Z ≤ Real.sqrt ((trace H).re * (trace J).re) := by
  exact traceNorm_submatrix_le h Sum.inl Sum.inr

end PositiveBlock

section

def InClass {a b : ℕ} (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Prop :=
  Density R ∧ ∃ (c d : ℕ) (L : Mat c →ₗ[ℂ] Mat a) (M : Mat d →ₗ[ℂ] Mat b)
    (χ : Fin c × Fin d → ℂ), PPTType L ∧ PPTType M ∧ R = tensorMap L M (outer χ χ)

def weight {a b : ℕ} (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (X : Mat a) (Y : Mat b) : ℝ := (Matrix.trace ((X ⊗ₖ Y) * R)).re

lemma cp_positive {a b : ℕ} {L : Mat a →ₗ[ℂ] Mat b} (hL : CompletelyPositive L)
    {U : Mat a} (hU : U.PosSemidef) : (L U).PosSemidef := by
  have h := hL 1 (U.submatrix Prod.snd Prod.snd) (hU.submatrix Prod.snd)
  exact h.submatrix (fun i => (0,i))

section TensorBlocks

universe v344_0

def amplifyTensor {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d)
    {κ : Type v344_0} (U : Matrix (κ × (Fin a × Fin c)) (κ × (Fin a × Fin c)) ℂ) :
    Matrix (κ × (Fin b × Fin d)) (κ × (Fin b × Fin d)) ℂ :=
  fun i j => tensorMap L M (fun x y => U (i.1,x) (j.1,y)) i.2 j.2

universe v349_0

lemma tensorMap_amplify_positive {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b}
    {M : Mat c →ₗ[ℂ] Mat d} (hL : CompletelyPositive L) (hM : CompletelyPositive M)
    {κ : Type v349_0} [Fintype κ]
    {U : Matrix (κ × (Fin a × Fin c)) (κ × (Fin a × Fin c)) ℂ} (hU : U.PosSemidef) :
    (amplifyTensor L M U).PosSemidef := by
  have h₁ := cp_amplifyIndex hM _
    (hU.submatrix (fun i : (κ × Fin a) × Fin c => (i.1.1, (i.1.2, i.2))))
  have h₂ := cp_amplifyIndex hL _
    (h₁.submatrix (fun i : (κ × Fin d) × Fin a => ((i.1.1, i.2), i.1.2)))
  have h₃ := h₂.submatrix (fun i : κ × (Fin b × Fin d) => ((i.1, i.2.2), i.2.1))
  convert h₃ using 1
  ext i j
  exact tensorMap_apply L M _ _ _ _ _

lemma tensorMap_global_transpose {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b)
    (M : Mat c →ₗ[ℂ] Mat d) (U : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap (L.comp (transposeLinear a)) (M.comp (transposeLinear c)) U =
    tensorMap L M Uᵀ := by
  ext i j
  calc
    _ = (L.comp (transposeLinear a))
        (fun x y => (M.comp (transposeLinear c)) (fun z w => U (x,z) (y,w)) i.2 j.2)
        i.1 j.1 := tensorMap_apply _ _ _ _ _ _ _
    _ = L (fun x y => M (fun z w => Uᵀ (x,z) (y,w)) i.2 j.2) i.1 j.1 := rfl
    _ = _ := (tensorMap_apply _ _ _ _ _ _ _).symm

universe v378_0

lemma outer_transpose_conj {ι : Type v378_0} (u s : ι → ℂ) :
    (outer (star s) (star u))ᵀ = outer u s := by
  ext i j
  simp [outer, Matrix.transpose_apply, mul_comm]

lemma tensorMap_outer_block {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b}
    {M : Mat c →ₗ[ℂ] Mat d} (hL : CompletelyPositive L) (hM : CompletelyPositive M)
    (u s : Fin a × Fin c → ℂ) :
    (fromBlocks (tensorMap L M (outer u u)) (tensorMap L M (outer u s))
      (tensorMap L M (outer s u)) (tensorMap L M (outer s s))).PosSemidef := by
  let v : Bool × (Fin a × Fin c) → ℂ := fun i => if i.1 then s i.2 else u i.2
  have h := tensorMap_amplify_positive hL hM (outer_posSemidef v)
  have h' := h.submatrix (Sum.elim (fun i => (false,i)) (fun i => (true,i)))
  convert h' using 1
  ext i j
  cases i <;> cases j <;> simp [amplifyTensor, Matrix.submatrix, v, outer, Matrix.fromBlocks] <;> rfl

end TensorBlocks

universe v398_0

variable {ι : Type v398_0} [inst398_0 : Fintype ι] [inst398_1 : DecidableEq ι]

lemma filtered_block_estimate (H Z J F₀ F₁ : Matrix ι ι ℂ)
    (h : (fromBlocks H Z Zᴴ J).PosSemidef) :
    traceNorm (F₀ * Z * F₁ᴴ) ≤
      Real.sqrt ((trace (F₀ * H * F₀ᴴ)).re * (trace (F₁ * J * F₁ᴴ)).re) := by
  have hf := h.mul_mul_conjTranspose_same (fromBlocks F₀ 0 0 F₁)
  have hf' : (fromBlocks (F₀ * H * F₀ᴴ) (F₀ * Z * F₁ᴴ)
      (F₀ * Z * F₁ᴴ)ᴴ (F₁ * J * F₁ᴴ)).PosSemidef := by
    simpa [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_mul, Matrix.mul_assoc] using hf
  exact positive_block_estimate _ _ _ hf'

lemma trace_sqrt_filter (D R : Matrix ι ι ℂ) (hD : D.PosSemidef) :
    trace (CFC.sqrt D * R * CFC.sqrt D) = trace (D * R) := by
  rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self D hD.nonneg]

lemma sqrt_filtered_block_estimate (H Z J D₀ D₁ : Matrix ι ι ℂ)
    (h : (fromBlocks H Z Zᴴ J).PosSemidef) (hD₀ : D₀.PosSemidef) (hD₁ : D₁.PosSemidef) :
    traceNorm (CFC.sqrt D₀ * Z * CFC.sqrt D₁) ≤
      Real.sqrt ((trace (D₀ * H)).re * (trace (D₁ * J)).re) := by
  have hf := filtered_block_estimate H Z J (CFC.sqrt D₀) (CFC.sqrt D₁) h
  simpa only [(CFC.sqrt_nonneg D₀).posSemidef.isHermitian.eq,
    (CFC.sqrt_nonneg D₁).posSemidef.isHermitian.eq, trace_sqrt_filter D₀ H hD₀,
    trace_sqrt_filter D₁ J hD₁] using hf

end

section

lemma tensorMap_outer_block_adjoint {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b}
    {M : Mat c →ₗ[ℂ] Mat d} (hL : CompletelyPositive L) (hM : CompletelyPositive M)
    (u s : Fin a × Fin c → ℂ) :
    (fromBlocks (tensorMap L M (outer u u)) (tensorMap L M (outer u s))
      (tensorMap L M (outer u s))ᴴ (tensorMap L M (outer s s))).PosSemidef := by
  have h := tensorMap_outer_block hL hM u s
  have he := (Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian).2.1
  rwa [he]

lemma direct_block_bound {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b}
    {M : Mat c →ₗ[ℂ] Mat d} (hL : CompletelyPositive L) (hM : CompletelyPositive M)
    (u s : Fin a × Fin c → ℂ) (D₀ D₁ : Matrix (Fin b × Fin d) (Fin b × Fin d) ℂ)
    (hD₀ : D₀.PosSemidef) (hD₁ : D₁.PosSemidef) :
    traceNorm (CFC.sqrt D₀ * tensorMap L M (outer u s) * CFC.sqrt D₁) ≤
      Real.sqrt ((trace (D₀ * tensorMap L M (outer u u))).re *
        (trace (D₁ * tensorMap L M (outer s s))).re) := by
  exact sqrt_filtered_block_estimate _ _ _ _ _
    (tensorMap_outer_block_adjoint hL hM u s) hD₀ hD₁

lemma reversed_block_bound {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b}
    {M : Mat c →ₗ[ℂ] Mat d} (hL : PPTType L) (hM : PPTType M)
    (u s : Fin a × Fin c → ℂ) (D₀ D₁ : Matrix (Fin b × Fin d) (Fin b × Fin d) ℂ)
    (hD₀ : D₀.PosSemidef) (hD₁ : D₁.PosSemidef) :
    traceNorm (CFC.sqrt D₀ * tensorMap L M (outer u s) * CFC.sqrt D₁) ≤
      Real.sqrt ((trace (D₀ * tensorMap L M (outer s s))).re *
        (trace (D₁ * tensorMap L M (outer u u))).re) := by
  have h := direct_block_bound hL.2 hM.2 (star s) (star u) D₀ D₁ hD₀ hD₁
  simpa only [tensorMap_global_transpose, outer_transpose_conj] using h

universe v464_0

variable {ι : Type v464_0} [inst464_0 : Fintype ι] [inst464_1 : DecidableEq ι]

lemma trace_mul_nonneg {S T : Matrix ι ι ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) : 0 ≤ trace (S * T) := by
  let B := CFC.sqrt S
  have hB : Bᴴ = B := (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have h := (hT.mul_mul_conjTranspose_same B).trace_nonneg
  rwa [hB, Matrix.trace_mul_cycle, hBB] at h

lemma psd_of_quadratic_nonneg (A : Matrix ι ι ℂ)
    (h : ∀ x : ι → ℂ, 0 ≤ star x ⬝ᵥ (A *ᵥ x)) : A.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, h⟩
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  rw [LinearMap.isSymmetric_iff_inner_map_self_real]
  intro x
  have hp : 0 ≤ inner ℂ x (A.toEuclideanLin x) := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm] using h (WithLp.ofLp x)
  have hs := (IsSelfAdjoint.of_nonneg hp).star_eq
  rw [← inner_conj_symm]
  simpa only [starRingEnd_apply, star_star] using hs.symm

omit inst464_1 in
lemma trace_mul_outer [DecidableEq ι] (A : Matrix ι ι ℂ) (u s : ι → ℂ) :
    trace (A * outer u s) = star s ⬝ᵥ (A *ᵥ u) := by
  simp only [trace, Matrix.diag, Matrix.mul_apply, outer, dotProduct, mulVec,
    Finset.mul_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def effectDual {a b : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (X : Mat b) : Mat a :=
  fun i j => trace (X * L (matrixUnit j i))

lemma effectDual_pairing {a b : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (X : Mat b) (U : Mat a) :
    trace (effectDual L X * U) = trace (X * L U) := by
  have he : trace (X * L U) = ∑ i, ∑ j, U i j * trace (X * L (matrixUnit i j)) := by
    rw [linearMap_matrix_units L U]
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul]
  rw [he]
  simp only [trace, Matrix.diag, Matrix.mul_apply, effectDual]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma effectDual_positive {a b : ℕ} {L : Mat a →ₗ[ℂ] Mat b}
    (hL : CompletelyPositive L) {X : Mat b} (hX : X.PosSemidef) :
    (effectDual L X).PosSemidef := by
  apply psd_of_quadratic_nonneg
  intro u
  rw [← trace_mul_outer, effectDual_pairing]
  exact trace_mul_nonneg hX (cp_positive hL (outer_posSemidef u))

end

lemma tensorMap_add {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d)
    (U V : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap L M (U+V) = tensorMap L M U + tensorMap L M V := by
  ext i j
  simp [tensorMap, add_mul, Finset.sum_add_distrib]

lemma tensorMap_smul {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d)
    (z : ℂ) (U : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap L M (z • U) = z • tensorMap L M U := by
  ext i j
  simp [tensorMap, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma tensorMap_expansion {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b)
    (M : Mat c →ₗ[ℂ] Mat d) (U : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap L M U = ∑ i, ∑ j, U i j •
      (L (matrixUnit i.1 j.1) ⊗ₖ M (matrixUnit i.2 j.2)) := by
  ext s t
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, tensorMap]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma tensorMap_effect_pairing {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b)
    (M : Mat c →ₗ[ℂ] Mat d) (X : Mat b) (Y : Mat d)
    (U : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    trace ((X ⊗ₖ Y) * tensorMap L M U) = trace ((effectDual L X ⊗ₖ effectDual M Y) * U) := by
  rw [tensorMap_expansion]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, smul_eq_mul]
  simp only [trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply, effectDual]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma tensor_weight_nonneg {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b}
    {M : Mat c →ₗ[ℂ] Mat d} (hL : CompletelyPositive L) (hM : CompletelyPositive M)
    (u : Fin a × Fin c → ℂ) {X : Mat b} {Y : Mat d}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ weight (tensorMap L M (outer u u)) X Y := by
  exact re_trace_mul_nonneg (hX.kronecker hY) (tensorMap_positive hL hM (outer_posSemidef u))

section

universe v590_0

variable {ι : Type v590_0} [inst590_0 : Fintype ι] [inst590_1 : DecidableEq ι]

lemma matrix_cfc_continuous (f : ℝ → ℝ) (H : Matrix ι ι ℂ) :
    ContinuousOn f (spectrum ℝ H) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_of_discreteTopology

lemma matrix_cfc_mul (f g : ℝ → ℝ) (H : Matrix ι ι ℂ) (_hH : H.IsHermitian) :
    cfc (fun t => f t * g t) H = cfc f H * cfc g H := by
  exact cfc_mul f g H (matrix_cfc_continuous f H) (matrix_cfc_continuous g H)

lemma matrix_cfc_nonneg (f : ℝ → ℝ) (H : Matrix ι ι ℂ) (_hH : H.IsHermitian)
    (hf : ∀ t ∈ spectrum ℝ H, 0 ≤ f t) : 0 ≤ cfc f H := by
  exact cfc_nonneg (f := f) (a := H) hf

def whiteningFunction (t : ℝ) : ℝ := if t = 0 then 1 else (Real.sqrt t)⁻¹

def unwhiteningFunction (t : ℝ) : ℝ := if t = 0 then 1 else Real.sqrt t

def supportFunction (t : ℝ) : ℝ := if t = 0 then 0 else 1

lemma whitening_mul_unwhitening {t : ℝ} (ht : 0 ≤ t) :
    whiteningFunction t * unwhiteningFunction t = 1 := by
  by_cases h : t = 0
  · simp [whiteningFunction, unwhiteningFunction, h]
  · simp [whiteningFunction, unwhiteningFunction, h, Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ht (Ne.symm h))]

lemma whitening_square {t : ℝ} (ht : 0 ≤ t) :
    whiteningFunction t * t * whiteningFunction t = supportFunction t := by
  by_cases h : t = 0
  · simp [whiteningFunction, supportFunction, h]
  · have hs : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ht (Ne.symm h))
    simp only [whiteningFunction, supportFunction, ite_eq_right h]
    calc
      _ = (Real.sqrt t)⁻¹ * (Real.sqrt t * Real.sqrt t) * (Real.sqrt t)⁻¹ := by rw [Real.mul_self_sqrt ht]
      _ = 1 := by field_simp

lemma whitening_of_psd (H : Matrix ι ι ℂ) (hH : H.PosSemidef) :
    let S := cfc whiteningFunction H
    let T := cfc unwhiteningFunction H
    let E := cfc supportFunction H
    S.IsHermitian ∧ T.IsHermitian ∧ S * T = 1 ∧ T * S = 1 ∧
      S * H * S = E ∧ IsStarProjection E := by
  dsimp
  have hh : IsSelfAdjoint H := hH.isHermitian
  have ht : ∀ t ∈ spectrum ℝ H, 0 ≤ t := fun t ht =>
    spectrum_nonneg_of_nonneg hH.nonneg ht
  have hST : cfc whiteningFunction H * cfc unwhiteningFunction H = 1 := by
    rw [← matrix_cfc_mul _ _ _ hH.isHermitian]
    have he : cfc (fun t => whiteningFunction t * unwhiteningFunction t) H = cfc (fun _ : ℝ => 1) H := by
      apply cfc_congr
      intro t ht'
      exact whitening_mul_unwhitening (ht t ht')
    rw [he, cfc_const_one ℝ H]
  refine ⟨IsSelfAdjoint.cfc.isHermitian, IsSelfAdjoint.cfc.isHermitian, hST,
    ?_, ?_, ?_⟩
  · rw [(cfc_commute_cfc unwhiteningFunction whiteningFunction H).eq, hST]
  · calc
      _ = cfc whiteningFunction H * cfc (id : ℝ → ℝ) H * cfc whiteningFunction H := by rw [cfc_id ℝ H]
      _ = cfc (fun t => whiteningFunction t * t * whiteningFunction t) H := by
        rw [matrix_cfc_mul _ _ H hH.isHermitian, matrix_cfc_mul _ _ H hH.isHermitian]
        rfl
      _ = _ := cfc_congr (fun t ht' => whitening_square (ht t ht'))
  · constructor
    · change cfc supportFunction H * cfc supportFunction H = cfc supportFunction H
      rw [← matrix_cfc_mul _ _ _ hH.isHermitian]
      apply cfc_congr
      intro t _
      simp [supportFunction]
    · exact IsSelfAdjoint.cfc

end

section

universe v667_0

variable {ι : Type v667_0} [inst667_0 : Fintype ι] [inst667_1 : DecidableEq ι]

def cutFunction (t : ℝ) : ℝ := if 0 ≤ t then 1 else 0

lemma spectral_cut (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    let P := cfc cutFunction H
    IsStarProjection P ∧ Commute P H ∧ (P * H * P).PosSemidef ∧
      ((1-P) * (-H) * (1-P)).PosSemidef := by
  dsimp
  have hh : IsSelfAdjoint H := hH
  have hp : IsStarProjection (cfc cutFunction H) := by
    constructor
    · change cfc cutFunction H * cfc cutFunction H = cfc cutFunction H
      rw [← matrix_cfc_mul _ _ H hH]
      apply cfc_congr
      intro t _
      simp [cutFunction]
    · exact IsSelfAdjoint.cfc
  have hc : Commute (cfc cutFunction H) H := (Commute.refl H).cfc_real _
  have hq : 1 - cfc cutFunction H = cfc (fun t => 1 - cutFunction t) H := by
    rw [cfc_sub _ _ H (matrix_cfc_continuous _ H) (matrix_cfc_continuous _ H), cfc_const_one ℝ H]
  refine ⟨hp, hc, ?_, ?_⟩
  · have he : cfc cutFunction H * H * cfc cutFunction H =
        cfc (fun t => cutFunction t * t * cutFunction t) H := by
      conv_lhs => arg 1; arg 2; rw [← cfc_id ℝ H]
      rw [matrix_cfc_mul _ _ H hH, matrix_cfc_mul _ _ H hH]
      rfl
    rw [he]
    apply LE.le.posSemidef
    apply matrix_cfc_nonneg _ _ hH
    intro t _
    by_cases ht : 0 ≤ t <;> simp [cutFunction, ht]
  · rw [hq]
    have hn : -H = cfc (fun t : ℝ => -t) H := by rw [cfc_neg_id (R := ℝ) H]
    have he : cfc (fun t => 1 - cutFunction t) H * (-H) * cfc (fun t => 1 - cutFunction t) H =
        cfc (fun t => (1-cutFunction t) * (-t) * (1-cutFunction t)) H := by
      conv_lhs => arg 1; arg 2; rw [hn]
      rw [matrix_cfc_mul _ _ H hH, matrix_cfc_mul _ _ H hH]
    rw [he]
    apply LE.le.posSemidef
    apply matrix_cfc_nonneg _ _ hH
    intro t _
    by_cases ht : 0 ≤ t <;> simp [cutFunction, ht]
    linarith

open scoped Matrix.Norms.L2Operator in
lemma commute_of_sum_projection (A B E : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hE : IsStarProjection E) (hsum : A+B=E) :
    Commute A B := by
  have hle : A ≤ E := by rw [← hsum]; exact le_add_of_nonneg_right hB.nonneg
  have hsupp := hE.mul_right_and_mul_left_of_nonneg_of_le hA.nonneg hle
  have he : B = E - A := by rw [← hsum]; abel
  change A * B = B * A
  rw [he, mul_sub, sub_mul, hsupp.1, hsupp.2]

lemma whitened_effects_commute (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let S := cfc whiteningFunction (A+B)
    (S * A * S).PosSemidef ∧ (S * B * S).PosSemidef ∧
      Commute (S * A * S) (S * B * S) := by
  dsimp
  let S := cfc whiteningFunction (A+B)
  let E := cfc supportFunction (A+B)
  have hw := whitening_of_psd (A+B) (hA.add hB)
  dsimp at hw
  have hS : Sᴴ = S := hw.1.eq
  have hSA : (S * A * S).PosSemidef := by
    simpa only [hS] using hA.mul_mul_conjTranspose_same S
  have hSB : (S * B * S).PosSemidef := by
    simpa only [hS] using hB.mul_mul_conjTranspose_same S
  have hsum : S * A * S + S * B * S = E := by
    rw [← add_mul, ← mul_add]
    exact hw.2.2.2.2.1
  exact ⟨hSA, hSB, commute_of_sum_projection _ _ E hSA hSB hw.2.2.2.2.2 hsum⟩

end

section

universe v746_0

variable {ι : Type v746_0} [inst746_0 : Fintype ι] [inst746_1 : DecidableEq ι]

lemma projection_cross_zero {P A : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hPA : Commute P A) : P * A * (1-P) = 0 := by
  rw [hPA.eq, mul_assoc, hP.mul_one_sub_self, mul_zero]

lemma commuting_spectral_cut (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ P : Matrix ι ι ℂ, IsStarProjection P ∧ Commute P A ∧ Commute P B ∧
      (P * (A-B) * P).PosSemidef ∧ ((1-P) * (B-A) * (1-P)).PosSemidef := by
  let P := cfc cutFunction (A-B)
  have h := spectral_cut (A-B) (hA.sub hB)
  have ha : Commute (A-B) A := (Commute.refl A).sub_left hAB.symm
  have hb : Commute (A-B) B := hAB.sub_left (Commute.refl B)
  refine ⟨P, h.1, ha.cfc_real _, hb.cfc_real _, h.2.2.1, ?_⟩
  simpa only [neg_sub] using h.2.2.2

lemma congruence_cross (S T P A : Matrix ι ι ℂ)
    (hS : S.IsHermitian) (hT : T.IsHermitian) (hP : P.IsHermitian) :
    (S * P * T)ᴴ * A * (S * (1-P) * T) = T * (P * (S*A*S) * (1-P)) * T := by
  simp only [Matrix.conjTranspose_mul, hS.eq, hT.eq, hP.eq]
  noncomm_ring

omit inst746_1 in
lemma congruence_diagonal [DecidableEq ι] (S T P A : Matrix ι ι ℂ)
    (hS : S.IsHermitian) (hT : T.IsHermitian) (hP : P.IsHermitian) :
    (S * P * T)ᴴ * A * (S * P * T) = T * (P * (S*A*S) * P) * T := by
  simp only [Matrix.conjTranspose_mul, hS.eq, hT.eq, hP.eq]
  noncomm_ring

lemma generalized_effect_split (A B : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    ∃ V W : Matrix ι ι ℂ, V + W = 1 ∧ Vᴴ * A * W = 0 ∧ Vᴴ * B * W = 0 ∧
      (Vᴴ * (A-B) * V).PosSemidef ∧ (Wᴴ * (B-A) * W).PosSemidef := by
  let S := cfc whiteningFunction (A+B)
  let T := cfc unwhiteningFunction (A+B)
  have hw := whitening_of_psd (A+B) (hA.add hB)
  have hS : S.IsHermitian := hw.1
  have hT : T.IsHermitian := hw.2.1
  have hST : S*T=1 := hw.2.2.1
  have hc := whitened_effects_commute A B hA hB
  obtain ⟨P, hP, hpA, hpB, hpplus, hpminus⟩ :=
    commuting_spectral_cut (S*A*S) (S*B*S) hc.1.isHermitian hc.2.1.isHermitian hc.2.2
  have hP' : P.IsHermitian := hP.isSelfAdjoint
  have hQ : (1-P).IsHermitian := Matrix.isHermitian_one.sub hP'
  refine ⟨S*P*T, S*(1-P)*T, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ = S * (P + (1-P)) * T := by noncomm_ring
      _ = 1 := by simp [hST]
  · rw [congruence_cross S T P A hS hT hP', projection_cross_zero hP hpA, mul_zero, zero_mul]
  · rw [congruence_cross S T P B hS hT hP', projection_cross_zero hP hpB, mul_zero, zero_mul]
  · rw [congruence_diagonal S T P (A-B) hS hT hP']
    have he : S * (A-B) * S = S*A*S - S*B*S := by noncomm_ring
    rw [he]
    simpa only [hT.eq] using hpplus.mul_mul_conjTranspose_same T
  · rw [congruence_diagonal S T (1-P) (B-A) hS hT hQ]
    have he : S * (B-A) * S = S*B*S - S*A*S := by noncomm_ring
    rw [he]
    simpa only [hT.eq] using hpminus.mul_mul_conjTranspose_same T

end

section

universe v812_0

variable {ι : Type v812_0} [inst812_0 : Fintype ι] [inst812_1 : DecidableEq ι]

def qform (A : Matrix ι ι ℂ) (u : ι → ℂ) : ℝ := (star u ⬝ᵥ (A *ᵥ u)).re

omit inst812_1 in
lemma qform_nonneg [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (u : ι → ℂ) :
    0 ≤ qform A u := by
  exact (hA.dotProduct_mulVec_nonneg u).1

omit inst812_1 in
lemma qform_congruence [DecidableEq ι] (A T : Matrix ι ι ℂ) (u : ι → ℂ) :
    qform A (T *ᵥ u) = qform (Tᴴ * A * T) u := by
  simp only [qform, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, mul_assoc]

omit inst812_1 in
lemma qform_add [DecidableEq ι] (A B : Matrix ι ι ℂ) (u : ι → ℂ) :
    qform (A+B) u = qform A u + qform B u := by
  simp [qform, Matrix.add_mulVec, dotProduct_add]

omit inst812_1 in
lemma qform_sub [DecidableEq ι] (A B : Matrix ι ι ℂ) (u : ι → ℂ) :
    qform (A-B) u = qform A u - qform B u := by
  simp [qform, Matrix.sub_mulVec, dotProduct_sub]

lemma tensor_qform_eq_weight {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b)
    (M : Mat c →ₗ[ℂ] Mat d) (X : Mat b) (Y : Mat d) (u : Fin a × Fin c → ℂ) :
    weight (tensorMap L M (outer u u)) X Y = qform (effectDual L X ⊗ₖ effectDual M Y) u := by
  rw [weight, tensorMap_effect_pairing, trace_mul_outer]
  rfl

lemma tensor_filter_congruence {a c : ℕ} (A V W : Mat a) (B : Mat c) :
    (V ⊗ₖ (1 : Mat c))ᴴ * (A ⊗ₖ B) * (W ⊗ₖ (1 : Mat c)) =
      (Vᴴ * A * W) ⊗ₖ B := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one]

lemma filter_qform_split {A V W : Matrix ι ι ℂ} (hVW : V+W=1)
    (hA : A.IsHermitian) (hcross : Vᴴ * A * W=0) (u : ι → ℂ) :
    qform A u = qform A (V *ᵥ u) + qform A (W *ᵥ u) := by
  have hcross' : Wᴴ * A * V=0 := by
    have h := congrArg Matrix.conjTranspose hcross
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA.eq, Matrix.conjTranspose_zero, mul_assoc] using h
  have he : A = Vᴴ*A*V + Wᴴ*A*W := by
    calc
      A = (V+W)ᴴ*A*(V+W) := by simp [hVW]
      _ = Vᴴ*A*V + Wᴴ*A*W := by
        simp only [Matrix.conjTranspose_add, add_mul, mul_add, hcross, hcross']
        abel
  rw [qform_congruence, qform_congruence, ← qform_add, ← he]

lemma input_split_weights {a c : ℕ} (A₀ A₁ : Mat a) (B₀ B₁ : Mat c)
    (hA₀ : A₀.PosSemidef) (hA₁ : A₁.PosSemidef)
    (hB₀ : B₀.PosSemidef) (hB₁ : B₁.PosSemidef) (χ : Fin a × Fin c → ℂ) :
    ∃ v w, χ = v+w ∧
      (∀ A ∈ ({A₀,A₁} : Finset (Mat a)), ∀ B ∈ ({B₀,B₁} : Finset (Mat c)),
        qform (A ⊗ₖ B) χ = qform (A ⊗ₖ B) v + qform (A ⊗ₖ B) w) ∧
      qform (A₁ ⊗ₖ B₁) v ≤ qform (A₀ ⊗ₖ B₁) v ∧
      qform (A₀ ⊗ₖ B₀) w ≤ qform (A₁ ⊗ₖ B₀) w := by
  classical
  obtain ⟨V,W,hVW,hcross₀,hcross₁,hplus,hminus⟩ := generalized_effect_split A₀ A₁ hA₀ hA₁
  let VV := V ⊗ₖ (1 : Mat c)
  let WW := W ⊗ₖ (1 : Mat c)
  have hVVWW : VV+WW=1 := by
    dsimp [VV, WW]
    rw [← Matrix.add_kronecker, hVW, Matrix.one_kronecker_one]
  refine ⟨VV *ᵥ χ, WW *ᵥ χ, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.add_mulVec, hVVWW, Matrix.one_mulVec]
  · intro A hA B hB
    have hc : Vᴴ*A*W=0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl <;> assumption
    have hAp : A.PosSemidef := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl <;> assumption
    have hBp : B.PosSemidef := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hB
      rcases hB with rfl | rfl <;> assumption
    apply filter_qform_split hVVWW (hAp.kronecker hBp).isHermitian
    dsimp [VV, WW]
    rw [tensor_filter_congruence, hc, Matrix.zero_kronecker]
  · have h := qform_nonneg (hplus.kronecker hB₁) χ
    rw [qform_congruence, qform_congruence]
    dsimp [VV]
    rw [tensor_filter_congruence, tensor_filter_congruence]
    have he : (Vᴴ * (A₀-A₁) * V) ⊗ₖ B₁ =
        (Vᴴ*A₀*V) ⊗ₖ B₁ - (Vᴴ*A₁*V) ⊗ₖ B₁ := by
      rw [mul_sub, sub_mul]
      ext i j
      simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]
    rw [he, qform_sub] at h
    linarith
  · have h := qform_nonneg (hminus.kronecker hB₀) χ
    rw [qform_congruence, qform_congruence]
    dsimp [WW]
    rw [tensor_filter_congruence, tensor_filter_congruence]
    have he : (Wᴴ * (A₁-A₀) * W) ⊗ₖ B₀ =
        (Wᴴ*A₁*W) ⊗ₖ B₀ - (Wᴴ*A₀*W) ⊗ₖ B₀ := by
      rw [mul_sub, sub_mul]
      ext i j
      simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]
    rw [he, qform_sub] at h
    linarith

end

universe v919_0

lemma outer_add_four {ι : Type v919_0} (v w : ι → ℂ) :
    outer (v+w) (v+w) = outer v v + outer w w + outer v w + outer w v := by
  ext i j
  simp only [outer, Pi.add_apply, star_add, Matrix.add_apply]
  ring

lemma sqrt_mul_mono {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hac : a ≤ c) (hbd : b ≤ d) : Real.sqrt (a*b) ≤ Real.sqrt (c*d) :=
  Real.sqrt_le_sqrt (mul_le_mul hac hbd hb hc)

theorem four_effect_inequality {a b : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (X₀ X₁ : Mat a) (Y₀ Y₁ : Mat b)
    (hX₀ : X₀.PosSemidef) (hX₁ : X₁.PosSemidef)
    (hY₀ : Y₀.PosSemidef) (hY₁ : Y₁.PosSemidef) :
    traceNorm (CFC.sqrt (X₀ ⊗ₖ Y₀) * R * CFC.sqrt (X₁ ⊗ₖ Y₁)) ≤
      Real.sqrt (weight R X₀ Y₀ * weight R X₀ Y₁) +
      Real.sqrt (weight R X₁ Y₀ * weight R X₁ Y₁) +
      2 * Real.sqrt (weight R X₀ Y₁ * weight R X₁ Y₀) := by
  classical
  obtain ⟨_,c,d,L,M,χ,hL,hM,rfl⟩ := hR
  let A₀ := effectDual L X₀
  let A₁ := effectDual L X₁
  let B₀ := effectDual M Y₀
  let B₁ := effectDual M Y₁
  obtain ⟨v,w,hχ,hsplit,hv,hw⟩ := input_split_weights A₀ A₁ B₀ B₁
    (effectDual_positive hL.1 hX₀) (effectDual_positive hL.1 hX₁)
    (effectDual_positive hM.1 hY₀) (effectDual_positive hM.1 hY₁) χ
  let p := fun X Y u => weight (tensorMap L M (outer u u)) X Y
  let Z := fun u s => CFC.sqrt (X₀ ⊗ₖ Y₀) * tensorMap L M (outer u s) *
    CFC.sqrt (X₁ ⊗ₖ Y₁)
  have hpos (X : Mat a) (Y : Mat b) (hX : X.PosSemidef) (hY : Y.PosSemidef)
      (u : Fin c × Fin d → ℂ) : 0 ≤ p X Y u := tensor_weight_nonneg hL.1 hM.1 u hX hY
  have hsplit' (X : Mat a) (hX : X ∈ ({X₀,X₁} : Finset (Mat a)))
      (Y : Mat b) (hY : Y ∈ ({Y₀,Y₁} : Finset (Mat b))) :
      p X Y χ = p X Y v + p X Y w := by
    dsimp [p]
    simp only [tensor_qform_eq_weight]
    apply hsplit
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hX ⊢
      rcases hX with rfl | rfl <;> tauto
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hY ⊢
      rcases hY with rfl | rfl <;> tauto
  have hmono (X : Mat a) (hX : X ∈ ({X₀,X₁} : Finset (Mat a)))
      (Y : Mat b) (hY : Y ∈ ({Y₀,Y₁} : Finset (Mat b))) :
      p X Y v ≤ p X Y χ ∧ p X Y w ≤ p X Y χ := by
    have hXp : X.PosSemidef := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl <;> assumption
    have hYp : Y.PosSemidef := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl <;> assumption
    have he := hsplit' X hX Y hY
    have hvp := hpos X Y hXp hYp v
    have hwp := hpos X Y hXp hYp w
    constructor <;> linarith
  have h00 := hmono X₀ (by simp) Y₀ (by simp)
  have h01 := hmono X₀ (by simp) Y₁ (by simp)
  have h10 := hmono X₁ (by simp) Y₀ (by simp)
  have h11 := hmono X₁ (by simp) Y₁ (by simp)
  have hv' : p X₁ Y₁ v ≤ p X₀ Y₁ v := by simpa [p, tensor_qform_eq_weight, A₀,A₁,B₀,B₁] using hv
  have hw' : p X₀ Y₀ w ≤ p X₁ Y₀ w := by simpa [p, tensor_qform_eq_weight, A₀,A₁,B₀,B₁] using hw
  have hdir (u s : Fin c × Fin d → ℂ) :
      traceNorm (Z u s) ≤ Real.sqrt (p X₀ Y₀ u * p X₁ Y₁ s) :=
    direct_block_bound hL.1 hM.1 u s _ _ (hX₀.kronecker hY₀) (hX₁.kronecker hY₁)
  have hrev (u s : Fin c × Fin d → ℂ) :
      traceNorm (Z u s) ≤ Real.sqrt (p X₀ Y₀ s * p X₁ Y₁ u) :=
    reversed_block_bound hL hM u s _ _ (hX₀.kronecker hY₀) (hX₁.kronecker hY₁)
  have hvv : traceNorm (Z v v) ≤ Real.sqrt (p X₀ Y₀ χ * p X₀ Y₁ χ) :=
    (hdir v v).trans (sqrt_mul_mono (hpos _ _ hX₁ hY₁ v) (hpos _ _ hX₀ hY₀ χ)
      h00.1 (hv'.trans h01.1))
  have hww : traceNorm (Z w w) ≤ Real.sqrt (p X₁ Y₀ χ * p X₁ Y₁ χ) :=
    (hdir w w).trans (sqrt_mul_mono (hpos _ _ hX₁ hY₁ w) (hpos _ _ hX₁ hY₀ χ)
      (hw'.trans h10.2) h11.2)
  have hcross : Real.sqrt (p X₀ Y₀ w * p X₁ Y₁ v) ≤
      Real.sqrt (p X₀ Y₁ χ * p X₁ Y₀ χ) := by
    rw [mul_comm (p X₀ Y₁ χ)]
    exact sqrt_mul_mono (hpos _ _ hX₁ hY₁ v) (hpos _ _ hX₁ hY₀ χ)
      (hw'.trans h10.2) (hv'.trans h01.1)
  have hvw := (hrev v w).trans hcross
  have hwv := (hdir w v).trans hcross
  have hZ : Z χ χ = Z v v + Z w w + Z v w + Z w v := by
    dsimp [Z]
    rw [hχ, outer_add_four]
    simp only [tensorMap_add, mul_add, add_mul]
  change traceNorm (Z χ χ) ≤ _
  rw [hZ]
  have ht₁ := traceNorm_add_le (Z v v) (Z w w)
  have ht₂ := traceNorm_add_le (Z v v + Z w w) (Z v w)
  have ht₃ := traceNorm_add_le (Z v v + Z w w + Z v w) (Z w v)
  change traceNorm _ ≤ Real.sqrt (p X₀ Y₀ χ * p X₀ Y₁ χ) +
    Real.sqrt (p X₁ Y₀ χ * p X₁ Y₁ χ) + 2 * Real.sqrt (p X₀ Y₁ χ * p X₁ Y₀ χ)
  linarith

universe v1039_0

lemma cp_sum {a b : ℕ} {ν : Type v1039_0} [Fintype ν] (L : ν → Mat a →ₗ[ℂ] Mat b)
    (hL : ∀ s, CompletelyPositive (L s)) : CompletelyPositive (∑ s, L s) := by
  intro r U hU
  have he : amplify (∑ s, L s) r U = ∑ s, amplify (L s) r U := by
    ext i j
    change (∑ s, L s) (fun x y => U (i.1,x) (j.1,y)) i.2 j.2 = _
    erw [LinearMap.sum_apply]
    simp only [Matrix.sum_apply, amplify]

  rw [he]
  exact Matrix.posSemidef_sum _ (fun s _ => hL s r U hU)

lemma cp_comp {a b c : ℕ} {L : Mat b →ₗ[ℂ] Mat c} {M : Mat a →ₗ[ℂ] Mat b}
    (hL : CompletelyPositive L) (hM : CompletelyPositive M) : CompletelyPositive (L.comp M) := by
  intro r U hU
  exact hL r (amplify M r U) (hM r U hU)

def tensorLinear {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d) :
    Mat (a*c) →ₗ[ℂ] Mat (b*d) where
  toFun U := (tensorMap L M (U.submatrix finProdFinEquiv finProdFinEquiv)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm
  map_add' U V := by
    simp only [Matrix.submatrix_add, Pi.add_apply, tensorMap_add]
  map_smul' z U := by
    simp only [Matrix.submatrix_smul, Pi.smul_apply, tensorMap_smul, RingHom.id_apply]

lemma cp_tensorLinear {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b} {M : Mat c →ₗ[ℂ] Mat d}
    (hL : CompletelyPositive L) (hM : CompletelyPositive M) : CompletelyPositive (tensorLinear L M) := by
  intro r U hU
  have h := (tensorMap_amplify_positive hL hM
    (hU.submatrix (fun i : Fin r × (Fin a × Fin c) => (i.1, finProdFinEquiv i.2)))).submatrix
      (fun i : Fin r × Fin (b*d) => (i.1, finProdFinEquiv.symm i.2))
  exact h

lemma tensorLinear_transpose {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d) :
    (tensorLinear L M).comp (transposeLinear (a*c)) =
      tensorLinear (L.comp (transposeLinear a)) (M.comp (transposeLinear c)) := by
  ext U i j
  exact congr_fun (congr_fun (tensorMap_global_transpose L M
    (U.submatrix finProdFinEquiv finProdFinEquiv)).symm
      (finProdFinEquiv.symm i)) (finProdFinEquiv.symm j)

lemma ppt_tensorLinear {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b} {M : Mat c →ₗ[ℂ] Mat d}
    (hL : PPTType L) (hM : PPTType M) : PPTType (tensorLinear L M) := by
  refine ⟨cp_tensorLinear hL.1 hM.1, ?_⟩
  rw [tensorLinear_transpose]
  exact cp_tensorLinear hL.2 hM.2

end ZeroKey

end

end OAI
