import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRank
import OAI.Probability.InvariantIsing.Cavity.CavityWindowGram

namespace OAI

/-! Positive definiteness of finite Gaussian and normalized-frame windows. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator NNReal

namespace InvariantIsing

/-- Any consecutive square block of the iid Gaussian row sequence is
nonsingular almost surely. -/
theorem cavityGaussianRows_window_det_ne_zero (q l : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Matrix.det (fun i j : Fin q => x (l + i) j) ≠ 0 := by
  let f : Fin q × Fin q → ℕ × Fin q := fun p => (l + p.1, p.2)
  have hf : Function.Injective f := by
    intro p r h
    apply Prod.ext
    · apply Fin.ext
      exact Nat.add_left_cancel (congrArg Prod.fst h)
    · exact congrArg (fun z : ℕ × Fin q => z.2) h
  have hi := (cavityGaussianRows_coordinates_independent q).precomp hf
  have hm := hi.map_fun_eq_pi_map (fun p : Fin q × Fin q =>
    (cavityGaussianRows_coordinate_law (l + p.1) p.2).aemeasurable)
  have hmap : (cavityGaussianRows q).map
      (fun x => fun p : Fin q × Fin q => x (l + p.1) p.2) =
        Measure.pi (fun _ : Fin q × Fin q => gaussianReal 0 1) := by
    simpa only [(cavityGaussianRows_coordinate_law _ _).map_eq] using hm
  have hh : ∀ᵐ y ∂(cavityGaussianRows q).map
      (fun x => fun p : Fin q × Fin q => x (l + p.1) p.2),
      Matrix.det (fun i j : Fin q => y (i, j)) ≠ 0 := by
    rw [hmap]
    exact cavityGaussianSquare_det_ne_zero q
  have hm : Measurable
      (fun x : ℕ → Fin q → ℝ => fun p : Fin q × Fin q => x (l + p.1) p.2) := by
    fun_prop
  have he : ∀ᵐ x ∂cavityGaussianRows q,
      Matrix.det (fun i j : Fin q => x (l + i) j) ≠ 0 :=
    ae_of_ae_map hm.aemeasurable hh
  exact he

lemma cavity_gram_posDef_of_minor {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (f : Fin q → Fin N) (hdet : (A.submatrix f id).det ≠ 0) :
    (A.transpose * A).PosDef := by
  have hB : Function.Injective (A.submatrix f id).mulVec :=
    Matrix.mulVec_injective_iff.mpr
      ((Matrix.nonsingular_iff_det_ne_zero.mpr hdet).linearIndependent_col)
  have hA : Function.Injective A.mulVec := by
    intro x y hxy
    apply hB
    funext i
    simpa only [Matrix.mulVec, Matrix.submatrix_apply, id_eq, dotProduct] using
      congrFun hxy (f i)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self A hA

lemma cavityWindowGram_mul {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (C : Matrix (Fin q) (Fin q) ℝ) (l u : ℕ) :
    cavityWindowGram (A * C) l u = C.transpose * cavityWindowGram A l u * C := by
  simp only [cavityWindowGram, cavityPrefixGram_mul]
  noncomm_ring

def cavityMaskedRows {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) (l u : ℕ) :
    Matrix (Fin N) (Fin q) ℝ :=
  fun k i => if l ≤ k.val ∧ k.val < u then A k i else 0

lemma cavityWindowGram_eq_mask_gram {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (l u : ℕ) (hlu : l ≤ u) :
    cavityWindowGram A l u =
      (cavityMaskedRows A l u).transpose * cavityMaskedRows A l u := by
  ext i j
  simp only [cavityWindowGram, Matrix.sub_apply, cavityPrefixGram_apply,
    ← Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.transpose_apply, cavityMaskedRows]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkl : k.val < l
  · have hku : k.val < u := lt_of_lt_of_le hkl hlu
    simp [hkl, hku, Nat.not_le_of_lt hkl]
  · by_cases hku : k.val < u
    · simp [hkl, hku, Nat.le_of_not_gt hkl]
    · simp [hkl, hku]

lemma cavityWindowGram_posDef_of_minor {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (l u : ℕ) (hlu : l ≤ u) (f : Fin q → Fin N)
    (hf : ∀ i, l ≤ (f i).val ∧ (f i).val < u)
    (hdet : (A.submatrix f id).det ≠ 0) :
    (cavityWindowGram A l u).PosDef := by
  rw [cavityWindowGram_eq_mask_gram A l u hlu]
  apply cavity_gram_posDef_of_minor _ f
  convert hdet using 1
  congr 1
  ext i j
  simp [Matrix.submatrix_apply, cavityMaskedRows, hf i]

/-- Positive definiteness holds at every admissible finite row count. -/
theorem cavityGaussianRows_gram_posDef (N q : ℕ) (hqN : q ≤ N) :
    ∀ᵐ x ∂cavityGaussianRows q, (cavityEmpiricalGram x N).PosDef := by
  by_cases hq : q = 0
  · subst q
    apply ae_of_all
    intro x
    exact cavity_posDef_of_posSemidef_det_ne_zero
      (cavityEmpiricalGram_posSemidef x N)
      (by
        have h : (cavityEmpiricalGram x N).det = 1 := Matrix.det_isEmpty
        exact h.trans_ne one_ne_zero)
  have hN : 0 < N := by omega
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.mpr hN))
  filter_upwards [cavityGaussianRows_square_det_ne_zero q] with x hx
  let A := cavityGaussianMatrix x N
  let f : Fin q → Fin N := Fin.castLE hqN
  let B : Matrix (Fin q) (Fin q) ℝ := fun i j => x i j
  have he : A.submatrix f id = (Real.sqrt (N : ℝ))⁻¹ • B := by
    ext i j
    change x i j / Real.sqrt (N : ℝ) = (Real.sqrt (N : ℝ))⁻¹ * x i j
    ring
  have hdet : (A.submatrix f id).det ≠ 0 := by
    rw [he, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hsqrt)) hx
  rw [← cavityGaussianMatrix_gram]
  exact cavity_gram_posDef_of_minor A f hdet

lemma cavityGoodGram_probability_one (N q : ℕ) (hqN : q ≤ N) :
    cavityGaussianRows q (cavityGoodGram q N) = 1 := by
  have hae : cavityGoodGram q N =ᵐ[cavityGaussianRows q] Set.univ := by
    filter_upwards [cavityGaussianRows_gram_posDef N q hqN] with x hx
    change (0 < (cavityEmpiricalGram x N).det) = True
    exact propext (iff_true_intro hx.det_pos)
  rw [measure_congr hae, measure_univ]

/-- Every window containing at least `q` rows is positive definite at
finite volume, before and after the common Gram normalization. -/
theorem cavityGaussianRows_normalized_window_posDef (N q l u : ℕ)
    (hlq : l + q ≤ u) (huN : u ≤ N) :
    ∀ᵐ x ∂cavityGaussianRows q,
      (cavityWindowGram (cavityNormalizeFrame (cavityGaussianMatrix x N)) l u).PosDef := by
  have hlu : l ≤ u := by omega
  by_cases hq : q = 0
  · subst q
    apply ae_of_all
    intro x
    exact cavity_posDef_of_posSemidef_det_ne_zero
      (cavityWindowGram_posSemidef _ l u hlu) (by
        have h : (cavityWindowGram
          (cavityNormalizeFrame (cavityGaussianMatrix x N)) l u).det = 1 := Matrix.det_isEmpty
        exact h.trans_ne one_ne_zero)
  have hN : 0 < N := by omega
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.mpr hN))
  filter_upwards [cavityGaussianRows_window_det_ne_zero q l] with x hx
  let A := cavityGaussianMatrix x N
  let f : Fin q → Fin N := fun i => ⟨l + i.val, by omega⟩
  have hf : ∀ i, l ≤ (f i).val ∧ (f i).val < u := by
    intro i
    dsimp [f]
    constructor <;> omega
  let B : Matrix (Fin q) (Fin q) ℝ := fun i j => x (l + i) j
  have he : A.submatrix f id = (Real.sqrt (N : ℝ))⁻¹ • B := by
    ext i j
    change x (l + i) j / Real.sqrt (N : ℝ) = (Real.sqrt (N : ℝ))⁻¹ * x (l + i) j
    ring
  have hdet : (A.submatrix f id).det ≠ 0 := by
    rw [he, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hsqrt)) hx
  have hG := cavity_gram_posDef_of_minor A f hdet
  have hW := cavityWindowGram_posDef_of_minor A l u hlu f hf hdet
  have hS := cavity_sqrt_det_isUnit (A.transpose * A) hG
  let C := (CFC.sqrt (A.transpose * A))⁻¹
  have hC : Function.Injective C.mulVec := by
    apply Matrix.mulVec_injective_iff.mpr
    apply Matrix.Nonsingular.linearIndependent_col
    apply Matrix.nonsingular_iff_det_ne_zero.mpr
    exact (Matrix.isUnit_nonsing_inv_det (CFC.sqrt (A.transpose * A)) hS).ne_zero
  change (cavityWindowGram (A * C) l u).PosDef
  rw [cavityWindowGram_mul]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hW.conjTranspose_mul_mul_same hC

end InvariantIsing

end

end OAI
