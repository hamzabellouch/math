import OAI.Analysis.TriangularHilbert.PlaneChart

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma abs_le_one_add_sq (x : ℝ) : |x| ≤ 1+x^2 := by
  nlinarith [sq_nonneg (|x|-1), sq_abs x]

lemma planePoly_ge_first (z : ℝ × ℝ) : |z.1| ≤ planePoly z := by
  have := abs_le_one_add_sq z.1
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]

lemma planePoly_ge_second (z : ℝ × ℝ) : |z.2| ≤ planePoly z := by
  have := abs_le_one_add_sq z.2
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]

lemma chart_abs_bound {D d : ℝ} (hd : |d| ≤ D) (i w : Three) (z : ℝ × ℝ) :
    |chart i d z w| ≤ (D+2) * planePoly z := by
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have hP := one_le_planePoly z
  have hx := planePoly_ge_first z
  have hy := planePoly_ge_second z
  have hDP : D ≤ D * planePoly z := by nlinarith
  have hab : |d-z.1-z.2| ≤ |d|+|z.1|+|z.2| := by
    calc
      _ ≤ |d-z.1| + |z.2| := by simpa using abs_sub_le (d-z.1) 0 z.2
      _ ≤ _ := by simpa using add_le_add_right (abs_sub_le d 0 z.1) (abs z.2)
  fin_cases i <;> fin_cases w <;> simp [chart] <;> nlinarith

lemma endpoint_gaussian_bound {D d b : ℝ} (hb : 0 < b) (hd : |d| ≤ D)
    (i j k : Three) (hjk : j ≠ k) (z : ℝ × ℝ) :
    Real.exp (-((chart i d z j)^2+(chart i d z k)^2)/(8*b)) ≤
      Real.exp (3*D^2/(32*b)) * planeGaussian (1/(32*b)) z := by
  have hh := chart_pair_bound hd i j k hjk z
  rw [planeGaussian, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : -((chart i d z j)^2+(chart i d z k)^2)/(8*b) ≤
      (3*D^2-(z.1^2+z.2^2))/(32*b) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 8*b) (by positivity : 0 < 32*b)]
    nlinarith
  convert! he using 1
  ring

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def rootCoefficient (h a b u : ℝ) : ℝ :=
  Real.sqrt (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b)))

omit [DecidableEq ι] in
lemma exists_heatArray_gaussian_bound (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (_hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Three → ℝ) (i : Three) (d : ℝ) (z : ℝ × ℝ),
      |d| ≤ D → p = chart i d z → ∀ (σ : Three → ℝ),
      (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → ∀ v k l,
      ‖heatArray A h u p σ v k l‖ ≤ C * planeGaussian (1/(32*b)) z := by
  let K : Three × ι × ι → ℝ := fun t => rootCoefficient h a b (u t.2.1) *
    ‖A t.1 t.2.1 t.2.2‖ * rootCoefficient h a b (u t.2.2)
  have hK t : 0 ≤ K t := by dsimp [K, rootCoefficient]; positivity
  let C := (∑ t, K t) * Real.exp (3*D^2/(32*b))
  refine ⟨C, mul_nonneg (Finset.sum_nonneg (fun t _ => hK t)) (Real.exp_pos _).le, ?_⟩
  intro p i d z hd hp σ hσa hσb v k l
  subst p
  have hb := ha.trans_le hab
  have hv : v ≠ v+1 := by fin_cases v <;> decide
  have hleft := rootWeight_le_gaussian hh.le ha (hσa v) (hσb v) (u k) (chart i d z v)
  have hright := rootWeight_le_gaussian hh.le ha (hσa (v+1)) (hσb (v+1)) (u l) (chart i d z (v+1))
  have hc : K (v,k,l) ≤ ∑ t, K t := Finset.single_le_sum (fun t _ => hK t) (Finset.mem_univ _)
  calc
    _ = Real.sqrt (weight h (u k) (chart i d z v) (σ v)) * ‖A v k l‖ *
        Real.sqrt (weight h (u l) (chart i d z (v+1)) (σ (v+1))) := by
      simp only [heatArray, weightedArray, heatWeights, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ (rootCoefficient h a b (u k) * Real.exp (-(chart i d z v)^2/(8*b))) * ‖A v k l‖ *
        (rootCoefficient h a b (u l) * Real.exp (-(chart i d z (v+1))^2/(8*b))) := by
      dsimp only [rootCoefficient]
      gcongr
    _ = K (v,k,l) * Real.exp (-((chart i d z v)^2+(chart i d z (v+1))^2)/(8*b)) := by
      dsimp [K]
      rw [show -((chart i d z v)^2+(chart i d z (v+1))^2)/(8*b) =
        -(chart i d z v)^2/(8*b) + -(chart i d z (v+1))^2/(8*b) by ring, Real.exp_add]
      ring
    _ ≤ (∑ t, K t) * (Real.exp (3*D^2/(32*b)) * planeGaussian (1/(32*b)) z) := by
      exact mul_le_mul hc (endpoint_gaussian_bound hb hd i v (v+1) hv z)
        (Real.exp_pos _).le (Finset.sum_nonneg (fun t _ => hK t))
    _ = _ := by dsimp [C]; ring

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_entry_bound (W : Three → Matrix ι ι ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hW : ∀ v i j, ‖W v i j‖ ≤ M) (a b : Three) (i j : ι) :
    ‖triangleBlocks W a b i j‖ ≤ M := by
  fin_cases a <;> fin_cases b <;> simp [triangleBlocks, Matrix.conjTranspose_apply]
  all_goals first | exact hM | exact hW _ _ _

lemma norm_rowStar_le_bound (W : Three → Matrix ι ι ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hW : ∀ v i j, ‖W v i j‖ ≤ M) (v : Three) :
    ‖rowStar W v‖ ≤ entryNormConstant (BlockSpace ι) * M := by
  apply norm_matrix_le_entries
  intro a b
  rw [rowStar_apply]
  split_ifs
  · exact triangleBlocks_entry_bound W hM hW _ _ _ _
  · simpa using hM

lemma exists_heatCarrier_gaussian_bound (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D →
      ∀ (σ : Three → ℝ), (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → ∀ v w,
      ‖heatCarrier A h u (chart i d z) σ v w‖ ≤ C * planeGaussian (1/(32*b)) z := by
  obtain ⟨C,hC,hbound⟩ := exists_heatArray_gaussian_bound A hh ha hab hD u
  refine ⟨entryNormConstant (BlockSpace ι) * C, mul_nonneg entryNormConstant_nonneg hC, ?_⟩
  intro i d z hd σ hσa hσb v w
  rw [heatCarrier_norm]
  calc
    _ ≤ entryNormConstant (BlockSpace ι) * (C * planeGaussian (1/(32*b)) z) :=
      norm_rowStar_le_bound _ (mul_nonneg hC (planeGaussian_pos _ _).le)
        (hbound _ i d z hd rfl σ hσa hσb) v
    _ = _ := by ring

lemma norm_heatMask_le (r : Three → ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hr : ∀ w j, |r w j| ≤ M) : ‖heatMask r‖ ≤ entryNormConstant (BlockSpace ι) * M := by
  apply norm_matrix_le_entries
  intro a b
  rw [heatMask_eq_diagonal]
  by_cases hab : a = b
  · subst b
    simpa only [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs] using hr a.1 a.2
  · simpa only [Matrix.diagonal_apply_ne _ hab, norm_zero] using hM

omit [DecidableEq ι] in
lemma exists_score_polynomial_bound (u : ι → ℝ) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D →
      ∀ (σ : Three → ℝ), (∀ w, a ≤ σ w) → ∀ w j,
        |score (u j) (chart i d z w) (σ w)| ≤ C * planePoly z ∧
        |score (u j) (chart i d z w) (σ w)^2 - (σ w)⁻¹| ≤ (C^2+a⁻¹) * planePoly z^2 := by
  let U := ∑ j, |u j|
  have hU : 0 ≤ U := Finset.sum_nonneg (fun j _ => abs_nonneg (u j))
  have hu j : |u j| ≤ U := Finset.single_le_sum (fun j _ => abs_nonneg (u j)) (Finset.mem_univ j)
  let C := (U+D+2)/a
  have hC : 0 ≤ C := div_nonneg (by linarith) ha.le
  refine ⟨C,hC,?_⟩
  intro i d z hd σ hσ w j
  have hP := one_le_planePoly z
  have hpn := planePoly_nonneg z
  have hsp : 0 < σ w := ha.trans_le (hσ w)
  have hs : |score (u j) (chart i d z w) (σ w)| ≤ C * planePoly z := by
    calc
      _ ≤ (|u j|+|chart i d z w|)/a := score_le_linear ha (hσ w) _ _
      _ ≤ (U+(D+2)*planePoly z)/a := by gcongr; exacts [hu j, chart_abs_bound hd i w z]
      _ ≤ C * planePoly z := by
        dsimp [C]
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha]
        nlinarith
  have hinv : (σ w)⁻¹ ≤ a⁻¹ := by
    simp only [← one_div]
    exact one_div_le_one_div_of_le ha (hσ w)
  have hs2 : score (u j) (chart i d z w) (σ w)^2 ≤ C^2 * planePoly z^2 := by
    have := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC hpn)).2 hs
    simpa only [sq_abs, mul_pow] using this
  refine ⟨hs,?_⟩
  calc
    _ ≤ score (u j) (chart i d z w) (σ w)^2 + (σ w)⁻¹ := by
      calc
        _ ≤ |score (u j) (chart i d z w) (σ w)^2| + |(σ w)⁻¹| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg (sq_nonneg _), abs_of_pos (inv_pos.mpr hsp)]
    _ ≤ C^2 * planePoly z^2 + a⁻¹ := add_le_add hs2 hinv
    _ ≤ _ := by nlinarith [inv_pos.mpr ha, sq_nonneg (planePoly z-1)]

end
end TriangularHilbert.Heat
end

end OAI
