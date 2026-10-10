import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedOrbitalGram
import Mathlib.Analysis.Matrix.Order

namespace OAI

/-! Quantitative symmetric orthonormalization of a finite real Gram matrix.
The correction is the actual spectral inverse square root, with Euclidean
operator norm estimates independent of the ambient function space. -/

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb.GramCorrection

lemma inverseSqrt_bounds {a x : ℝ} (_ha : 0 ≤ a) (has : a ≤ 1 / 2)
    (hx : 1 - a ≤ x ∧ x ≤ 1 + a) :
    (Real.sqrt x)⁻¹ ≤ 2 ∧ |(Real.sqrt x)⁻¹ - 1| ≤ 2 * a := by
  have hxp : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hsq := Real.sq_sqrt hxp.le
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  have hinv : (Real.sqrt x)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hs).mpr
    linarith
  refine ⟨hinv, ?_⟩
  have hid : ((Real.sqrt x)⁻¹ - 1) *
      (Real.sqrt x * (Real.sqrt x + 1)) = 1 - x := by
    calc
      _ = ((Real.sqrt x)⁻¹ * Real.sqrt x - Real.sqrt x) * (Real.sqrt x + 1) := by ring
      _ = (1 - Real.sqrt x) * (Real.sqrt x + 1) := by rw [inv_mul_cancel₀ hs.ne']
      _ = 1 - x := by nlinarith
  have hden : (1 / 2 : ℝ) ≤ Real.sqrt x * (Real.sqrt x + 1) := by
    nlinarith
  have habs : |1 - x| ≤ a := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hm : |(Real.sqrt x)⁻¹ - 1| * (Real.sqrt x * (Real.sqrt x + 1)) ≤ a := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt x * (Real.sqrt x + 1)), ← abs_mul, hid]
    exact habs
  nlinarith [mul_nonneg (abs_nonneg ((Real.sqrt x)⁻¹ - 1)) (sub_nonneg.mpr hden)]

variable {m : ℕ} {G : Matrix (Fin m) (Fin m) ℝ}

lemma eigenvalue_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta) (i : Fin m) :
    1 - m * delta ≤ hG.eigenvalues i ∧ hG.eigenvalues i ≤ 1 + m * delta := by
  let v : Fin m → ℝ := hG.eigenvectorBasis i
  have hnorm : ∑ j, v j ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) (hG.eigenvectorBasis.orthonormal.1 i)
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, one_pow] using h
  have hval : hG.eigenvalues i = ∑ j, ∑ k, G j k * v j * v k := by
    rw [hG.eigenvalues_eq]
    simp only [RCLike.re_to_real, star_trivial, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [v]
    ring
  rw [hval]
  have hlo := dualMatrix_quadratic_lower G hdelta (fun j => (hdiag j).ge) hoff v
  have hhi := dualMatrix_quadratic_upper G hdelta (fun j => (hdiag j).le) hoff v
  rw [hnorm, mul_one] at hlo hhi
  exact ⟨hlo, hhi⟩

def correction (hG : G.IsHermitian) : Matrix (Fin m) (Fin m) ℝ :=
  hG.cfc (fun x => (Real.sqrt x)⁻¹)

lemma correction_isHermitian (hG : G.IsHermitian) : (correction hG).IsHermitian := by
  rw [correction, ← hG.cfc_eq]
  exact (IsSelfAdjoint.cfc : IsSelfAdjoint (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G))

lemma correction_transpose (hG : G.IsHermitian) : (correction hG)ᵀ = correction hG := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    correction_isHermitian hG

lemma correction_gram (hG : G.IsHermitian) (hpos : ∀ i, 0 < hG.eigenvalues i) :
    (correction hG)ᵀ * G * correction hG = 1 := by
  rw [correction_transpose]
  conv_lhs => arg 1; arg 2; rw [hG.spectral_theorem]
  unfold correction Matrix.IsHermitian.cfc
  rw [← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hdiag : Matrix.diagonal (fun i =>
      (Real.sqrt (hG.eigenvalues i))⁻¹ * hG.eigenvalues i *
        (Real.sqrt (hG.eigenvalues i))⁻¹) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    have hscalar (i : Fin m) : (Real.sqrt (hG.eigenvalues i))⁻¹ * hG.eigenvalues i *
        (Real.sqrt (hG.eigenvalues i))⁻¹ = 1 := by
      have hs : Real.sqrt (hG.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
      calc
        _ = (Real.sqrt (hG.eigenvalues i))⁻¹ * Real.sqrt (hG.eigenvalues i) ^ 2 *
            (Real.sqrt (hG.eigenvalues i))⁻¹ := by rw [Real.sq_sqrt (hpos i).le]
        _ = 1 := by field_simp
    simp only [hscalar, Matrix.diagonal_one]
  simpa only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq] using
    congrArg (Unitary.conjStarAlgAut ℝ _ hG.eigenvectorUnitary) hdiag |>.trans (map_one _)

lemma correction_norm_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) :
    ‖correction hG‖ ≤ 2 ∧ ‖correction hG - 1‖ ≤ 2 * m * delta := by
  have ha : 0 ≤ (m : ℝ) * delta := mul_nonneg (Nat.cast_nonneg _) hdelta
  have hb (i : Fin m) := inverseSqrt_bounds ha hsmall (eigenvalue_bounds hG hdelta hdiag hoff i)
  have hnorm : ‖correction hG‖ ≤ 2 := by
    rw [correction, ← hG.cfc_eq]
    apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 2)
    intro x hx
    rw [hG.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact (hb i).1
  refine ⟨hnorm, ?_⟩
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ G) :=
    G.finite_real_spectrum.continuousOn _
  rw [correction, ← hG.cfc_eq, ← cfc_const_one ℝ G, ← cfc_sub _ _ G hc continuousOn_const]
  apply norm_cfc_le (by positivity : (0 : ℝ) ≤ 2 * m * delta)
  intro x hx
  rw [hG.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  simpa only [Real.norm_eq_abs, mul_assoc] using (hb i).2

lemma entry_abs_le_norm (B : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) : |B i j| ≤ ‖B‖ := by
  let v : EuclideanSpace ℝ (Fin m) := PiLp.single 2 j 1
  let y : EuclideanSpace ℝ (Fin m) := Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B v
  have hy : y i = B i j := by
    change (B *ᵥ Pi.single j (1 : ℝ)) i = B i j
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    |B i j| = ‖y i‖ := by rw [hy, Real.norm_eq_abs]
    _ ≤ ‖y‖ := PiLp.norm_apply_le y i
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B‖ * ‖v‖ := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B).le_opNorm v
    _ = ‖B‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]; simp only [v, PiLp.norm_single, norm_one, mul_one]

lemma correction_entry_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) (i j : Fin m) :
    |correction hG i j - if i = j then 1 else 0| ≤ 2 * m * delta ∧
      |correction hG i j| ≤ 2 := by
  have hb := correction_norm_bounds hG hdelta hdiag hoff hsmall
  constructor
  · simpa only [Matrix.sub_apply, Matrix.one_apply] using
      (entry_abs_le_norm (correction hG - 1) i j).trans hb.2
  · exact (entry_abs_le_norm (correction hG) i j).trans hb.1

/-- The actual symmetric correction orthonormalizes the given Gram matrix,
changes coefficients by at most twice its overlap row bound, and has
Euclidean operator norm at most two. -/
theorem exists_symmetric_correction (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) :
    ∃ A : Matrix (Fin m) (Fin m) ℝ,
      Aᵀ = A ∧ Aᵀ * G * A = 1 ∧ ‖A - 1‖ ≤ 2 * m * delta ∧ ‖A‖ ≤ 2 := by
  have hpos (i : Fin m) : 0 < hG.eigenvalues i := by
    have hi := (eigenvalue_bounds hG hdelta hdiag hoff i).1
    linarith
  exact ⟨correction hG, correction_transpose hG, correction_gram hG hpos,
    (correction_norm_bounds hG hdelta hdiag hoff hsmall).2,
    (correction_norm_bounds hG hdelta hdiag hoff hsmall).1⟩

end ContinuumCoulomb.GramCorrection

end

end OAI
