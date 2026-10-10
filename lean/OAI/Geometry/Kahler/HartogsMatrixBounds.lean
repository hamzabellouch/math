import OAI.Geometry.Kahler.HartogsModelBridge

namespace OAI

universe uKahler7661_1

open scoped ContDiff
open Complex
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix Unitary

lemma positive_horizontalMetric {c lam x : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hx : 0 ≤ x)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hl : ∀ w, c * euclidean.q w ≤ (form A hA).q w) :
    (horizontalMetric A lam x).PosDef := by
  apply (form_pos_iff _ (horizontalMetric_hermitian A hA lam x)).mp
  intro u hu
  have hp := form_one_pos u hu
  have hAu : 0 ≤ (form A hA).q u := (mul_nonneg hc.le hp.le).trans (hl u)
  simp only [horizontalMetric, form, HForm.q, add_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change 0 < lam * euclidean.q u + x * (form A hA).q u
  exact add_pos_of_pos_of_nonneg (mul_pos hlam hp) (mul_nonneg hx hAu)

lemma hermitian_entry_bound {C : ℝ} (hC : 0 ≤ C) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (hn : (form A hA).Nonneg)
    (hu : ∀ w, (form A hA).q w ≤ C * euclidean.q w) (i j : Fin 2) : ‖A i j‖ ≤ C := by
  let u : Fin 2 → ℂ := Pi.single i 1
  let v : Fin 2 → ℂ := Pi.single j 1
  have huq : euclidean.q u = 1 := by fin_cases i <;> simp [u, form, HForm.q, dotProduct, Matrix.mulVec]
  have hvq : euclidean.q v = 1 := by fin_cases j <;> simp [v, form, HForm.q, dotProduct, Matrix.mulVec]
  have huv : form A hA u v = A i j := by
    fin_cases i <;> fin_cases j <;> simp [form, dotProduct, Matrix.mulVec, u, v]
  have hi := hu u
  have hj := hu v
  rw [huq, mul_one] at hi
  rw [hvq, mul_one] at hj
  have hm := mul_le_mul hi hj (hn v) hC
  have hg := (form A hA).gram u v hn
  have hnorm : ‖A i j‖^2 ≤ C^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [HForm.imag, HForm.area, huv] at hg
    nlinarith only [hg, hm]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mp hnorm

lemma conjugate_real_smul {n : Type uKahler7661_1} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) (r : ℝ) :
    conjStarAlgAut ℂ _ U (r • A) = r • conjStarAlgAut ℂ _ U A := by
  simp [conjStarAlgAut_apply]

lemma horizontal_inverse_spectral (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) {lam x : ℝ}
    (hden : ∀ i, lam + x * hA.eigenvalues i ≠ 0) :
    (horizontalMetric A lam x)⁻¹ = conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i ↦ (((lam + x * hA.eigenvalues i)⁻¹ : ℝ) : ℂ))) := by
  let U := hA.eigenvectorUnitary
  let F := conjStarAlgAut ℂ _ U
  let d := hA.eigenvalues
  have hAe : A = F (diagonal (fun i ↦ (d i : ℂ))) := hA.spectral_theorem
  have hdiag : (diagonal (fun i ↦ ((lam + x * d i : ℝ) : ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      lam • 1 + x • diagonal (fun i ↦ (d i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hG : horizontalMetric A lam x = F (diagonal (fun i ↦ ((lam + x * d i : ℝ) : ℂ))) := by
    rw [hdiag, map_add, conjugate_real_smul, conjugate_real_smul, map_one, ← hAe]
    rfl
  apply Matrix.inv_eq_right_inv
  change horizontalMetric A lam x * F (diagonal (fun i ↦ (((lam + x * d i)⁻¹ : ℝ) : ℂ))) = 1
  rw [hG, ← map_mul]
  have Hi : (diagonal (fun i ↦ ((lam + x * d i : ℝ) : ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
      diagonal (fun i ↦ (((lam + x * d i)⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq, one_apply_eq, ← Complex.ofReal_mul]
      rw [mul_inv_cancel₀ (hden i)]
      rfl
    · simp [hij]
  rw [Hi, map_one]

lemma horizontal_inverse_bound {c C lam x : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hx : 0 ≤ x)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hl : ∀ w, c * euclidean.q w ≤ (form A hA).q w)
    (hu : ∀ w, (form A hA).q w ≤ C * euclidean.q w) (i j : Fin 2) :
    ‖(horizontalMetric A lam x)⁻¹ i j‖ ≤ (lam + x*c)⁻¹ := by
  have hd := spectral_interval A hA hl hu
  have hld : 0 < lam + x*c := add_pos_of_pos_of_nonneg hlam (mul_nonneg hx hc.le)
  have hp (i : Fin 2) : 0 < lam + x*hA.eigenvalues i :=
    lt_of_lt_of_le hld (by linarith [mul_le_mul_of_nonneg_left (hd i).1 hx])
  have hGi := (horizontalMetric_hermitian A hA lam x).inv
  have hB : (((lam+x*c)⁻¹ : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by rfl)
  have hBe : ((lam+x*c)⁻¹ : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      conjStarAlgAut ℂ _ hA.eigenvectorUnitary (diagonal (fun _ : Fin 2 ↦ (((lam+x*c)⁻¹ : ℝ) : ℂ))) := by
    have he : (diagonal (fun _ : Fin 2 ↦ (((lam+x*c)⁻¹ : ℝ) : ℂ))) =
        ((lam+x*c)⁻¹ : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [he, conjugate_real_smul, map_one]
  have hcomp := spectral_comparison hA.eigenvectorUnitary
    (fun i => (lam + x*hA.eigenvalues i)⁻¹) (fun _ => (lam+x*c)⁻¹)
    _ _ hGi hB (horizontal_inverse_spectral A hA (fun i => (hp i).ne')) hBe
    (fun i => inv_anti₀ hld (by linarith [mul_le_mul_of_nonneg_left (hd i).1 hx]))
  apply hermitian_entry_bound (inv_nonneg.mpr hld.le) _ hGi
  · exact (form_nonneg_iff _ hGi).mpr (positive_horizontalMetric hc hlam hx A hA hl).inv.posSemidef
  · intro w
    have hw := hcomp w
    simpa only [form, HForm.q, smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul] using hw

end PinchedHartogs

end

end OAI
