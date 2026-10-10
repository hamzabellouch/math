import OAI.Analysis.TriangularHilbert.FiniteLineMax

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

def jumpMax (D : Finset ℤ) (A : Three → Matrix D D ℂ) (i j : D) : ℝ :=
  2*lineMax D (fun m => ‖A 0 i m‖^2) j+
  2*lineMax D (fun m => ‖A 0 m j‖^2) i+
  lineMax D (fun m => ‖A 2 m i‖^2) (-(i:ℤ)-(j:ℤ))+
  lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ))

lemma jumpMax_nonneg (D : Finset ℤ) (A : Three → Matrix D D ℂ) (i j : D) :
    0 ≤ jumpMax D A i j := by
  unfold jumpMax
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (by norm_num) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _))
    (mul_nonneg (by norm_num) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)))
    (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)

lemma gaussian_sum_back_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m : D, f m*(h*density σ (h*n-h*(m:ℤ)))) ≤ meshMassConstant*lineMax D f n := by
  have he (m : D) : density σ (h*n-h*(m:ℤ)) = density σ (h*((m-n:ℤ):ℝ)) := by
    rw [show h*n-h*(m:ℤ) = -(h*((m-n:ℤ):ℝ)) by push_cast; ring,density_neg]
  simp_rw [he]
  exact gaussian_sum_le_lineMax D f hf hh hσ n

lemma gaussian_sum_triangle_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (i j : ℤ) :
    (∑ m : D, f m*(h*density σ (h*i+h*j+h*(m:ℤ)))) ≤ meshMassConstant*lineMax D f (-i-j) := by
  have he (m : D) : h*i+h*j+h*(m:ℤ) = h*((m-(-i-j):ℤ):ℝ) := by push_cast; ring
  simp_rw [he]
  exact gaussian_sum_le_lineMax D f hf hh hσ (-i-j)

lemma jumpExpectation_le_jumpMax (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    {h : ℝ} (hh : 0 < h) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) (i j : D) :
    jumpExpectation A h (fun m => h*(m:ℤ)) σ i j ≤ meshMassConstant*jumpMax D A i j := by
  have htwo (v : Three) : h^2 ≤ 2*σ v := by nlinarith [hσ v,sq_nonneg h]
  have hsum : h^2 ≤ σ 0+σ 1+σ 2 := by nlinarith [hσ 0,hσ 1,hσ 2,sq_nonneg h]
  have hX := gaussian_sum_back_le_lineMax D (fun m => ‖A 0 i m‖^2) (fun _ => sq_nonneg _) hh (htwo 1) j
  have hY := gaussian_sum_back_le_lineMax D (fun m => ‖A 0 m j‖^2) (fun _ => sq_nonneg _) hh (htwo 0) i
  have hH := gaussian_sum_triangle_le_lineMax D (fun m => ‖A 2 m i‖^2) (fun _ => sq_nonneg _) hh hsum i j
  have hK := gaussian_sum_triangle_le_lineMax D (fun m => ‖A 1 j m‖^2) (fun _ => sq_nonneg _) hh hsum i j
  unfold jumpExpectation jumpMax
  linarith

lemma finite_mesh_energy_jump_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (B C : Matrix D D ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) :
    |totalPlaneEnergy (replaceZero A B) h (fun m => h*(m:ℤ)) 0 σ-
      totalPlaneEnergy (replaceZero A C) h (fun m => h*(m:ℤ)) 0 σ| ≤
      3/2*meshMassConstant*h^2*∑ i, ∑ j, ‖B i j-C i j‖*jumpMax D A i j := by
  have hj := totalPlaneEnergy_replaceZero_jump A B C hB hC hh (fun m => h*(m:ℤ))
    (fun v => (sq_pos_of_pos hh).trans_le (hσ v))
  apply hj.trans
  calc
    _ ≤ 3/2*h^2*∑ i, ∑ j, ‖B i j-C i j‖*(meshMassConstant*jumpMax D A i j) := by
      gcongr with i j
      exact jumpExpectation_le_jumpMax D A hh hσ i j
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
end
end TriangularHilbert.Heat
end

end OAI
