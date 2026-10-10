import OAI.Geometry.Relativity.CKS.AngularGeometry
import OAI.Geometry.Relativity.CKS.SmoothOuterDEC

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rescale (c : ℝ) (j : Jet) : Jet :=
  (fun i k => c*j.1 i k, (fun s i k => c*j.2.1 s i k), fun s t i k => c*j.2.2 s t i k)

lemma inverse_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (i k : I) :
    inverse (rescale c j).1 i k = inverse j.1 i k / c := by
  have heq : determinant (rescale c j).1 = c^2*determinant j.1 := by
    dsimp [rescale,determinant]
    ring
  simp only [inverse,heq]
  fin_cases i <;> fin_cases k <;> dsimp [rescale] <;> field_simp

lemma christoffel_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (a i k : I) :
    christoffel (rescale c j) a i k = christoffel j a i k := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [inverse_rescale c j hc]
  dsimp [rescale]
  field_simp

lemma inverseDerivative_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (s a b : I) :
    inverseDerivative (rescale c j) s a b = inverseDerivative j s a b / c := by
  unfold inverseDerivative
  simp only [Finset.sum_div,neg_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [inverse_rescale c j hc,inverse_rescale c j hc]
  dsimp [rescale]
  field_simp

lemma christoffelDerivative_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (s a i k : I) :
    christoffelDerivative (rescale c j) s a i k = christoffelDerivative j s a i k := by
  unfold christoffelDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [inverseDerivative_rescale c j hc,inverse_rescale c j hc]
  dsimp [rescale]
  field_simp

lemma ricci_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (i k : I) :
    ricci (rescale c j) i k = ricci j i k := by
  simp only [ricci,christoffelDerivative_rescale c j hc,christoffel_rescale c j hc]

lemma scalar_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) :
    scalarCurvature (rescale c j) = scalarCurvature j / c := by
  simp only [scalarCurvature,inverse_rescale c j hc,ricci_rescale c j hc,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma lapse_rescale (c : ℝ) (j : Jet) (z : ScalarJet) (hc : c ≠ 0) :
    lapseLaplacian (rescale c j) z = lapseLaplacian j z / c := by
  simp only [lapseLaplacian,inverse_rescale c j hc,christoffel_rescale c j hc,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem weighted_curvature_lapse {K : Set CombinedJet} (hK : IsCompact K)
    (hreg : K ⊆ regular) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ j j₀ : CombinedJet, j ∈ Metric.cthickening δ K → j₀ ∈ Metric.cthickening δ K →
      ∀ r w A : ℝ, 0 < r → 0 ≤ w → 0 ≤ A → ‖j-j₀‖ ≤ A*w/r^3 →
      |scalarCurvature (rescale (r^2) j.1)-scalarCurvature (rescale (r^2) j₀.1)| ≤ C*A*w/r^5 ∧
      |lapseLaplacian (rescale (r^2) j.1) j.2-lapseLaplacian (rescale (r^2) j₀.1) j₀.2| ≤ C*A*w/r^5 := by
  obtain ⟨δ,hδ,C,hC⟩ := operators_uniform_lipschitz hK hreg
  refine ⟨δ,hδ,C,C.coe_nonneg,?_⟩
  intro j j₀ hj hj₀ r w A hr hw hA hbound
  have hop : ‖operators j-operators j₀‖ ≤ (C:ℝ)*(A*w/r^3) := by
    have hh := hC.dist_le_mul j hj j₀ hj₀
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hbound C.coe_nonneg)
  have hfirst : |scalarCurvature j.1-scalarCurvature j₀.1| ≤ (C:ℝ)*(A*w/r^3) :=
    calc
      _ ≤ ‖operators j-operators j₀‖ := by
        exact norm_fst_le (operators j-operators j₀)
      _ ≤ _ := hop
  have hsecond : |lapseLaplacian j.1 j.2-lapseLaplacian j₀.1 j₀.2| ≤ (C:ℝ)*(A*w/r^3) :=
    calc
      _ ≤ ‖operators j-operators j₀‖ := by
        exact norm_snd_le (operators j-operators j₀)
      _ ≤ _ := hop
  have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr.ne'
  rw [scalar_rescale _ _ hr2,scalar_rescale _ _ hr2,lapse_rescale _ _ _ hr2,lapse_rescale _ _ _ hr2]
  constructor
  · rw [← sub_div,abs_div,abs_of_pos (sq_pos_of_pos hr)]
    exact (div_le_div_of_nonneg_right hfirst (sq_nonneg r)).trans_eq (by field_simp)
  · rw [← sub_div,abs_div,abs_of_pos (sq_pos_of_pos hr)]
    exact (div_le_div_of_nonneg_right hsecond (sq_nonneg r)).trans_eq (by field_simp)

end
end CKSAngularGeometry

end

end OAI
