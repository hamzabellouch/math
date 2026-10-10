import OAI.Analysis.TriangularHilbert.GaussianMax

namespace OAI

section
namespace TriangularHilbert.Heat
open scoped BigOperators
noncomputable section

lemma density_radial_int (σ h : ℝ) (m : ℤ) :
    density σ (h*(m:ℝ)) = density σ (h*(m.natAbs:ℝ)) := by
  have he := congrArg (fun n : ℤ => (n : ℝ)) (Int.natAbs_sq m).symm
  simp only [Int.cast_pow,Int.cast_natCast] at he
  simp only [density,mul_pow,he]

lemma density_radial_descending {σ h : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) (r : ℕ) :
    h*density σ (h*(r+1:ℕ)) ≤ h*density σ (h*(r:ℝ)) := by
  apply mul_le_mul_of_nonneg_left _ hh
  unfold density
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hr : (0:ℝ) ≤ r := by positivity
  push_cast
  nlinarith [sq_nonneg h]

lemma intInterval_density_mass {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) (N : ℕ) :
    (∑ m ∈ intInterval n N, h*density σ (h*((m-n).natAbs:ℝ))) ≤ meshMassConstant := by
  simp_rw [← density_radial_int]
  rw [intInterval_sum_fin]
  have he (i : Fin (2*N+1)) : h*density σ (h*((n-(N:ℤ)+(i:ℕ)-n:ℤ):ℝ)) =
      h*density σ (-(h*N)+h*i) := by
    congr 2
    push_cast
    ring
  simp_rw [he]
  exact mesh_mass_le hh hσ (-(h*N)) (2*N+1)

lemma gaussian_sum_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m ∈ D, f m*(h*density σ (h*((m-n:ℤ):ℝ)))) ≤ meshMassConstant * intMax D f n := by
  have hpos : 0 < σ := (sq_pos_of_pos hh).trans_le hσ
  simp_rw [density_radial_int]
  have hw := intInterval_weighted_le D f hf n (fun r => h*density σ (h*(r:ℝ)))
    (fun r => mul_nonneg hh.le (density_nonneg hpos.le _)) (density_radial_descending hpos hh.le)
  apply hw.trans
  rw [mul_comm meshMassConstant]
  exact mul_le_mul_of_nonneg_left (intInterval_density_mass hh hσ n (supportRadius D n)) (intMax_nonneg D f hf n)
end
end TriangularHilbert.Heat
end

end OAI
