import OAI.Geometry.NodalSets.Elliptic.CompactFluxGreen

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_compact_test_derivative {n : ℕ} (u phi : Coord n → ℝ)
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (i : Fin n) (K : Set (Coord n)) (hK : tsupport phi ⊆ K) :
    Integrable (fun x ↦ coordPartial u x i*phi x) ∧
    Integrable (fun x ↦ u x*coordPartial phi x i) ∧
    (∫ x in K, coordPartial u x i*phi x) = -(∫ x in K, u x*coordPartial phi x i) := by
  have h1 : Integrable (fun x ↦ coordPartial u x i*phi x) :=
    ((real_coordPartial_smooth u hu i).continuous.mul hp.continuous).integrable_of_hasCompactSupport hc.mul_left
  have h2 : Integrable (fun x ↦ u x*coordPartial phi x i) :=
    (hu.continuous.mul (real_coordPartial_smooth phi hp i).continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (Pi.single i 1)).mul_left
  have h3 : Integrable (fun x ↦ phi x*u x) :=
    (hp.continuous.mul hu.continuous).integrable_of_hasCompactSupport hc.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := phi) (g := u) (v := Pi.single i 1)
    (by simpa only [coordPartial,mul_comm] using h2)
    (by simpa only [coordPartial,mul_comm] using h1) h3
    (fun x _ ↦ hp.differentiable (by simp) x) (fun x _ ↦ hu.differentiable (by simp) x)
  have hz1 : ∀ x, x ∉ K → coordPartial u x i*phi x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hK h)),mul_zero]
  have hz2 : ∀ x, x ∉ K → u x*coordPartial phi x i = 0 := by
    intro x hx
    unfold coordPartial
    rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hK h))]
    simp
  refine ⟨h1,h2,?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz2]
  simpa only [coordPartial,mul_comm] using h

end
end Yau

end OAI
