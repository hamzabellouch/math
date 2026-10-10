import OAI.Geometry.RCD.Coordinates.BilinearDiagonalBound

namespace OAI

/-! # A common null set for all mixed directions of finite quadratic forms -/

open Set Filter MeasureTheory TopologicalSpace

noncomputable section
namespace RegularPointCoordinates

variable {m : ℕ}

theorem bilinear_coordinates (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ) :
    coordinateBilinear (fun i j => B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))=B := by
  apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
  intro i
  apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
  intro j
  simp [coordinateBilinear,EuclideanSpace.basisFun_apply]

theorem bilinear_diagonal_continuous (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ) :
    Continuous (fun a => B a a) := by
  rw [← bilinear_coordinates B]
  simp only [coordinateBilinear_apply,smul_eq_mul]
  fun_prop

/-- Bounds established separately in each real direction yield one
null set outside which every mixed-direction bound holds. -/
theorem ae_bilinear_mixed_bound_of_diagonal {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (P H : X → Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ) (b : X → ℝ)
    (hP : ∀ x a c, P x a c=P x c a) (hH : ∀ x a c, H x a c=H x c a)
    (hpos : ∀ a, ∀ᵐ x ∂μ, 0≤P x a a) (hb : ∀ᵐ x ∂μ, 0≤b x)
    (hdiag : ∀ a, ∀ᵐ x ∂μ, (H x a a)^2≤b x*(P x a a)^2) :
    ∀ᵐ x ∂μ, ∀ a c, (H x a c)^2≤b x*P x a a*P x c c := by
  obtain ⟨D,hD,hdense⟩ := exists_countable_dense (Euclidean m)
  let : Countable D := hD.to_subtype
  filter_upwards [hb,ae_all_iff.mpr (fun a : D => (hpos a).and (hdiag a))] with x hb hx
  have hPc := bilinear_diagonal_continuous (P x)
  have hHc := bilinear_diagonal_continuous (H x)
  have hc : IsClosed {a : Euclidean m | 0≤P x a a ∧ (H x a a)^2≤b x*(P x a a)^2} :=
    (isClosed_le continuous_const hPc).inter
      (isClosed_le (hHc.pow 2) (continuous_const.mul (hPc.pow 2)))
  have hsub : D ⊆ {a : Euclidean m | 0≤P x a a ∧ (H x a a)^2≤b x*(P x a a)^2} :=
    fun a ha => hx ⟨a,ha⟩
  have hall := closure_minimal hsub hc
  rw [hdense.closure_eq] at hall
  intro a c
  exact bilinear_mixed_sq_bound_of_diagonal (P x) (H x) (hP x)
    (fun z => (hall (mem_univ z)).1) (hH x) (b x) hb
    (fun z => (hall (mem_univ z)).2) a c

end RegularPointCoordinates

end

end OAI
