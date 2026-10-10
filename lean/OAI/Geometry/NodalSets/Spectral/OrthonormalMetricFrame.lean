import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import OAI.Geometry.NodalSets.Charts.PositiveMetric

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem positive_metric_orthonormal_basis (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E,
      ∀ i j, g (b i) (b j) = if i = j then 1 else 0 := by
  let G : LinearMap.BilinForm ℝ E :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).symm.toLinearMap.comp
      g.toLinearMap
  have hG : G.IsSymm := ⟨hs⟩
  let : Invertible (2:ℝ) := invertibleOfNonzero (by norm_num)
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hG
  have hpos (i) : 0 < g (b i) (b i) := hp (b i) (b.ne_zero i)
  let w : Fin (Module.finrank ℝ E) → ℝˣ := fun i ↦
    Units.mk0 (Real.sqrt (g (b i) (b i)))⁻¹ (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (hpos i))))
  refine ⟨b.unitsSMul w, ?_⟩
  intro i j
  simp only [Module.Basis.unitsSMul_apply, Units.smul_def, map_smul,
    smul_apply, smul_eq_mul]
  change (Real.sqrt (g (b j) (b j)))⁻¹ *
    ((Real.sqrt (g (b i) (b i)))⁻¹ * g (b i) (b j)) = _
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have hr : Real.sqrt (g (b i) (b i)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hpos i))
    have hh := Real.sq_sqrt (hpos i).le
    field_simp
    nlinarith
  · rw [ite_eq_right hij]
    have hz : g (b i) (b j) = 0 := hb hij
    rw [hz]
    ring

end
end Yau.Geometry

end OAI
