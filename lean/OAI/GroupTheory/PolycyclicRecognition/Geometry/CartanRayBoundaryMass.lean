import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryFamilyMass

namespace OAI

/-! # Common boundary windows for the actual Cartan quotient actions -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

variable {EG G P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {M : CartanWordModel H}
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} {F : CartanFactorModel H ExpG}
  {αS αT : H →ₗ[ℝ] ℝ} (RS : M.RayBoundaryModel F αS) (RT : M.RayBoundaryModel F αT)

/-- The common shadow bounds produce a compact source window with nonempty
interior and both of the uniform inequalities used in the leaf/trace proof. -/
theorem RayBoundaryModel.exists_mass_and_equal_set_trace
    (B : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier) (f g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier)
    (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z)
    (hC : ∀ p x, ∃ z ∈ KS, (B p).symm (RT.action x 1) = RS.action (g p x) z)
    (μ : Measure RT.cone.Q.carrier) [μ.IsHaarMeasure] (height : G → ℝ)
    (hvolume : ∀ x V, μ (RT.action x '' V) =
      ENNReal.ofReal (Real.exp (height x)) * μ V) :
    ∃ (U : PositiveCompacts RS.cone.Q.carrier) (K D : ℝ), 0 < K ∧ 0 ≤ D ∧
      (∀ p x, ENNReal.ofReal (Real.exp (height (f p x))) ≤
          ENNReal.ofReal K * μ (B p '' (RS.action x '' (U : Set RS.cone.Q.carrier))) ∧
        μ (B p '' (RS.action x '' (U : Set RS.cone.Q.carrier))) ≤
          ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x)))) ∧
      ∀ p x y, RS.action x '' (U : Set RS.cone.Q.carrier) = RS.action y '' (U : Set RS.cone.Q.carrier) →
        |height (f p x) - height (f p y)| ≤ D := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let : IsTopologicalGroup RT.cone.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, RT.cone.Q.modelSpace)) ⊤
  let : LocallyCompactSpace RT.cone.Q.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, RT.cone.Q.modelSpace))
  let : LocallyCompactSpace RS.cone.Q.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, RS.cone.Q.modelSpace))
  let U₀ : PositiveCompacts RS.cone.Q.carrier := Classical.choice inferInstance
  obtain ⟨U, K, D, hU, hU₀U, hK, hD, hmass, htrace⟩ :=
    boundary_family_mass_and_trace_of_compact_shadows RS.action RT.action
      RS.orbit_isQuotientMap.continuous RT.orbit_isQuotientMap.continuous
      (fun p => B p) (fun p => (B p).symm) f g hLf hLg hf hg hinv
      (fun p => (B p).apply_symm_apply)
      RS.sectionMap RS.continuous_sectionMap RS.section_rightInverse
      RT.sectionMap RT.continuous_sectionMap RT.section_rightInverse
      KS KT hKS hKT hB hC μ height hvolume U₀ U₀.isCompact
  let V : PositiveCompacts RS.cone.Q.carrier :=
    ⟨⟨U, hU⟩, U₀.interior_nonempty.mono (interior_mono hU₀U)⟩
  exact ⟨V, K, D, hK, hD, hmass, htrace⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
