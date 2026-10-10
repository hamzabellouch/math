import OAI.Geometry.Perimeter.Regularity.EllipticLocality

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack

section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem gradient_comp_isometry (e : V ≃ₗᵢ[ℝ] W) (f : W → ℝ) (x : V) :
    gradient (f ∘ e) x=e.symm (gradient f (e x)) := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left]
  have he : inner ℝ (e.symm (gradient f (e x))) y=inner ℝ (gradient f (e x)) (e y) := by
    rw [←e.inner_map_map,e.apply_symm_apply]
  rw [he,inner_gradient_left]
  have hd := e.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := x)
  exact congrArg (fun L : V →L[ℝ] ℝ ↦ L y) hd

omit [CompleteSpace V] [CompleteSpace W] in
theorem GeometricHolderAt.precomp_isometry [CompleteSpace V] [CompleteSpace W]
    {X : Type*} [PseudoMetricSpace X]
    {θ : ℝ} {f : W → X} {p : V} (e : V ≃ₗᵢ[ℝ] W)
    (h : GeometricHolderAt θ f (e p)) : GeometricHolderAt θ (f ∘ e) p := by
  obtain ⟨r,C,hr,hC,hh⟩ := h
  refine ⟨r,C,hr,hC,fun j x hx y hy hxy ↦ hh j (e x) ?_ (e y) ?_ ?_⟩
  · simpa only [Metric.mem_ball,e.dist_map] using hx
  · simpa only [Metric.mem_ball,e.dist_map] using hy
  · simpa only [e.dist_map] using hxy

end

section Transfer
variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

theorem minimal_equation_isometry (e : Euc m ≃ₗᵢ[ℝ] W) {f : W → ℝ} {U : Set W}
    (h : ∀ ψ : W → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y, inner ℝ (gradient f y) (gradient ψ y)/Real.sqrt (1+‖gradient f y‖^2))=0)
    (φ : SmoothLocalTest (e ⁻¹' U)) :
    (∫ x, inner ℝ (gradient (f ∘ e) x) (gradient φ.val x)/
      Real.sqrt (1+‖gradient (f ∘ e) x‖^2))=0 := by
  let ψ : W → ℝ := φ.val ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := φ.property.1.comp e.symm.contDiff
  have hcψ : HasCompactSupport ψ := φ.property.2.1.comp_homeomorph e.symm.toHomeomorph
  have hsψ : tsupport ψ ⊆ U := by
    intro y hy
    have hh := φ.property.2.2 (tsupport_comp_subset_preimage φ.val e.symm.continuous hy)
    simpa only [mem_preimage,e.apply_symm_apply] using hh
  have hh := h ψ hψ hcψ hsψ
  have hi := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y ↦ inner ℝ (gradient f y) (gradient ψ y)/Real.sqrt (1+‖gradient f y‖^2))
  rw [←hi] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [gradient_comp_isometry,e.symm.norm_map]
  have heg : gradient ψ (e x)=e (gradient φ.val x) := by
    dsimp [ψ]
    rw [gradient_comp_isometry,e.symm_apply_apply]
    rfl
  rw [heg]
  congr 1
  rw [←e.inner_map_map,e.apply_symm_apply]

end Transfer
end RPISingularHarnack

end

end OAI
