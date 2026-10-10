import Mathlib

namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

theorem exists_auerbach_basis {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : Module.Basis ι ℝ E) :
    ∃ b : Module.Basis ι ℝ E, (∀ i, ‖b i‖ ≤ 1) ∧
      ∀ x i, |b.repr x i| ≤ ‖x‖ := by
  classical
  let U : Set (ι → E) := {v | ∀ i, ‖v i‖ ≤ 1}
  have hcompact : IsCompact U := by
    simpa only [U, Metric.mem_closedBall, dist_zero_right] using
      (isCompact_pi_infinite fun _ : ι => isCompact_closedBall (0 : E) 1)
  let en : Module.Basis ι ℝ E := e.unitsSMul fun i =>
    Units.mk0 (‖e i‖⁻¹) (inv_ne_zero (norm_ne_zero_iff.mpr (e.ne_zero i)))
  have hen : (en : ι → E) ∈ U := by
    intro i
    dsimp only [en]
    rw [Module.Basis.unitsSMul_apply]
    change ‖(‖e i‖ : ℝ)⁻¹ • e i‖ ≤ 1
    exact (norm_smul_inv_norm (𝕜 := ℝ) (e.ne_zero i)).le
  have hcont : Continuous fun v : ι → E => |e.det v| := by
    apply Continuous.abs
    change Continuous fun v : ι → E => Matrix.det (e.toMatrix v)
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i j
    exact (e.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
  obtain ⟨v, hv, hmax⟩ := hcompact.exists_isMaxOn ⟨en, hen⟩ hcont.continuousOn
  have hdet : e.det v ≠ 0 := by
    have hne : e.det en ≠ 0 := isUnit_iff_ne_zero.mp (e.isUnit_det en)
    have h := hmax hen
    exact abs_pos.mp (lt_of_lt_of_le (abs_pos.mpr hne) h)
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  let b : Module.Basis ι ℝ E := Module.Basis.mk hli hsp.ge
  refine ⟨b, ?_, ?_⟩
  · intro i
    simpa only [b, Module.Basis.mk_apply] using hv i
  · have hunit : ∀ x : E, ‖x‖ ≤ 1 → ∀ i, |b.repr x i| ≤ 1 := by
      intro x hx i
      have hu : Function.update v i x ∈ U := by
        intro j
        by_cases hj : j = i
        · subst j; simpa using hx
        · simpa [Function.update_of_ne hj] using hv j
      have hbound : |e.det (Function.update v i x)| ≤ |e.det v| := hmax hu
      have hid : e.det v * b.repr x i = e.det (Function.update v i x) := by
        have hh := congrArg (fun f : E →ₗ[ℝ] ℝ => f x)
          (e.det_smul_mk_coord_eq_det_update hli hsp.ge i)
        exact hh
      rw [← hid, abs_mul] at hbound
      exact (mul_le_mul_iff_right₀ (abs_pos.mpr hdet)).mp (by simpa using hbound)
    intro x i
    by_cases hx : x = 0
    · subst x; simp
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h := hunit (‖x‖⁻¹ • x) (norm_smul_inv_norm (𝕜 := ℝ) hx).le i
    have hid : b.repr (‖x‖⁻¹ • x) i = ‖x‖⁻¹ * b.repr x i := by simp
    rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hn)] at h
    have := mul_le_mul_of_nonneg_left h hn.le
    simpa [← mul_assoc, ne_of_gt hn] using this

                                                                                       
theorem exists_auerbach_vectors {B ι : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [Fintype ι] (hB : ¬ FiniteDimensional ℝ B) :
    ∃ v : ι → B, (∀ i, ‖v i‖ ≤ 1) ∧
      ∀ (c : ι → ℝ) i, |c i| ≤ ‖∑ j, c j • v j‖ := by
  classical
  let I := Module.Basis.ofVectorSpaceIndex ℝ B
  let e : Module.Basis I ℝ B := Module.Basis.ofVectorSpace ℝ B
  have : Infinite I := not_finite_iff_infinite.mp (by
    intro h
    let := h
    exact hB (Module.Finite.of_basis e))
  let f : ι → I := fun i => Infinite.natEmbedding I ((Fintype.equivFin ι) i).val
  have hf : Function.Injective f :=
    (Infinite.natEmbedding I).injective.comp (Fin.val_injective.comp (Fintype.equivFin ι).injective)
  have hli : LinearIndependent ℝ (e ∘ f) := e.linearIndependent.comp f hf
  let V := Submodule.span ℝ (Set.range (e ∘ f))
  let eV : Module.Basis ι ℝ V := Module.Basis.span hli
  let : FiniteDimensional ℝ V := Module.Finite.of_basis eV
  obtain ⟨b, hb, hc⟩ := exists_auerbach_basis eV
  refine ⟨fun i => (b i : B), hb, ?_⟩
  intro c i
  have h := hc (∑ j, c j • b j) i
  rw [b.repr_sum_self] at h
  simpa only [← Submodule.coe_smul, ← Submodule.coe_sum, Submodule.norm_coe] using h

end CompactBanach
end

end OAI
