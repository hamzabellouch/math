import Mathlib

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem315.FrameSynthesis

variable {ι E : Type*} [Fintype ι] [sectionDecidableEqι : DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

def synthesis (z : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun c := ∑ i, c i • z i
  map_add' c d := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

include sectionDecidableEqι in
@[simp] theorem synthesis_apply (z : ι → E) (c : EuclideanSpace ℝ ι) :
    synthesis z c = ∑ i, c i • z i := by
  have retainedsectionDecidableEqι := sectionDecidableEqι
  exact rfl

@[simp] theorem synthesis_single (z : ι → E) (i : ι) (a : ℝ) :
    synthesis z (EuclideanSpace.single i a) = a • z i := by
  classical
  simp [synthesis, EuclideanSpace.single]

section Adjoint
variable [FiniteDimensional ℝ E]

@[simp] theorem adjoint_synthesis_apply (z : ι → E) (f : E) (i : ι) :
    (synthesis z).adjoint f i = ⟪z i, f⟫ := by
  classical
  have h := (synthesis z).adjoint_inner_right (EuclideanSpace.single i 1) f
  simpa [EuclideanSpace.inner_single_left] using h

theorem synthesis_adjoint_apply (z : ι → E) (f : E) :
    synthesis z ((synthesis z).adjoint f) = ∑ i, ⟪z i, f⟫ • z i := by
  simp only [synthesis_apply, adjoint_synthesis_apply]

theorem gram_apply (z : ι → E) (c : EuclideanSpace ℝ ι) (i : ι) :
    (synthesis z).adjoint (synthesis z c) i = ∑ j, c j * ⟪z i, z j⟫ := by
  rw [adjoint_synthesis_apply, synthesis_apply, inner_sum]
  simp only [inner_smul_right]

theorem frame_energy (z : ι → E) (f : E) :
    ⟪f, synthesis z ((synthesis z).adjoint f)⟫ = ∑ i, ⟪z i, f⟫ ^ 2 := by
  rw [synthesis_adjoint_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_right, real_inner_comm f (z i)]
  ring

end Adjoint

def normalized (z : E) : E := ‖z‖⁻¹ • z

theorem normalized_rank_one_eq_projection (z f : E) :
    ⟪normalized z, f⟫ • normalized z = (ℝ ∙ z).starProjection f := by
  rw [Submodule.starProjection_singleton ℝ]
  simp only [normalized, inner_smul_left, RCLike.conj_to_real, smul_smul]
  congr 1
  change (‖z‖⁻¹ * ⟪z, f⟫) * ‖z‖⁻¹ = ⟪z, f⟫ / ‖z‖ ^ 2
  ring

theorem normalized_inner (z w : E) :
    ⟪normalized z, normalized w⟫ = ⟪z, w⟫ / (‖z‖ * ‖w‖) := by
  simp only [normalized, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

variable [FiniteDimensional ℝ E]

theorem normalized_frame_apply (z : ι → E) (f : E) :
    synthesis (fun i => normalized (z i))
      ((synthesis (fun i => normalized (z i))).adjoint f) =
        ∑ i, (ℝ ∙ z i).starProjection f := by
  rw [synthesis_adjoint_apply]
  simp_rw [normalized_rank_one_eq_projection]

theorem normalized_frame_eq_sum_projection (z : ι → E) :
    (synthesis (fun i => normalized (z i))).comp
        (synthesis (fun i => normalized (z i))).adjoint =
      ∑ i, ((ℝ ∙ z i).starProjection : E →L[ℝ] E).toLinearMap := by
  ext f
  simpa using normalized_frame_apply z f

theorem normalized_gram_apply (z : ι → E) (c : EuclideanSpace ℝ ι) (i : ι) :
    (synthesis (fun j => normalized (z j))).adjoint
        (synthesis (fun j => normalized (z j)) c) i =
      ∑ j, c j * (⟪z i, z j⟫ / (‖z i‖ * ‖z j‖)) := by
  rw [gram_apply]
  simp_rw [normalized_inner]

theorem normalized_frame_energy (z : ι → E) (f : E) :
    ⟪f, synthesis (fun i => normalized (z i))
      ((synthesis (fun i => normalized (z i))).adjoint f)⟫ =
        ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [normalized_frame_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := (ℝ ∙ z i).re_inner_starProjection_eq_normSq f
  simpa only [RCLike.re_to_real, real_inner_comm,
    Submodule.starProjection_apply, Submodule.norm_coe] using h

theorem scaled_frame_apply (a : ℝ) (z : ι → E) (f : E) :
    synthesis (fun i => a • z i) ((synthesis (fun i => a • z i)).adjoint f) =
      a ^ 2 • synthesis z ((synthesis z).adjoint f) := by
  rw [synthesis_adjoint_apply, synthesis_adjoint_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [inner_smul_left, RCLike.conj_to_real, smul_smul]
  congr 1
  ring

theorem scaled_normalized_frame_apply (a : ℝ) (z : ι → E) (f : E) :
    synthesis (fun i => a • normalized (z i))
      ((synthesis (fun i => a • normalized (z i))).adjoint f) =
        a ^ 2 • ∑ i, (ℝ ∙ z i).starProjection f := by
  rw [scaled_frame_apply, normalized_frame_apply]

theorem scaled_normalized_frame_energy (a : ℝ) (z : ι → E) (f : E) :
    ⟪f, synthesis (fun i => a • normalized (z i))
      ((synthesis (fun i => a • normalized (z i))).adjoint f)⟫ =
        a ^ 2 * ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [scaled_frame_apply, inner_smul_right, normalized_frame_energy]

theorem half_normalized_frame_energy (z : ι → E) (f : E) :
    ⟪f, synthesis (fun i => (Real.sqrt 2)⁻¹ • normalized (z i))
      ((synthesis (fun i => (Real.sqrt 2)⁻¹ • normalized (z i))).adjoint f)⟫ =
        (1 / 2 : ℝ) * ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [scaled_normalized_frame_energy]
  have hsq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hsq]

theorem frame_apply_of_common_norm_sq (z : ι → E) (a : ℝ)
    (hz : ∀ i, z i = 0 ∨ ‖z i‖ ^ 2 = a) (f : E) :
    synthesis z ((synthesis z).adjoint f) = a • ∑ i, (ℝ ∙ z i).starProjection f := by
  rw [synthesis_adjoint_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hz i with hzero | hnorm
  · simp [hzero]
  · rw [← Submodule.smul_starProjection_singleton ℝ f]
    change ‖z i‖ ^ 2 • (ℝ ∙ z i).starProjection f = _
    rw [hnorm]

theorem frame_energy_of_common_norm_sq (z : ι → E) (a : ℝ)
    (hz : ∀ i, z i = 0 ∨ ‖z i‖ ^ 2 = a) (f : E) :
    ⟪f, synthesis z ((synthesis z).adjoint f)⟫ =
      a * ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [frame_apply_of_common_norm_sq z a hz, inner_smul_right, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have h := (ℝ ∙ z i).re_inner_starProjection_eq_normSq f
  simpa only [RCLike.re_to_real, real_inner_comm,
    Submodule.starProjection_apply, Submodule.norm_coe] using h


end Problem315.FrameSynthesis

end

end OAI
