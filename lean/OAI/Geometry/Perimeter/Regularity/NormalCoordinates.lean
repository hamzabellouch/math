import OAI.Geometry.Perimeter.Regularity.HasC1TraceAt

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace RPISingularHarnack
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev normalPlane (v : V) := (ℝ ∙ v)ᗮ

def normalCoordinateIsometry (v : V) (hv : ‖v‖ = 1) :
    WithLp 2 (normalPlane v × ℝ) →ₗᵢ[ℝ] V where
  toLinearMap :=
    { toFun := fun x ↦ (x.fst : V) + x.snd • v
      map_add' := by intro x y; simp [add_smul]; abel
      map_smul' := by intro t x; simp [smul_add,smul_smul] }
  norm_map' := by
    intro x
    have ho : inner ℝ (x.fst : V) v = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.fst.property
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(x.fst : V)+x.snd•v‖^2 = ‖x‖^2
    rw [norm_add_sq_real, real_inner_smul_right, ho, mul_zero, mul_zero, add_zero,
      norm_smul, hv, mul_one, WithLp.prod_norm_sq_eq_of_L2]
    rfl

theorem normalCoordinateIsometry_surjective (v : V) (hv : ‖v‖ = 1) :
    Function.Surjective (normalCoordinateIsometry v hv) := by
  have hself : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq,hv]; norm_num
  intro x
  let y : normalPlane v := ⟨x-inner ℝ v x•v, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right,inner_sub_right,
      real_inner_smul_right,hself,mul_one,sub_self]⟩
  refine ⟨WithLp.toLp 2 (y,inner ℝ v x), ?_⟩
  change x-inner ℝ v x•v+inner ℝ v x•v=x
  exact sub_add_cancel _ _

def normalCoordinateEquiv (v : V) (hv : ‖v‖ = 1) :
    WithLp 2 (normalPlane v × ℝ) ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofSurjective (normalCoordinateIsometry v hv)
    (normalCoordinateIsometry_surjective v hv)

@[simp] theorem normalCoordinateEquiv_apply (v : V) (hv : ‖v‖ = 1)
    (x : WithLp 2 (normalPlane v × ℝ)) :
    normalCoordinateEquiv v hv x = (x.fst : V)+x.snd•v := rfl

variable [MeasurableSpace V] [BorelSpace V]

def normalCoordinates (v : V) (hv : ‖v‖ = 1) : (normalPlane v × ℝ) ≃ᵐ V :=
  (MeasurableEquiv.toLp 2 (normalPlane v × ℝ)).trans
    (normalCoordinateEquiv v hv).toMeasurableEquiv

@[simp] theorem normalCoordinates_apply (v : V) (hv : ‖v‖ = 1)
    (x : normalPlane v × ℝ) : normalCoordinates v hv x = (x.1 : V)+x.2•v := rfl

variable [FiniteDimensional ℝ V]

theorem normalCoordinates_measurePreserving (v : V) (hv : ‖v‖ = 1) :
    MeasurePreserving (normalCoordinates v hv) volume volume :=
  (normalCoordinateEquiv v hv).measurePreserving.comp
    (WithLp.volume_preserving_toLp (normalPlane v) ℝ)

theorem integral_normalCoordinates (v : V) (hv : ‖v‖ = 1) (f : V → ℝ)
    (hf : Integrable f volume) :
    (∫ x, f x) = ∫ y : normalPlane v, ∫ s : ℝ, f ((y:V)+s•v) := by
  have hm := normalCoordinates_measurePreserving v hv
  have he := hm.integral_comp (normalCoordinates v hv).measurableEmbedding f
  rw [← he]
  apply integral_prod
  exact (hm.integrable_comp hf.aestronglyMeasurable).mpr hf

theorem lintegral_normalCoordinates (v : V) (hv : ‖v‖ = 1) (f : V → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x, f x) = ∫⁻ y : normalPlane v, ∫⁻ s : ℝ, f ((y:V)+s•v) := by
  rw [← (normalCoordinates_measurePreserving v hv).lintegral_comp hf]
  apply lintegral_prod
  exact (hf.comp (normalCoordinates v hv).measurable).aemeasurable

end RPISingularHarnack

end

end OAI
