import OAI.Analysis.BoundedHochschild.MultimodularGenerators
import OAI.Analysis.BoundedHochschild.RightAveragingAlgebra

namespace OAI

/-! Finite group averaging on arbitrary bounded linear maps. Unlike the
simultaneous infinite module projection, this elementary contraction does
not require complete boundedness and preserves normality. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} {G : Type v} [CStarAlgebra M] [Group G] [Fintype G]

def finiteGroupRightAverage (ρ : G →* unitary M) (T : M →L[ℂ] M) : M →L[ℂ] M :=
  (Fintype.card G : ℂ)⁻¹ • finiteRightAverage (fun g => (ρ g : M)) T

@[simp] lemma finiteGroupRightAverage_apply (ρ : G →* unitary M) (T : M →L[ℂ] M) (x : M) :
    finiteGroupRightAverage ρ T x =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, T (x * (ρ g : M)) * star (ρ g : M) := by
  simp only [finiteGroupRightAverage, smul_apply, finiteRightAverage_apply]

lemma finiteGroupRightAverage_norm (ρ : G →* unitary M) (T : M →L[ℂ] M) :
    ‖finiteGroupRightAverage ρ T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hb (g : G) : ‖T (x * (ρ g : M)) * star (ρ g : M)‖ ≤ ‖T‖ * ‖x‖ := by
    rw [show star (ρ g : M) = ((star (ρ g) : unitary M) : M) by rfl,
      CStarRing.norm_mul_coe_unitary]
    simpa only [CStarRing.norm_mul_coe_unitary] using T.le_opNorm (x * (ρ g : M))
  have hc : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [finiteGroupRightAverage_apply, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ((Fintype.card G : ℝ) * (‖T‖ * ‖x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (norm_sum_le _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun g _ => hb g))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

lemma finiteGroupRightAverage_module (ρ : G →* unitary M) (T : M →L[ℂ] M)
    (h : G) (x : M) :
    finiteGroupRightAverage ρ T (x * (ρ h : M)) = finiteGroupRightAverage ρ T x * (ρ h : M) := by
  have hu : star (ρ h : M) * (ρ h : M) = 1 := Unitary.star_mul_self_of_mem (ρ h).property
  have hs : (∑ g : G, T ((x * (ρ h : M)) * (ρ g : M)) * star (ρ g : M)) =
      ∑ g : G, (T (x * (ρ g : M)) * star (ρ g : M)) * (ρ h : M) := by
    apply Fintype.sum_equiv (Equiv.mulLeft h) _ _
    intro g
    change T ((x * (ρ h : M)) * (ρ g : M)) * star (ρ g : M) =
      (T (x * (ρ (h * g) : M)) * star (ρ (h * g) : M)) * (ρ h : M)
    rw [map_mul ρ h g, Submonoid.coe_mul, star_mul]
    simp only [mul_assoc, hu, mul_one]
  simp only [finiteGroupRightAverage_apply, smul_mul_assoc, Finset.sum_mul]
  rw [hs]

lemma finiteGroupRightAverage_span_module (ρ : G →* unitary M) (T : M →L[ℂ] M)
    {a : M} (ha : a ∈ Submodule.span ℂ (Set.range (fun g => (ρ g : M)))) (x : M) :
    finiteGroupRightAverage ρ T (x * a) = finiteGroupRightAverage ρ T x * a := by
  apply linear_maps_eq_on_span (Set.range (fun g => (ρ g : M)))
    ((finiteGroupRightAverage ρ T).comp (ContinuousLinearMap.mul ℂ M x))
    (ContinuousLinearMap.mul ℂ M (finiteGroupRightAverage ρ T x)) _ ha
  rintro _ ⟨g, rfl⟩
  exact finiteGroupRightAverage_module ρ T g x

lemma finiteGroupRightAverage_fixes (ρ : G →* unitary M) (T : M →L[ℂ] M)
    (hT : ∀ g x, T (x * (ρ g : M)) = T x * (ρ g : M)) :
    finiteGroupRightAverage ρ T = T := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hu (g : G) : (ρ g : M) * star (ρ g : M) = 1 := Unitary.mul_star_self_of_mem (ρ g).property
  ext x
  simp only [finiteGroupRightAverage_apply, hT, mul_assoc, hu,
    mul_one, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

def finiteGroupRightAverageCLM (ρ : G →* unitary M) :
    (M →L[ℂ] M) →L[ℂ] (M →L[ℂ] M) :=
  LinearMap.mkContinuous
    { toFun := finiteGroupRightAverage ρ
      map_add' := fun T U => by
        simp only [finiteGroupRightAverage, finiteRightAverage_add, smul_add]
      map_smul' := fun z T => by
        simp only [finiteGroupRightAverage, finiteRightAverage_smul, RingHom.id_apply]
        exact smul_comm _ _ _ }
    1 (fun T => by
      change ‖finiteGroupRightAverage ρ T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using finiteGroupRightAverage_norm ρ T)

@[simp] lemma finiteGroupRightAverageCLM_apply (ρ : G →* unitary M) (T : M →L[ℂ] M) :
    finiteGroupRightAverageCLM ρ T = finiteGroupRightAverage ρ T := rfl

lemma finiteGroupRightAverage_idempotent (ρ : G →* unitary M) (T : M →L[ℂ] M) :
    finiteGroupRightAverage ρ (finiteGroupRightAverage ρ T) = finiteGroupRightAverage ρ T :=
  finiteGroupRightAverage_fixes ρ _ (finiteGroupRightAverage_module ρ T)

lemma finiteGroupRightAverage_covariance (ρ : G →* unitary M) (T : M →L[ℂ] M) (a b : M) :
    finiteGroupRightAverage ρ (leftSandwichMap a b T) =
      leftSandwichMap a b (finiteGroupRightAverage ρ T) := by
  rw [finiteGroupRightAverage, ← leftSandwichMap_rightAverage]
  ext x
  simp only [smul_apply, leftSandwichMap_apply, mul_smul_comm, finiteGroupRightAverage]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma finiteGroupRightAverage_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ρ : G →* unitary M) (T : M →L[ℂ] M) (hT : HasPreadjoint e T) :
    HasPreadjoint e (finiteGroupRightAverage ρ T) := by
  have hR := (HochschildSakai.abstract_multiplication_normal e).2
  unfold finiteGroupRightAverage finiteRightAverage
  apply HasPreadjoint.smul e
  apply HasPreadjoint.sum e
  intro g _
  exact (hR _).comp e (hT.comp e (hR _))

end BoundedHochschild.KadisonRingrose

end

end OAI
