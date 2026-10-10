import Mathlib
import OAI.Analysis.FreeWords.UltraTrace

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] KKUltraTrace.seqOrder

attribute [local instance] KKUltraTrace.seqSOR

open scoped InnerProductSpace

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem tracial_null_right (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x)) (x : A)
    (hx : τ (star x*x) = 0) (b : A) : τ (star (x*b) * (x*b)) = 0 := by
  apply le_antisymm _ (τ.map_nonneg (star_mul_self_nonneg _))
  calc
    τ (star (x*b) * (x*b)) = τ (x * (b * star b) * star x) := by
      rw [htr (star (x*b)) (x*b), star_mul]
      congr 1
      noncomm_ring
    _ ≤ τ (‖b * star b‖ • (x * star x)) :=
      τ.monotone' (CStarAlgebra.star_right_conjugate_le_norm_smul x (b * star b))
    _ = 0 := by simp [← Complex.coe_smul, htr x (star x), hx]

def gnsQuotient (τ : A →ₚ[ℂ] ℂ) : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS) :=
  τ.gnsStarAlgHom.range.topologicalClosure

instance gnsQuotient_closed (τ : A →ₚ[ℂ] ℂ) :
    IsClosed (gnsQuotient τ : Set (τ.GNS →L[ℂ] τ.GNS)) := isClosed_closure

@[instance_reducible] def quotientOrder (τ : A →ₚ[ℂ] ℂ) : PartialOrder (gnsQuotient τ) :=
  CStarAlgebra.spectralOrder _

attribute [local instance] KKUltraTrace.quotientOrder

@[instance_reducible] def quotientLE (τ : A →ₚ[ℂ] ℂ) : LE (gnsQuotient τ) := (quotientOrder τ).toLE

attribute [local instance] KKUltraTrace.quotientLE

@[instance_reducible] def quotientPreorder (τ : A →ₚ[ℂ] ℂ) : Preorder (gnsQuotient τ) := (quotientOrder τ).toPreorder

attribute [local instance] KKUltraTrace.quotientPreorder

theorem quotientSOR (τ : A →ₚ[ℂ] ℂ) : StarOrderedRing (gnsQuotient τ) :=
  CStarAlgebra.spectralOrderedRing _

attribute [local instance] KKUltraTrace.quotientSOR

def gnsExpectation (τ : A →ₚ[ℂ] ℂ) (x : τ.GNS →L[ℂ] τ.GNS) : ℂ :=
  ⟪gnsVector τ 1, x (gnsVector τ 1)⟫_ℂ

@[simp] theorem gnsExpectation_image (τ : A →ₚ[ℂ] ℂ) (a : A) :
    gnsExpectation τ (τ.gnsStarAlgHom a) = τ a := by
  rw [gnsExpectation, gnsStarAlgHom_vector, mul_one, gnsVector_inner, star_one, one_mul]

theorem continuous_gnsExpectation (τ : A →ₚ[ℂ] ℂ) : Continuous (gnsExpectation τ) := by
  unfold gnsExpectation
  fun_prop

def gnsQuotientState (τ : A →ₚ[ℂ] ℂ) : gnsQuotient τ →ₚ[ℂ] ℂ where
  toFun x := gnsExpectation τ x.1
  map_add' x y := by simp [gnsExpectation, inner_add_right]
  map_smul' c x := by simp [gnsExpectation]
  monotone' x y hxy := by
    obtain ⟨v, hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
    apply sub_nonneg.mp
    change 0 ≤ ⟪gnsVector τ 1, y.1 (gnsVector τ 1)⟫_ℂ -
      ⟪gnsVector τ 1, x.1 (gnsVector τ 1)⟫_ℂ
    rw [← inner_sub_right]
    have he : y.1 (gnsVector τ 1) - x.1 (gnsVector τ 1) =
        (star v.1) (v.1 (gnsVector τ 1)) :=
      congrArg (fun z : gnsQuotient τ => z.1 (gnsVector τ 1)) hv
    rw [he]
    change 0 ≤ ⟪gnsVector τ 1, v.1.adjoint (v.1 (gnsVector τ 1))⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_self_ofReal_re]
    exact Complex.zero_le_real.mpr (inner_self_nonneg (𝕜 := ℂ) (x := v.1 (gnsVector τ 1)))

@[simp] theorem gnsQuotientState_star_mul (τ : A →ₚ[ℂ] ℂ) (x : gnsQuotient τ) :
    gnsQuotientState τ (star x * x) =
      ⟪x.1 (gnsVector τ 1), x.1 (gnsVector τ 1)⟫_ℂ := by
  change ⟪gnsVector τ 1, x.1.adjoint (x.1 (gnsVector τ 1))⟫_ℂ = _
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

theorem gnsQuotientState_tracial (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x * y) = τ (y * x)) (x y : gnsQuotient τ) :
    gnsQuotientState τ (x * y) = gnsQuotientState τ (y * x) := by
  have hb : ∀ a ∈ τ.gnsStarAlgHom.range, ∀ b ∈ τ.gnsStarAlgHom.range,
      gnsExpectation τ (a * b) = gnsExpectation τ (b * a) := by
    rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
    change gnsExpectation τ (τ.gnsStarAlgHom a' * τ.gnsStarAlgHom b') =
      gnsExpectation τ (τ.gnsStarAlgHom b' * τ.gnsStarAlgHom a')
    rw [← map_mul τ.gnsStarAlgHom, ← map_mul τ.gnsStarAlgHom,
      gnsExpectation_image, gnsExpectation_image]
    exact htr a' b'
  have hc : ∀ b ∈ τ.gnsStarAlgHom.range.topologicalClosure,
      ∀ a ∈ τ.gnsStarAlgHom.range, gnsExpectation τ (a * b) = gnsExpectation τ (b * a) := by
    intro b hb' a ha
    apply (closure_minimal (t := {z | gnsExpectation τ (a * z) = gnsExpectation τ (z * a)})
      (fun z hz => hb a ha z hz) ?_) hb'
    exact isClosed_eq ((continuous_gnsExpectation τ).comp (continuous_const.mul continuous_id))
      ((continuous_gnsExpectation τ).comp (continuous_id.mul continuous_const))
  change gnsExpectation τ (x.1 * y.1) = gnsExpectation τ (y.1 * x.1)
  apply (closure_minimal (t := {z | gnsExpectation τ (z * y.1) = gnsExpectation τ (y.1 * z)})
    (fun z hz => hc y.1 y.2 z hz) ?_) x.2
  exact isClosed_eq ((continuous_gnsExpectation τ).comp (continuous_id.mul continuous_const))
    ((continuous_gnsExpectation τ).comp (continuous_const.mul continuous_id))

theorem gnsQuotientState_faithful (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x * y) = τ (y * x)) (x : gnsQuotient τ)
    (hx : gnsQuotientState τ (star x * x) = 0) : x = 0 := by
  have hzero : ∀ b : gnsQuotient τ, x.1 (b.1 (gnsVector τ 1)) = 0 := by
    intro b
    have hab := tracial_null_right (gnsQuotientState τ) (gnsQuotientState_tracial τ htr) x hx b
    rw [gnsQuotientState_star_mul] at hab
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp hab
  have hvec : ∀ a : A, x.1 (gnsVector τ a) = 0 := by
    intro a
    let b : gnsQuotient τ := ⟨τ.gnsStarAlgHom a, subset_closure ⟨a, rfl⟩⟩
    have hb := hzero b
    simpa only [b, gnsStarAlgHom_vector, mul_one] using hb
  apply Subtype.ext
  ext ξ
  induction ξ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq x.1.continuous continuous_const
  | ih a => exact hvec (τ.ofPreGNS a)

theorem gnsQuotient_has_faithful_trace (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
    (htr : ∀ x y : A, τ (x * y) = τ (y * x)) :
    ∃ T : gnsQuotient τ →ₚ[ℂ] ℂ,
      (∀ x, T x = ⟪(τ.toPreGNS 1 : τ.GNS), x.1 (τ.toPreGNS 1 : τ.GNS)⟫_ℂ) ∧
      T 1 = 1 ∧ (∀ x y, T (x * y) = T (y * x)) ∧
      (∀ x, T (star x * x) = 0 → x = 0) := by
  refine ⟨gnsQuotientState τ, fun _ => rfl, ?_, gnsQuotientState_tracial τ htr,
    gnsQuotientState_faithful τ htr⟩
  change ⟪gnsVector τ 1, gnsVector τ 1⟫_ℂ = 1
  simpa only [gnsVector_inner, star_one, one_mul] using h1

end

end KKUltraTrace
end

end OAI
