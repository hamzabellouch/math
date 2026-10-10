import OAI.Analysis.IrrationalRotation.Model.FieldUnboundedMultiplier
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldHilbert_ext {ξ η : FieldHilbert μ}
    (h : ∀ᵐ x ∂μ, ∀ k, ξ x k = η x k) : ξ = η := by
  apply Lp.ext
  filter_upwards [h] with x hx
  exact lp.ext (funext hx)

theorem fieldMultiplierGraph_unique (h : X → ℤ → ℂ)
    {ξ η ζ : FieldHilbert μ}
    (hη : (ξ, η) ∈ fieldMultiplierGraph μ h)
    (hζ : (ξ, ζ) ∈ fieldMultiplierGraph μ h) : η = ζ := by
  apply fieldHilbert_ext
  filter_upwards [hη, hζ] with x hη hζ
  intro k
  exact (hη k).trans (hζ k).symm

theorem fieldMultiplierGraph_zero (h : X → ℤ → ℂ)
    (p : FieldHilbert μ × FieldHilbert μ)
    (hp : p ∈ fieldMultiplierGraph μ h) (hzero : p.1 = 0) : p.2 = 0 := by
  apply fieldHilbert_ext
  filter_upwards [hp, Lp.coeFn_zero Hilbert 2 μ] with x hx hz
  intro k
  rw [hx, hzero, hz]
  simp

theorem fieldUnboundedMultiplier_graph (h : X → ℤ → ℂ) :
    (fieldUnboundedMultiplier μ h).graph = fieldMultiplierGraph μ h :=
  (fieldMultiplierGraph μ h).toLinearPMap_graph_eq (fieldMultiplierGraph_zero h)

theorem mem_fieldUnboundedMultiplier_domain_iff (h : X → ℤ → ℂ)
    (ξ : FieldHilbert μ) :
    ξ ∈ (fieldUnboundedMultiplier μ h).domain ↔
      ∃ η : FieldHilbert μ, ∀ᵐ x ∂μ, ∀ k, η x k = h x k * ξ x k := by
  change ξ ∈ (fieldMultiplierGraph μ h).map (LinearMap.fst ℂ _ _) ↔ _
  constructor
  · rintro ⟨⟨ζ, η⟩, hζη, hζ⟩
    change ζ = ξ at hζ
    subst ζ
    exact ⟨η, hζη⟩
  · rintro ⟨η, hη⟩
    exact ⟨(ξ, η), hη, rfl⟩

theorem fieldUnboundedMultiplier_apply_ae (h : X → ℤ → ℂ)
    (ξ : (fieldUnboundedMultiplier μ h).domain) :
    ∀ᵐ x ∂μ, ∀ k, fieldUnboundedMultiplier μ h ξ x k = h x k * ξ.val x k :=
  (fieldMultiplierGraph μ h).mem_graph_toLinearPMap (fieldMultiplierGraph_zero h) ξ

theorem fieldUnboundedMultiplier_eq_of_ae (h : X → ℤ → ℂ)
    (ξ : (fieldUnboundedMultiplier μ h).domain) (η : FieldHilbert μ)
    (hη : ∀ᵐ x ∂μ, ∀ k, η x k = h x k * ξ.val x k) :
    fieldUnboundedMultiplier μ h ξ = η :=
  fieldMultiplierGraph_unique h (fieldUnboundedMultiplier_apply_ae h ξ) hη

theorem fieldUnboundedMultiplier_injective (h : X → ℤ → ℂ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0) :
    Function.Injective (fieldUnboundedMultiplier μ h) := by
  intro ξ η heq
  apply Subtype.ext
  apply fieldHilbert_ext
  filter_upwards [fieldUnboundedMultiplier_apply_ae h ξ,
    fieldUnboundedMultiplier_apply_ae h η, hh] with x hξ hη hh
  intro k
  apply mul_left_cancel₀ (hh k)
  rw [← hξ, ← hη, heq]

theorem field_operator_mem_multiplierDomain
    (h f g : X → ℤ → ℂ) (c : ℂ)
    (A B : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, A ξ x k = f x (k - 1) * ξ x (k - 1))
    (hB : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, B ξ x k = g x (k - 1) * ξ x (k - 1))
    (hfg : ∀ᵐ x ∂μ, ∀ k, h x (k + 1) * f x k = c * g x k * h x k)
    (ξ : (fieldUnboundedMultiplier μ h).domain) :
    A ξ.val ∈ (fieldUnboundedMultiplier μ h).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff h _).mpr
  refine ⟨c • B (fieldUnboundedMultiplier μ h ξ), ?_⟩
  filter_upwards [hA ξ.val, hB (fieldUnboundedMultiplier μ h ξ),
    fieldUnboundedMultiplier_apply_ae h ξ, hfg,
    Lp.coeFn_smul c (B (fieldUnboundedMultiplier μ h ξ))]
    with x hA hB hH hfg hsmul
  intro k
  rw [hsmul]
  change c * B (fieldUnboundedMultiplier μ h ξ) x k = h x k * A ξ.val x k
  rw [hA, hB, hH]
  have hk := hfg (k - 1)
  simp only [sub_add_cancel] at hk
  rw [← mul_assoc (h x k), hk]
  ring

theorem field_multiplier_intertwines
    (h f g : X → ℤ → ℂ) (c : ℂ)
    (A B : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, A ξ x k = f x (k - 1) * ξ x (k - 1))
    (hB : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, B ξ x k = g x (k - 1) * ξ x (k - 1))
    (hfg : ∀ᵐ x ∂μ, ∀ k, h x (k + 1) * f x k = c * g x k * h x k)
    (ξ : (fieldUnboundedMultiplier μ h).domain) :
    fieldUnboundedMultiplier μ h
      ⟨A ξ.val, field_operator_mem_multiplierDomain h f g c A B hA hB hfg ξ⟩ =
        c • B (fieldUnboundedMultiplier μ h ξ) := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [hA ξ.val, hB (fieldUnboundedMultiplier μ h ξ),
    fieldUnboundedMultiplier_apply_ae h ξ, hfg,
    Lp.coeFn_smul c (B (fieldUnboundedMultiplier μ h ξ))]
    with x hA hB hH hfg hsmul
  intro k
  rw [hsmul]
  change c * B (fieldUnboundedMultiplier μ h ξ) x k = h x k * A ξ.val x k
  rw [hA, hB, hH]
  have hk := hfg (k - 1)
  simp only [sub_add_cancel] at hk
  rw [← mul_assoc (h x k), hk]
  ring

theorem fieldUnboundedMultiplier_formalAdjoint (h : X → ℤ → ℂ) :
    (fieldUnboundedMultiplier μ h).IsFormalAdjoint
      (fieldUnboundedMultiplier μ (fun x k => star (h x k))) := by
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldUnboundedMultiplier_apply_ae h ξ,
    fieldUnboundedMultiplier_apply_ae (fun x k => star (h x k)) η] with x hξ hη
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [hξ, hη]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_apply]
  ring

theorem fieldUnboundedMultiplier_nonnegative (h : X → ℤ → ℝ)
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 ≤ h x k)
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) :
    0 ≤ (inner ℂ ξ.val
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)).re := by
  let η := fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ
  change 0 ≤ (inner ℂ ξ.val η).re
  rw [L2.inner_def]
  have hre := integral_re (L2.integrable_inner (𝕜 := ℂ) ξ.val η)
  simp only [RCLike.re_eq_complex_re] at hre
  rw [← hre]
  apply integral_nonneg_of_ae
  filter_upwards [fieldUnboundedMultiplier_apply_ae (fun x k => (h x k : ℂ)) ξ,
    hh] with x hξ hh
  change 0 ≤ (inner ℂ (ξ.val x) (η x)).re
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  apply tsum_nonneg
  intro k
  change 0 ≤ (inner ℂ (ξ.val x k)
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ x k)).re
  rw [hξ]
  change 0 ≤ (inner ℂ (ξ.val x k) ((h x k : ℂ) • ξ.val x k)).re
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (hh k) (inner_self_nonneg (𝕜 := ℂ) (x := ξ.val x k))

theorem fieldMultiplier_mem_inverseDomain (h : X → ℤ → ℂ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0)
    (ξ : (fieldUnboundedMultiplier μ h).domain) :
    fieldUnboundedMultiplier μ h ξ ∈
      (fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹)).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
  refine ⟨ξ.val, ?_⟩
  filter_upwards [fieldUnboundedMultiplier_apply_ae h ξ, hh] with x hξ hh
  intro k
  rw [hξ, ← mul_assoc, inv_mul_cancel₀ (hh k), one_mul]

theorem inverse_fieldMultiplier_mul (h : X → ℤ → ℂ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0)
    (ξ : (fieldUnboundedMultiplier μ h).domain) :
    fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹)
      ⟨fieldUnboundedMultiplier μ h ξ, fieldMultiplier_mem_inverseDomain h hh ξ⟩ = ξ.val := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [fieldUnboundedMultiplier_apply_ae h ξ, hh] with x hξ hh
  intro k
  rw [hξ, ← mul_assoc, inv_mul_cancel₀ (hh k), one_mul]

theorem inverseFieldMultiplier_mem_domain (h : X → ℤ → ℂ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0)
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹)).domain) :
    fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹) ξ ∈
      (fieldUnboundedMultiplier μ h).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
  refine ⟨ξ.val, ?_⟩
  filter_upwards [fieldUnboundedMultiplier_apply_ae (fun x k => (h x k)⁻¹) ξ, hh]
    with x hξ hh
  intro k
  rw [hξ, ← mul_assoc, mul_inv_cancel₀ (hh k), one_mul]

theorem fieldMultiplier_mul_inverse (h : X → ℤ → ℂ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0)
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹)).domain) :
    fieldUnboundedMultiplier μ h
      ⟨fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹) ξ,
        inverseFieldMultiplier_mem_domain h hh ξ⟩ = ξ.val := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [fieldUnboundedMultiplier_apply_ae (fun x k => (h x k)⁻¹) ξ, hh]
    with x hξ hh
  intro k
  rw [hξ, ← mul_assoc, mul_inv_cancel₀ (hh k), one_mul]

theorem fieldMultiplier_range (h : X → ℤ → ℂ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0) :
    LinearMap.range (fieldUnboundedMultiplier μ h).toFun =
      (fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹)).domain := by
  ext ξ
  constructor
  · rintro ⟨η, rfl⟩
    exact fieldMultiplier_mem_inverseDomain h hh η
  · intro hξ
    refine ⟨⟨fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹) ⟨ξ, hξ⟩,
      inverseFieldMultiplier_mem_domain h hh ⟨ξ, hξ⟩⟩, ?_⟩
    exact fieldMultiplier_mul_inverse h hh ⟨ξ, hξ⟩

theorem inverse_fieldMultiplier_inner (h : X → ℤ → ℝ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0)
    (η : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)⁻¹)).domain)
    (ζ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) :
    inner ℂ (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)⁻¹) η)
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ζ) =
        inner ℂ η.val ζ.val := by
  have hh' : ∀ᵐ x ∂μ, ∀ k, (h x k : ℂ) ≠ 0 := by
    filter_upwards [hh] with x hx k
    exact Complex.ofReal_ne_zero.mpr (hx k)
  have hf : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).IsFormalAdjoint
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) := by
    simpa using fieldUnboundedMultiplier_formalAdjoint (μ := μ) (fun x k => (h x k : ℂ))
  have heq := hf
    ⟨fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)⁻¹) η,
      inverseFieldMultiplier_mem_domain (fun x k => (h x k : ℂ)) hh' η⟩ ζ
  rw [fieldMultiplier_mul_inverse _ hh'] at heq
  exact heq.symm

end Invariant233.WeightedShift

end

end OAI
