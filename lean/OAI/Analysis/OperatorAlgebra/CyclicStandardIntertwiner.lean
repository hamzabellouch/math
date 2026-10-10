import OAI.Analysis.PureInfiniteness.NormalizedSeparatingSequence
import OAI.Analysis.OperatorAlgebra.GNSSeparableCyclic

namespace OAI

/-! The application-specific standard representation and bounded intertwiner
for a tested vector of a representation of a separable C*-algebra. -/
noncomputable section
open TopologicalSpace
open scoped ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

universe u v
variable {A : Type u} {H : Type v} [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A] [SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_cyclic_standard_intertwiner
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1) :
    ∃ (K : ComplexHilbert.{u}) (S : StandardModularData K)
      (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : K →L[ℂ] H),
      S.M = bicommutant ρ.range ∧ ‖V‖ ≤ 3 ∧ V S.xi = ξ ∧
      ∀ a, V.comp (ρ a) = (π a).comp V := by
  let f₀ := vectorPositiveFunctional π ξ
  let K₀ := gnsHilbert f₀
  let ρ₀ : A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀) := gnsBundledHom f₀
  let ξ₀ : K₀ := gnsVector f₀ 1
  let W₀ : K₀ →ₗᵢ[ℂ] H := cyclicBundledGNSIsometry f₀ π ξ
    (vectorPositiveFunctional_apply π ξ)
  have hW₀ : W₀ ξ₀ = ξ := cyclicBundledGNSIsometry_one f₀ π ξ _
  have hξ₀ : ‖ξ₀‖ = 1 := by
    rw [← W₀.norm_map ξ₀, hW₀, hξ]
  let : SeparableSpace K₀ := gns_separable_of_cyclic f₀ π ξ
    (vectorPositiveFunctional_apply π ξ)
  let d : ℕ → K₀ := TopologicalSpace.denseSeq K₀
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq K₀
  let Ω := separatingSequence ξ₀ d
  let ω := normalizedSeparatingSequence ξ₀ d
  let f₁ := vectorPositiveFunctional (sequenceAmplification ρ₀) ω
  let K₁ := gnsHilbert f₁
  let ρ₁ : A →⋆ₐ[ℂ] (K₁ →L[ℂ] K₁) := gnsBundledHom f₁
  let W₁ : K₁ →ₗᵢ[ℂ] SequenceHilbert K₀ :=
    cyclicBundledGNSIsometry f₁ (sequenceAmplification ρ₀) ω
      (vectorPositiveFunctional_apply _ _)
  let D := sequenceStandardGNSData ρ₀ ξ₀ hξ₀ d hd
  let S : StandardModularData K₁ := D.toStandardModularData
  let V : K₁ →L[ℂ] H := (‖Ω‖ : ℂ) •
    (W₀.toContinuousLinearMap.comp
      ((lp.evalCLM ℂ (fun _ : ℕ => K₀) 2 0).comp W₁.toContinuousLinearMap))
  have hV (x : K₁) : V x = (‖Ω‖ : ℂ) • W₀ (W₁ x 0) := rfl
  have hΩn : ‖Ω‖ ≤ 3 := by
    have h := separatingSequence_norm_le ξ₀ d
    change ‖Ω‖ ≤ ‖ξ₀‖ + 2 at h
    rw [hξ₀] at h
    norm_num at h ⊢
    exact h
  have hΩ : ‖Ω‖ ≠ 0 := norm_ne_zero_iff.mpr (separatingSequence_ne_zero ξ₀ hξ₀ d)
  refine ⟨K₁, S, ρ₁, V, rfl, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound V (by norm_num)
    intro x
    rw [hV, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg Ω), W₀.norm_map]
    calc
      ‖Ω‖ * ‖W₁ x 0‖ ≤ ‖Ω‖ * ‖W₁ x‖ :=
        mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _)
      _ = ‖Ω‖ * ‖x‖ := by rw [W₁.norm_map]
      _ ≤ 3 * ‖x‖ := mul_le_mul_of_nonneg_right hΩn (norm_nonneg _)
  · change V (gnsVector f₁ 1) = ξ
    rw [hV, cyclicBundledGNSIsometry_one]
    change (‖Ω‖ : ℂ) • W₀ (((‖Ω‖⁻¹ : ℝ) : ℂ) • Ω 0) = ξ
    rw [separatingSequence_zero, map_smul, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hΩ, Complex.ofReal_one, one_smul, hW₀]
  · intro a
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hV, hV, map_smul]
    congr 1
    have h₁ := congrArg (fun T : K₁ →L[ℂ] SequenceHilbert K₀ => T x)
      (cyclicBundledGNSIsometry_intertwines f₁ (sequenceAmplification ρ₀) ω
        (vectorPositiveFunctional_apply _ _) a)
    have h₀ := congrArg (fun T : K₀ →L[ℂ] H => T (W₁ x 0))
      (cyclicBundledGNSIsometry_intertwines f₀ π ξ
        (vectorPositiveFunctional_apply _ _) a)
    change W₀ (W₁ (ρ₁ a x) 0) = π a (W₀ (W₁ x 0))
    rw [show W₁ (ρ₁ a x) = sequenceAmplification ρ₀ a (W₁ x) from h₁]
    exact h₀

end WeakPureInfiniteness

end

end OAI
