import OAI.Analysis.BoundedHochschild.NormalOperators
import OAI.Analysis.BoundedHochschild.PrimitiveAverages
import OAI.Analysis.BoundedHochschild.CentralProjectionSuprema

namespace OAI

/-!
# Normal positive functionals for the finite trace cover

Every nonzero projection in an abstract von Neumann algebra is detected by
a normal positive state supported on that projection. This constructs the
normal positive functionals needed for a later trace cover; it does not
assume or assert that finiteness alone supplies a trace.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector state before normalizing its vector. -/
def vectorPositiveFunctional (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : M →ₚ[ℂ] ℂ where
  toLinearMap := (coefficient π ξ ξ).toLinearMap
  monotone' := by
    change Monotone (coefficient π ξ ξ)
    apply (monotone_iff_map_nonneg _).mpr
    intro a ha
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (map_nonneg π ha)).inner_nonneg_right ξ

@[simp] lemma vectorPositiveFunctional_apply (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (a : M) : vectorPositiveFunctional π ξ a = inner ℂ ξ (π a ξ) := rfl

omit [CompleteSpace X] in
lemma vectorPositiveFunctional_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {ξ : H} (hξ : ξ ∈ normalVectors e π) :
    TraceInPredual e (vectorPositiveFunctional π ξ) := by
  exact (mem_normalDual e _).mp ((mem_normalVectors e π ξ).mp hξ ξ)

/-- Every nonzero projection supports a normal positive state. -/
theorem exists_normal_state_on_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ ψ : M →ₚ[ℂ] ℂ, TraceInPredual e ψ ∧ ψ 1 = 1 ∧ ψ p = 1 ∧
      ∀ a : M, ψ (p * a * p) = ψ a := by
  classical
  have hex : ∃ z : X, e.symm p z ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hp0
    apply e.symm.injective
    ext z
    simpa only [map_zero, zero_apply] using hn z
  obtain ⟨z, hz⟩ := hex
  let φ := predualEmbedding e z
  let m := functionalModel φ
  let π := m.representation
  let η := m.leftVector
  let ξ := normalProjection e π m.rightVector
  have hφ : φ ∈ normalDual e := ⟨z, rfl⟩
  have hreal : coefficient π η ξ = φ := by
    exact (normalProjection_fixes_normal e π η m.rightVector
      (m.realizes.symm ▸ hφ)).trans m.realizes
  have hξ : ξ ∈ normalVectors e π := by simp [ξ, normalProjection]
  let ζ := π p ξ
  have hζ : ζ ∈ normalVectors e π := normalVectors_mul e π hξ p
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    have he := congrArg (fun f : StrongDual ℂ M => f p) hreal
    have hφp : φ p ≠ 0 := by simpa only [φ, predualEmbedding_apply, star_ne_zero] using hz
    apply hφp
    change inner ℂ η ζ = φ p at he
    rw [hzero, inner_zero_right] at he
    exact he.symm
  have hfix : π p ζ = ζ := by
    change π p (π p ξ) = π p ξ
    rw [← mul_apply_eq_comp, ← map_mul, hp.isIdempotentElem.eq]
  let w := (‖ζ‖⁻¹ : ℂ) • ζ
  have hwn : ‖w‖ = 1 := norm_smul_inv_norm hζ0
  have hw : w ∈ normalVectors e π := (normalVectors e π).smul_mem _ hζ
  have hwfix : π p w = w := by simp only [w, map_smul, hfix]
  let ψ := vectorPositiveFunctional π w
  have hψ1 : ψ 1 = 1 := by
    simp only [ψ, vectorPositiveFunctional_apply, map_one, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, hwn]
    norm_num
  refine ⟨ψ, vectorPositiveFunctional_normal e π hw, hψ1, ?_, ?_⟩
  · simpa only [ψ, vectorPositiveFunctional_apply, hwfix, map_one, one_apply_eq_self]
      using hψ1
  · intro a
    change inner ℂ w (π (p * a * p) w) = inner ℂ w (π a w)
    rw [map_mul, map_mul]
    change inner ℂ w (π p (π a (π p w))) = inner ℂ w (π a w)
    rw [hwfix, ← ContinuousLinearMap.adjoint_inner_left]
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, hp.isSelfAdjoint.star_eq, hwfix]

lemma normal_functional_central_null_chain (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hS : ∀ q ∈ S, IsStarProjection q ∧ (∀ a : M, q * a = a * q) ∧ ψ q = 0) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ ψ p = 0 ∧
      ∀ q ∈ S, q ≤ p := by
  obtain ⟨p, hp, hc, hu, _, _, U, _, ht⟩ :=
    exists_central_projection_chain_supremum_with_limit e S hne hchain
      (fun q hq => (hS q hq).1) (fun q hq => (hS q hq).2.1)
  refine ⟨p, hp, hc, ?_, hu⟩
  have heq : (fun q : S => ψ (q : M)) = (fun _ : S => (0 : ℂ)) :=
    funext fun q => (hS q q.property).2.2
  have hl := trace_predual_tendsto e ψ hψ ht
  rw [heq] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

/-- A normal positive functional is faithful on central projections within its
central support. This is not a traciality assertion. -/
theorem exists_normal_positive_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ ψ p = ψ 1 ∧
      ∀ q : M, IsStarProjection q → (∀ a : M, q * a = a * q) →
        q ≤ p → ψ q = 0 → q = 0 := by
  classical
  let S : Set M := {q | IsStarProjection q ∧ (∀ a : M, q * a = a * q) ∧ ψ q = 0}
  have hz : (0 : M) ∈ S := ⟨IsStarProjection.zero M, fun a => by simp, map_zero ψ⟩
  obtain ⟨r, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain a ha => by
    obtain ⟨s, hs, hcs, hψs, hu⟩ := normal_functional_central_null_chain e ψ hψ
      c ⟨a, ha⟩ hchain (fun q hq => hc hq)
    exact ⟨s, ⟨hs, hcs, hψs⟩, hu⟩) 0 hz
  have hr := hmax.1.1
  have hrc := hmax.1.2.1
  have hψr := hmax.1.2.2
  refine ⟨1 - r, hr.one_sub, ?_, ?_, ?_⟩
  · intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hrc]
  · rw [map_sub, hψr, sub_zero]
  · intro q hq hqc hqr hψq
    have hrq : r * q = 0 := by
      have h := (hq.le_iff_mul_eq_right hr.one_sub).mp hqr
      rw [sub_mul, one_mul] at h
      exact sub_eq_self.mp h
    have hs : r + q ∈ S := ⟨hr.add hq hrq,
      fun a => by rw [add_mul, mul_add, hrc, hqc], by rw [map_add, hψr, hψq, add_zero]⟩
    have hle : r ≤ r + q := le_add_of_nonneg_right hq.nonneg
    have he : r + q = r := le_antisymm (hmax.2 hs hle) hle
    exact add_eq_left.mp he

/-- A normal state detecting all nonzero central subprojections of `p`. -/
def HasCentralFaithfulNormalState (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (p : M) : Prop :=
  ∃ ψ : M →ₚ[ℂ] ℂ, TraceInPredual e ψ ∧ ψ 1 = 1 ∧ ψ p = 1 ∧
    ∀ q : M, IsStarProjection q → (∀ a : M, q * a = a * q) →
      q ≤ p → ψ q = 0 → q = 0

/-- Every nonzero central projection contains a nonzero central subprojection
on which some normal state is faithful on the center. -/
theorem exists_central_normal_state_subprojection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hqc : ∀ a : M, q * a = a * q) (hq0 : q ≠ 0) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      p ≤ q ∧ p ≠ 0 ∧ HasCentralFaithfulNormalState e p := by
  obtain ⟨ψ, hψ, hψ1, _, hsupport⟩ := exists_normal_state_on_projection e hq hq0
  obtain ⟨p, hp, hpc, hψp, hfaith⟩ := exists_normal_positive_central_support e ψ hψ
  have hψp1 : ψ p = 1 := hψp.trans hψ1
  have hcut : IsStarProjection (p * (1 - q)) := hp.mul hq.one_sub
    (show Commute p (1 - q) from hpc (1 - q))
  have hcutc : ∀ a : M, (p * (1 - q)) * a = a * (p * (1 - q)) := by
    intro a
    have hqc' : Commute (1 - q) a := (Commute.one_left a).sub_left (hqc a)
    exact ((show Commute p a from hpc a).mul_left hqc').eq
  have hcutle : p * (1 - q) ≤ p := (hcut.le_iff_mul_eq_right hp).mpr
    (by rw [← mul_assoc, hp.isIdempotentElem.eq])
  have hcutzero : ψ (p * (1 - q)) = 0 := by
    have h := hsupport (p * (1 - q))
    have hzero : q * (p * (1 - q)) = 0 := by
      rw [← mul_assoc, hqc p, mul_assoc, mul_sub, mul_one,
        hq.isIdempotentElem.eq, sub_self, mul_zero]
    rw [hzero, zero_mul, map_zero] at h
    exact h.symm
  have hpq : p ≤ q := by
    have hzero := hfaith (p * (1 - q)) hcut hcutc hcutle hcutzero
    rw [mul_sub, mul_one] at hzero
    exact (hp.le_iff_mul_eq_left hq).mpr (sub_eq_zero.mp hzero).symm
  have hp0 : p ≠ 0 := by
    intro hzero
    have h01 : (0 : ℂ) = 1 := by simpa only [hzero, map_zero] using hψp1
    exact zero_ne_one h01
  exact ⟨p, hp, hpc, hpq, hp0, ψ, hψ, hψ1, hψp1, hfaith⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
