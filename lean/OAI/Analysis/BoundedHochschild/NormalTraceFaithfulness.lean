import OAI.Analysis.BoundedHochschild.FiniteNormalTrace
import OAI.Analysis.BoundedHochschild.FiniteNormalState

namespace OAI

/-! A normal trace faithful on the center is faithful on the whole algebra. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma normal_tracial_null_projection_join (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htp : τ p = 0) (htq : τ q = 0) :
    ∃ r : M, IsStarProjection r ∧ p ≤ r ∧ q ≤ r ∧ τ r = 0 := by
  obtain ⟨v, hvq, _, hr, hpr, hqr, _⟩ := exists_trace_free_projection_join e p q hp hq
  have hvi : τ v.initial = 0 := le_antisymm ((τ.monotone hvq).trans_eq htq)
    (τ.map_nonneg v.initial_proj.nonneg)
  have hvf : τ v.final = 0 := (htr v.val (star v.val)).trans hvi
  exact ⟨p + v.final, hr, hpr, hqr, by rw [map_add, htp, hvf, add_zero]⟩

/-- The largest projection annihilated by a normal trace is central. -/
theorem normal_trace_largest_null_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a)) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ τ p = 0 ∧
      ∀ q : M, IsStarProjection q → τ q = 0 → q ≤ p := by
  classical
  let S : Set M := {p | IsStarProjection p ∧ τ p = 0}
  obtain ⟨p, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain a ha => by
    obtain ⟨p, hp, hu, _, _, U, _, ht⟩ :=
      exists_projection_chain_supremum_with_limit e c ⟨a, ha⟩ hchain
        (fun q hq => (hc hq).1)
    refine ⟨p, ⟨hp, ?_⟩, hu⟩
    have heq : (fun q : c => τ (q : M)) = (fun _ : c => (0 : ℂ)) :=
      funext (fun q => (hc q.property).2)
    have hlim := trace_predual_tendsto e τ hτ ht
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds) 0
      (show (0 : M) ∈ S from ⟨IsStarProjection.zero M, map_zero τ⟩)
  have hp := hmax.1.1
  have hnull := hmax.1.2
  have hgreat (q : M) (hq : IsStarProjection q) (htq : τ q = 0) : q ≤ p := by
    obtain ⟨r, hr, hpr, hqr, htr0⟩ := normal_tracial_null_projection_join e τ htr hp hq hnull htq
    exact hqr.trans (hmax.2 ⟨hr, htr0⟩ hpr)
  have hconj (u : unitary M) : (u : M) * p * star (u : M) ≤ p := by
    apply hgreat
    · constructor
      · change ((u : M) * p * star (u : M)) * ((u : M) * p * star (u : M)) =
          (u : M) * p * star (u : M)
        calc
          _ = (u : M) * (p * ((star (u : M) * (u : M)) * p)) * star (u : M) := by
            noncomm_ring
          _ = _ := by rw [Unitary.star_mul_self_of_mem u.property, one_mul, hp.isIdempotentElem.eq]
      · change star ((u : M) * p * star (u : M)) = (u : M) * p * star (u : M)
        simp only [star_mul, star_star, hp.isSelfAdjoint.star_eq, mul_assoc]
    · rw [htr, ← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul, hnull]
  have hfix (u : unitary M) : (u : M) * p * star (u : M) = p := by
    apply le_antisymm (hconj u)
    have h := star_right_conjugate_le_conjugate (hconj (star u)) (u : M)
    simp only [Unitary.coe_star, star_star, mul_assoc,
      Unitary.mul_star_self_of_mem u.property, mul_one] at h
    have huus : (u : M) * (star (u : M) * p) = p := by
      rw [← mul_assoc, Unitary.mul_star_self_of_mem u.property, one_mul]
    rw [huus] at h
    simpa only [mul_assoc] using h
  have hcomm (u : unitary M) : p * (u : M) = (u : M) * p := by
    have h := congrArg (fun a : M => a * (u : M)) (hfix u)
    simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using h.symm
  refine ⟨p, hp, ?_, hnull, hgreat⟩
  intro a
  obtain ⟨u, c, rfl, _⟩ := CStarAlgebra.exists_sum_four_unitary a
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul_comm, smul_mul_assoc, hcomm]

/-- Faithfulness on central projections suffices for a normal trace. -/
theorem normal_trace_faithful_of_center (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hcenter : ∀ p : M, IsStarProjection p → (∀ a : M, p * a = a * p) →
      τ p = 0 → p = 0) : ∀ a : M, τ (star a * a) = 0 → a = 0 := by
  obtain ⟨p, hp, hpc, hnull, hgreat⟩ := normal_trace_largest_null_projection e τ hτ htr
  have hp0 : p = 0 := hcenter p hp hpc hnull
  intro a ha
  let t : ℝ := ‖star a * a‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let c : M := t⁻¹ • (star a * a)
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr ht.le) (star_mul_self_nonneg a)
  have hcn : ‖c‖ ≤ 1 := by
    rw [show c = t⁻¹ • (star a * a) from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_one₀ ht).mpr (by dsimp [t]; linarith)
  have hc1 : c ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn
  have hτc : τ c = 0 := by
    rw [show c = t⁻¹ • (star a * a) from rfl, τ.map_smul_of_tower, ha, smul_zero]
  obtain ⟨q, hq, hτq⟩ := exists_null_support_projection e τ hτ hc0 hc1 hτc
  have hq0 : q = 0 := le_antisymm (hp0 ▸ hgreat q hq.proj hτq) hq.proj.nonneg
  have hc : c = 0 := by simpa only [hq0, zero_mul] using hq.left.symm
  have haa : star a * a = 0 := (smul_eq_zero.mp hc).resolve_left (inv_ne_zero ht.ne')
  apply norm_eq_zero.mp
  have hn := congrArg norm haa
  rw [CStarRing.norm_star_mul_self, norm_zero] at hn
  nlinarith [norm_nonneg a]

end KadisonRingrose
end BoundedHochschild

end

end OAI
