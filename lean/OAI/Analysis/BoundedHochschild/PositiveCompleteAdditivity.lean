import OAI.Analysis.BoundedHochschild.PositiveCompression

namespace OAI

/-!
# Complete additivity implies normality for positive functionals

The positive-functional case of Takesaki's criterion, as proved in Ringrose,
*Lectures on the trace in a finite von Neumann algebra*, Lemmas 4.1--4.3.
Only this case is needed for the normal-state orbit in the trace construction.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma positiveFunctional_zero_of_one_zero (ψ : M →ₚ[ℂ] ℂ) (hψ : ψ 1 = 0) :
    positiveFunctionalCLM ψ = 0 := by
  ext a
  change ψ a = 0
  have h := PositiveLinearMap.norm_map_star_mul_sq_le ψ (1 : M) a
  simp only [star_one, one_mul, hψ, norm_zero, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ψ a)])

lemma exists_normal_positive_larger_on_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {E : M} (hE : IsStarProjection E) (hE0 : E ≠ 0) (c : ℝ) :
    ∃ φ : M →ₚ[ℂ] ℂ, TraceInPredual e φ ∧ c < (φ E).re := by
  obtain ⟨ρ, hρ, _, hρE, _⟩ := exists_normal_state_on_projection e hE hE0
  let C : ℝ := max c 0 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let φ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (C : ℂ) • ρ.toLinearMap
      monotone' := fun _ _ hab => mul_le_mul_of_nonneg_left (ρ.monotone hab)
        (Complex.zero_le_real.mpr hC) }
  refine ⟨φ, ?_, ?_⟩
  · have hφ : positiveFunctionalCLM φ = (C : ℂ) • positiveFunctionalCLM ρ := rfl
    apply (mem_normalDual e (positiveFunctionalCLM φ)).mp
    rw [hφ]
    exact (normalDual e).smul_mem _ ((mem_normalDual e (positiveFunctionalCLM ρ)).mpr hρ)
  · change c < ((C : ℂ) * ρ E).re
    rw [hρE, mul_one, Complex.ofReal_re]
    dsimp [C]
    linarith [le_max_left c 0]

/-- A positive completely additive functional is normal. -/
theorem positive_normal_of_completelyAdditive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : CompletelyAdditive (positiveFunctionalCLM ψ)) :
    TraceInPredual e ψ := by
  classical
  let χ := positiveSingularPart e ψ
  have hχeq : positiveFunctionalCLM χ =
      positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) :=
    positiveSingularPart_eq e ψ
  have hχadd : CompletelyAdditive (positiveFunctionalCLM χ) := by
    rw [hχeq]
    exact hψ.sub (normal_completelyAdditive e (scalarNormalPart_mem e _))
  have hχsing : scalarNormalPart e (positiveFunctionalCLM χ) = 0 := by
    rw [hχeq, map_sub, scalarNormalPart_fixes e (scalarNormalPart_mem e _), sub_self]
  have hχzero : positiveFunctionalCLM χ = 0 := by
    by_contra hχne
    have hχ1 : χ 1 ≠ 0 := fun hz => hχne (positiveFunctional_zero_of_one_zero χ hz)
    obtain ⟨E, hE, hχE, hfaith⟩ := exists_additive_positive_support e χ hχadd
    have hE0 : E ≠ 0 := by
      intro hE0
      apply hχ1
      rw [← hχE, hE0, map_zero]
    obtain ⟨φ, hφ, hlarge⟩ := exists_normal_positive_larger_on_projection e hE hE0 (χ E).re
    let F := positiveFunctionalCLM φ - positiveFunctionalCLM χ
    have hF : CompletelyAdditive F := (normal_completelyAdditive e
      ((mem_normalDual e (positiveFunctionalCLM φ)).mpr hφ)).sub hχadd
    obtain ⟨p, hp, hpE, hEp, hnonneg⟩ := exists_nonnegative_projection_corner e F hF hE
    have hFE : 0 < (F E).re := by
      change 0 < (φ E - χ E).re
      rw [Complex.sub_re]
      exact sub_pos.mpr hlarge
    have hp0 : p ≠ 0 := by
      intro hp0
      rw [hp0, map_zero, Complex.zero_re] at hEp
      linarith
    have hdom : ∀ q : M, IsStarProjection q → q ≤ p → χ q ≤ φ q := by
      intro q hq hqp
      apply sub_nonneg.mp
      apply Complex.nonneg_iff.mpr
      constructor
      · exact hnonneg q hq hqp
      · have hχq : (χ q).im = 0 := (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
          (hq.isSelfAdjoint.map χ)
        have hφq : (φ q).im = 0 := (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
          (hq.isSelfAdjoint.map φ)
        simp only [Complex.sub_im, hφq, hχq, sub_self]
    have hn := compression_normal_of_projection_dominance e hp χ φ hφ hdom
    have hpnull := singular_zero_of_normal_compression e hp χ hχsing hn
    exact hp0 (hfaith p hp hpE hpnull)
  have hfix : scalarNormalPart e (positiveFunctionalCLM ψ) = positiveFunctionalCLM ψ := by
    rw [hχeq] at hχzero
    exact (sub_eq_zero.mp hχzero).symm
  apply (mem_normalDual e (positiveFunctionalCLM ψ)).mp
  rw [← hfix]
  exact scalarNormalPart_mem e _

end KadisonRingrose
end BoundedHochschild

end

end OAI
