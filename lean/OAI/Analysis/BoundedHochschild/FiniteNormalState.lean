import OAI.Analysis.BoundedHochschild.FiniteTraceCover
import OAI.Analysis.BoundedHochschild.FiniteCentralDecomposition

namespace OAI

/-!
# Normal states and the remaining tracial averaging step

A normal state faithful on central projections is faithful on positive
central elements. The property passes to its actual central corner.
Composing such a state with a faithful normal positive central averaging
map gives a faithful normal tracial state. Constructing that map from
finiteness is a separate remaining theorem; no such map is postulated here.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A positive functional vanishing on a positive contraction annihilates its left multiples. -/
lemma positive_contraction_zero_mul (ψ : M →ₚ[ℂ] ℂ) {c : M}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hψc : ψ c = 0) (b : M) : ψ (c * b) = 0 := by
  have hcc : c * c ≤ c := by
    simpa only [pow_two, pow_one] using
      CStarAlgebra.pow_antitone hc1 hc0 (by omega : 1 ≤ 2)
  have hψcc : ψ (c * c) = 0 := le_antisymm
    ((ψ.monotone hcc).trans_eq hψc)
    (ψ.map_nonneg hc0.isSelfAdjoint.mul_self_nonneg)
  have h := PositiveLinearMap.norm_map_star_mul_sq_le ψ c b
  rw [hc0.isSelfAdjoint.star_eq, hψcc, norm_zero, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ψ (c * b))])

/-- The support projection of a null positive contraction is null for a normal functional. -/
lemma exists_null_support_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) {c : M}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hψc : ψ c = 0) :
    ∃ r : M, IsSupportProjection c r ∧ ψ r = 0 := by
  obtain ⟨r, hr, ht⟩ := HochschildSakai.exists_support_contraction e c hc0 hc1
  have hpow (n : ℕ) : ψ ((1 - c) ^ n) = ψ 1 := by
    induction n with
    | zero => simp only [pow_zero]
    | succ n ih =>
      rw [pow_succ', sub_mul, one_mul, map_sub,
        positive_contraction_zero_mul ψ hc0 hc1 hψc, sub_zero, ih]
  have hzero (n : ℕ) : ψ (1 - (1 - c) ^ n) = 0 := by
    rw [map_sub, hpow, sub_self]
  refine ⟨r, hr, ?_⟩
  have hl := trace_predual_tendsto e ψ hψ ht
  have heq : (fun n : ℕ => ψ (1 - (1 - c) ^ n)) = (fun _ : ℕ => (0 : ℂ)) := funext hzero
  rw [heq] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

/-- Normality upgrades faithfulness on central projections to positive central elements. -/
theorem normal_state_faithful_on_positive_center (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hfaith : ∀ p : M, IsStarProjection p → (∀ a : M, p * a = a * p) → ψ p = 0 → p = 0)
    {a : M} (ha : 0 ≤ a) (hcentral : ∀ b : M, a * b = b * a) (hψa : ψ a = 0) :
    a = 0 := by
  let t : ℝ := ‖a‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let c : M := t⁻¹ • a
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr ht.le) ha
  have hcn : ‖c‖ ≤ 1 := by
    rw [show c = t⁻¹ • a from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_one₀ ht).mpr (by dsimp [t]; linarith)
  have hc1 : c ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn
  have hψc : ψ c = 0 := by
    rw [show c = t⁻¹ • a from rfl, ψ.map_smul_of_tower, hψa, smul_zero]
  obtain ⟨r, hr, hψr⟩ := exists_null_support_projection e ψ hψ hc0 hc1 hψc
  have hrc : ∀ b : M, r * b = b * r := by
    intro b
    apply (hr.commute hc0.isSelfAdjoint ?_).eq
    change (t⁻¹ • a) * b = b * (t⁻¹ • a)
    rw [smul_mul_assoc, mul_smul_comm, hcentral]
  have hr0 : r = 0 := hfaith r hr.proj hrc hψr
  have hc : c = 0 := by simpa only [hr0, zero_mul] using hr.left.symm
  exact (smul_eq_zero.mp hc).resolve_left (inv_ne_zero ht.ne')

/-- A state faithful on the central subprojections of `p` induces a normal state
faithful on all central projections of the actual corner `pMp`. -/
theorem central_faithful_state_on_corner (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p)
    (hstate : HasCentralFaithfulNormalState e p) :
    ∃ ψ : Corner p hp →ₚ[ℂ] ℂ,
      TraceInPredual (cornerPredualEquiv p hp e) ψ ∧ ψ 1 = 1 ∧
      ∀ q : Corner p hp, IsStarProjection q →
        (∀ a : Corner p hp, q * a = a * q) → ψ q = 0 → q = 0 := by
  obtain ⟨ψ, hψ, _, hψp, hfaith⟩ := hstate
  let τ := cornerTrace p hp ψ
  have hτ (a : Corner p hp) : τ a = ψ (a : M) := by
    simp only [τ, cornerTrace_apply, hψp, Complex.one_re, Complex.ofReal_one, inv_one, one_mul]
  refine ⟨τ, cornerTrace_normal p hp e ψ hψ, ?_, ?_⟩
  · simpa only [hτ, corner_coe_one] using hψp
  · intro q hq hqc hzero
    apply Subtype.ext
    exact hfaith (q : M) (corner_projection_coe p hp hq)
      (centralCorner_central hp hc q hqc) (corner_projection_le p hp hq)
      (by rwa [hτ] at hzero)

/-- Actual normal central averaging data convert a center-faithful state into a
faithful normal trace. The existence of this averaging map is the remaining
finite-algebra input. -/
theorem tracial_state_of_normal_center_average (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) (hψ1 : ψ 1 = 1)
    (hfaith : ∀ p : M, IsStarProjection p → (∀ a : M, p * a = a * p) → ψ p = 0 → p = 0)
    (E : M →L[ℂ] M) (hEnormal : HasPreadjoint e E)
    (hEpositive : ∀ a : M, 0 ≤ a → 0 ≤ E a) (hE1 : E 1 = 1)
    (hEcentral : ∀ a b : M, E a * b = b * E a)
    (hEtracial : ∀ a b : M, E (a * b) = E (b * a))
    (hEfaithful : ∀ a : M, E (star a * a) = 0 → a = 0) :
    ∃ τ : M →ₚ[ℂ] ℂ, TraceInPredual e τ ∧ τ 1 = 1 ∧
      (∀ a b : M, τ (a * b) = τ (b * a)) ∧
      (∀ a : M, τ (star a * a) = 0 → a = 0) := by
  let τ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := ψ.toLinearMap.comp E.toLinearMap
      monotone' := by
        change Monotone (ψ.toLinearMap.comp E.toLinearMap)
        apply (monotone_iff_map_nonneg _).mpr
        intro a ha
        exact ψ.map_nonneg (hEpositive a ha) }
  have hτ (a : M) : τ a = ψ (E a) := rfl
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hψ
    obtain ⟨w, hw⟩ := hEnormal z
    exact ⟨w, fun a => by rw [hτ, hz, hw]⟩
  · rw [hτ, hE1, hψ1]
  · intro a b
    rw [hτ, hτ, hEtracial]
  · intro a ha
    apply hEfaithful a
    exact normal_state_faithful_on_positive_center e ψ hψ hfaith
      (hEpositive _ (star_mul_self_nonneg a)) (hEcentral _) ha

end KadisonRingrose
end BoundedHochschild

end

end OAI
