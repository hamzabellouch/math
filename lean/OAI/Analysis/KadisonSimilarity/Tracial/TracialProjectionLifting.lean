import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerActions
import OAI.Analysis.KadisonSimilarity.Tracial.TracialSmallCornerTransfer

namespace OAI

/-! Projection lifting in a tracial ultrapower, using only the scalar
spectral rounding estimate. The subsequent trace cutoff uses the strict
gap between the desired trace and the coordinate trace bound. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower TracialUltrapower Filter
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- Blackadar, I.6.2.4 and I.9.2.1(iv): bounded Borel functional calculus
with the cutoff at 1/2. The scalar estimate is
`|x - 1_[1/2,∞)(x)| ≤ 2 |x²-x|`. This predicate is used only for the
fixed finite von Neumann algebra, not for arbitrary C-star algebras. -/
def SpectralProjectionRoundingInput : Prop :=
  ∀ a : A, IsSelfAdjoint a → ∃ p : A, IsStarProjection p ∧
    ‖τ.toPreGNS (p - a)‖ ≤ 2 * ‖τ.toPreGNS (a * a - a)‖

omit h1 ω htr [PartialOrder A] [StarOrderedRing A] in
theorem norm_le_one_of_star_projection (p : A) (hp : IsStarProjection p) : ‖p‖ ≤ 1 :=
  norm_le_one_of_initial_projection p p hp (by
    rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq])

/-- Every quotient projection has a representative consisting of actual
projections. Rounding is the sole spectral-calculus prerequisite. -/
theorem exists_projection_representative (rounding : SpectralProjectionRoundingInput τ)
    (e : Ultrapower τ h1 ω htr) (he : IsStarProjection e) :
    ∃ p : ℕ →ᵇ A, (∀ i, IsStarProjection (p i)) ∧ quotientHom τ h1 ω htr p = e := by
  classical
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e
  let b : ℕ →ᵇ A := (1 / 2 : ℂ) • (a + star a)
  have hb : ∀ i, IsSelfAdjoint (b i) := by
    intro i
    change star (b i) = b i
    simp [b, star_smul, star_add, add_comm]
  have hbe : quotientHom τ h1 ω htr b = e := by
    change quotientHom τ h1 ω htr ((1 / 2 : ℂ) • (a + star a)) = e
    have ha' : quotientHom τ h1 ω htr a = e := ha
    simp only [map_smul, map_add, map_star, ha', he.isSelfAdjoint.star_eq]
    module
  choose p hp hpa using fun i => rounding (b i) (hb i)
  let p' : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete p 1
    (fun i => norm_le_one_of_star_projection (p i) (hp i))
  have hdefect : Tendsto (fun i => ‖τ.toPreGNS ((b i) * (b i) - b i)‖)
      (ω : Filter ℕ) (𝓝 0) := by
    have hzero : quotientHom τ h1 ω htr (b * b - b) = 0 := by
      rw [map_sub, map_mul, hbe, he.isIdempotentElem.eq, sub_self]
    have hmem : b * b - b ∈ ideal τ h1 ω htr :=
      (Ideal.Quotient.eq_zero_iff_mem).mp hzero
    exact (mem_nullSubmodule _ _ _).mp hmem
  have hnull : p' - b ∈ ideal τ h1 ω htr := by
    apply (mem_nullSubmodule _ _ _).mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i => hpa i)
    simpa using hdefect.const_mul 2
  refine ⟨p', hp, ?_⟩
  have hzero : quotientHom τ h1 ω htr (p' - b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hnull
  rw [map_sub, hbe, sub_eq_zero] at hzero
  exact hzero

/-- A strict trace gap permits uniform coordinate bounds after changing a
representative on a set outside the ultrafilter. -/
theorem exists_projection_representative_trace_le
    (rounding : SpectralProjectionRoundingInput τ)
    (e : Ultrapower τ h1 ω htr) (he : IsStarProjection e)
    {s : ℝ} (hs : (quotientTrace τ h1 ω htr e).re < s) :
    ∃ p : ℕ →ᵇ A, (∀ i, IsStarProjection (p i)) ∧
      (∀ i, (τ (p i)).re ≤ s) ∧ quotientHom τ h1 ω htr p = e := by
  classical
  obtain ⟨p, hp, hpe⟩ := exists_projection_representative τ h1 ω htr rounding e he
  have ht : Tendsto (fun i => (τ (p i)).re) (ω : Filter ℕ)
      (𝓝 (quotientTrace τ h1 ω htr e).re) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_sequenceTrace τ h1 ω p)
    rw [← hpe]
    exact h
  have hgood : ∀ᶠ i in (ω : Filter ℕ), (τ (p i)).re ≤ s :=
    (ht.eventually_lt_const hs).mono (fun _ hi => hi.le)
  have hs0 : 0 ≤ s := by
    have hepos : 0 ≤ quotientTrace τ h1 ω htr e :=
      (quotientTrace τ h1 ω htr).map_nonneg he.nonneg
    exact (show 0 ≤ (quotientTrace τ h1 ω htr e).re from hepos.1).trans hs.le
  let q : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => if (τ (p i)).re ≤ s then p i else 0) 1 (by
      intro i
      split_ifs
      · exact norm_le_one_of_star_projection (p i) (hp i)
      · simp)
  have heq : ∀ᶠ i in (ω : Filter ℕ), q i = p i := by
    filter_upwards [hgood] with i hi
    change (if (τ (p i)).re ≤ s then p i else 0) = p i
    simp only [hi, ↓reduceIte]
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    change IsStarProjection (if (τ (p i)).re ≤ s then p i else 0)
    split_ifs
    · exact hp i
    · exact IsStarProjection.zero A
  · intro i
    change (τ (if (τ (p i)).re ≤ s then p i else 0)).re ≤ s
    split_ifs with hi
    · exact hi
    · simpa using hs0
  · have hnull : q - p ∈ ideal τ h1 ω htr := by
      apply (mem_nullSubmodule _ _ _).mpr
      apply tendsto_const_nhds.congr'
      filter_upwards [heq] with i hi
      simp only [BoundedContinuousFunction.sub_apply, hi, sub_self, map_zero, norm_zero]
    have hzero : quotientHom τ h1 ω htr (q - p) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hnull
    rwa [map_sub, hpe, sub_eq_zero] at hzero

end KadisonSimilarity

end

end OAI
