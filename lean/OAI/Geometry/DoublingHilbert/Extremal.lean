import Mathlib

namespace OAI

/-! Compact lexicographic extrema and quantitative second-moment estimates. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
/-- Near a compact lexicographic maximum, the second coordinate has a uniform upper bound. -/
theorem near_lexicographic_maximum
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A B : ℝ}
    (hfirst : ∀ p ∈ K, p.1 ≤ A)
    (hsecond : ∀ p ∈ K, p.1 = A → p.2 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, A - δ < p.1 → p.2 ≤ B + ε := by
  let bad : Set (ℝ × ℝ) := K ∩ {p | B + ε ≤ p.2}
  have hbcompact : IsCompact bad :=
    hK.inter_right (isClosed_le continuous_const continuous_snd)
  by_cases hb : bad.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hbcompact.exists_isMaxOn hb continuous_fst.continuousOn
    have hpA : p.1 < A := by
      apply lt_of_le_of_ne (hfirst p hp.1)
      intro heq
      have hpB := hsecond p hp.1 heq
      have hpB' : B + ε ≤ p.2 := hp.2
      linarith
    refine ⟨A - p.1, sub_pos.mpr hpA, ?_⟩
    intro q hq hqA
    by_contra hqB
    have hqb : q ∈ bad := ⟨hq, (not_le.mp hqB).le⟩
    have := hmax hqb
    dsimp at this
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p hp _
    by_contra h
    exact hb ⟨p, hp, (not_le.mp h).le⟩


/-- A nonempty compact set has a lexicographic maximum. -/
theorem exists_lexicographic_maximum {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ A B : ℝ, (A, B) ∈ K ∧
      (∀ p ∈ K, p.1 ≤ A) ∧ (∀ p ∈ K, p.1 = A → p.2 ≤ B) := by
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
  let fiber : Set (ℝ × ℝ) := K ∩ {q | q.1 = p.1}
  have hc : IsCompact fiber :=
    hK.inter_right (isClosed_eq continuous_fst continuous_const)
  obtain ⟨q, hq, hqmax⟩ := hc.exists_isMaxOn ⟨p, hp, rfl⟩ continuous_snd.continuousOn
  refine ⟨p.1, q.2, ?_, hmax, ?_⟩
  · have hqfst : q.1 = p.1 := hq.2
    simpa only [← hqfst, Prod.eta] using hq.1
  · intro r hr hrp
    exact hqmax ⟨hr, hrp⟩

/-- An affine barrier bounds the second coordinate in terms of the first-coordinate deficit. -/
theorem lexicographic_affine_barrier
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A B M : ℝ}
    (hfirst : ∀ p ∈ K, p.1 ≤ A)
    (hsecond : ∀ p ∈ K, p.1 = A → p.2 ≤ B)
    (hbound : ∀ p ∈ K, p.2 ≤ M) (hB : 0 ≤ B) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1) := by
  obtain ⟨δ, hδ, hnear⟩ := near_lexicographic_maximum hK hfirst hsecond hε
  refine ⟨M / δ, div_nonneg hM hδ.le, ?_⟩
  intro p hp
  have hdef : 0 ≤ A - p.1 := sub_nonneg.mpr (hfirst p hp)
  by_cases hclose : A - δ < p.1
  · exact (hnear p hp hclose).trans (le_add_of_nonneg_right (by positivity))
  · have hgap : δ ≤ A - p.1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hgap (div_nonneg hM hδ.le)
    have heq : M / δ * δ = M := div_mul_cancel₀ _ hδ.ne'
    have hpm := hbound p hp
    linarith

open MeasureTheory
open scoped BigOperators

section Moments

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The variance identity over an arbitrary probability space. -/
theorem integral_variance_identity {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) :
    (∫ x, ‖G x - a‖ ^ 2 ∂μ) = (∫ x, ‖G x‖ ^ 2 ∂μ) - ‖a‖ ^ 2 -
      2 * inner ℝ a ((∫ x, G x ∂μ) - a) := by
  have hpoint (x : X) : ‖G x - a‖ ^ 2 =
      ‖G x‖ ^ 2 - 2 * inner ℝ a (G x) + ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm (G x) a]
  simp_rw [hpoint]
  rw [integral_add (f := fun x => ‖G x‖ ^ 2 - 2 * inner ℝ a (G x))
      (g := fun _ => ‖a‖ ^ 2) (hG2.sub ((hG.const_inner a).const_mul 2)) (integrable_const _),
    integral_sub hG2 ((hG.const_inner a).const_mul 2), integral_const_mul,
    integral_inner hG a]
  simp only [integral_const, probReal_univ, one_smul, inner_sub_right,
    real_inner_self_eq_norm_sq]
  ring

omit [CompleteSpace E] in
theorem integrable_norm_sub_sq {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) :
    Integrable (fun x => ‖G x - a‖ ^ 2) μ := by
  simp_rw [norm_sub_sq_real]
  exact (hG2.sub ((hG.inner_const a).const_mul 2)).add (integrable_const _)

/-- Small moment error and an upper second moment force small mean-square variation. -/
theorem variance_le_of_moments {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) {M : ℝ}
    (hM : (∫ x, ‖G x‖ ^ 2 ∂μ) ≤ M) :
    (∫ x, ‖G x - a‖ ^ 2 ∂μ) ≤ M - ‖a‖ ^ 2 +
      2 * ‖a‖ * ‖(∫ x, G x ∂μ) - a‖ := by
  rw [integral_variance_identity hG hG2 a]
  have h := real_inner_le_norm (-a) ((∫ x, G x ∂μ) - a)
  simp only [inner_neg_left, norm_neg] at h
  nlinarith

/-- Discarding the nonnegative variance bounds the second-moment deficit. -/
theorem mean_deficit_le {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) (A : ℝ) :
    A - (∫ x, ‖G x‖ ^ 2 ∂μ) ≤ A - ‖a‖ ^ 2 +
      2 * ‖a‖ * ‖(∫ x, G x ∂μ) - a‖ := by
  have hnonneg : 0 ≤ (∫ x, ‖G x - a‖ ^ 2 ∂μ) := integral_nonneg fun _ => sq_nonneg _
  rw [integral_variance_identity hG hG2 a] at hnonneg
  have h := real_inner_le_norm (-a) ((∫ x, G x ∂μ) - a)
  simp only [inner_neg_left, norm_neg] at h
  nlinarith

/-- Integrated affine barrier; unlike a limsup statement, this keeps all quantitative data. -/
theorem integral_second_le_barrier {K : Set (ℝ × ℝ)} {s t : X → ℝ}
    (hs : Integrable s μ) (ht : Integrable t μ)
    (hvalues : ∀ᵐ x ∂μ, (s x, t x) ∈ K) {A B ε C : ℝ}
    (hbarrier : ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1)) :
    (∫ x, t x ∂μ) ≤ B + ε + C * (A - ∫ x, s x ∂μ) := by
  have hi : Integrable (fun x => B + ε + C * (A - s x)) μ :=
    (integrable_const _).add (((integrable_const _).sub hs).const_mul _)
  have hle := integral_mono_ae ht hi (hvalues.mono fun x hx => hbarrier _ hx)
  simpa only [integral_add (f := fun _ => B + ε) (g := fun x => C * (A - s x))
      (integrable_const _) (((integrable_const _).sub hs).const_mul _),
    integral_const_mul, integral_sub (integrable_const _) hs, integral_const,
    probReal_univ, smul_eq_mul, one_mul] using hle

/-- The hard lexicographic energy step, before substituting the geometric moment bounds. -/
theorem vertical_variance_bound
    {G H : X → E} (hG : Integrable G μ) (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ)
    (hH : Integrable H μ) (hH2 : Integrable (fun x => ‖H x‖ ^ 2) μ)
    {K : Set (ℝ × ℝ)} (hvalues : ∀ᵐ x ∂μ, (‖G x‖ ^ 2, ‖H x‖ ^ 2) ∈ K)
    {A B ε C D : ℝ} (hC : 0 ≤ C)
    (hbarrier : ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1))
    (u v : E) (hu : ‖u‖ ≤ D) (hv : ‖v‖ ≤ D) :
    (∫ x, ‖H x - v‖ ^ 2 ∂μ) ≤ B - ‖v‖ ^ 2 + ε +
      C * (A - ‖u‖ ^ 2 + 2 * D * ‖(∫ x, G x ∂μ) - u‖) +
      2 * D * ‖(∫ x, H x ∂μ) - v‖ := by
  have hb := integral_second_le_barrier hG2 hH2 hvalues hbarrier
  have hvb := variance_le_of_moments hH hH2 v hb
  have hdef := mean_deficit_le hG hG2 u A
  have hdu : 2 * ‖u‖ * ‖(∫ x, G x ∂μ) - u‖ ≤
      2 * D * ‖(∫ x, G x ∂μ) - u‖ := by
    gcongr
  have hdv : 2 * ‖v‖ * ‖(∫ x, H x ∂μ) - v‖ ≤
      2 * D * ‖(∫ x, H x ∂μ) - v‖ := by
    gcongr
  have hdef' : A - (∫ x, ‖G x‖ ^ 2 ∂μ) ≤
      A - ‖u‖ ^ 2 + 2 * D * ‖(∫ x, G x ∂μ) - u‖ := by linarith
  have hdef'' := mul_le_mul_of_nonneg_left hdef' hC
  linarith

end Moments


end DoublingHilbert

end OAI
