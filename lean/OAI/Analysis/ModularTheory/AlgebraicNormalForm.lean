import OAI.Analysis.ModularTheory.FiniteAdjoint

namespace OAI

/-! Normal ordering of algebraic modular-core elements. The finite sums here
are taken in the concrete regular representation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private abbrev translation (t : ℝ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  (modularLpTranslateEquiv (H := H) volume t :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))

omit [CompleteSpace H] in
private lemma translation_add (s t : ℝ) :
    translation (H := H) s * translation t = translation (s + t) := by
  apply ContinuousLinearMap.ext
  intro f
  exact modularLpTranslate_comp volume s t f

omit [CompleteSpace H] in
private lemma translation_zero : translation (H := H) 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact modularLpTranslate_zero volume f

private lemma translation_star (t : ℝ) :
    star (translation (H := H) t) = translation (-t) := by
  exact LinearIsometryEquiv.star_eq_symm _

private lemma translation_coefficient (S : StandardModularData H)
    (t : ℝ) (a : H →L[ℂ] H) :
    translation t * modularLpRepresentation volume S.D a =
      modularLpRepresentation volume S.D (S.sigma t a) * translation t := by
  have he : translation t * modularLpRepresentation volume S.D a * translation (-t) =
      modularLpRepresentation volume S.D (S.sigma t a) := by
    apply ContinuousLinearMap.ext
    intro f
    exact modularLp_covariance volume S.D t a f
  have h := congrArg (fun T => T * translation (H := H) t) he
  simpa only [mul_assoc, translation_add, neg_add_cancel, translation_zero, mul_one] using h

def modularCoreMonomial (S : StandardModularData H) (p : S.M.toStarSubalgebra × ℝ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  modularLpRepresentation volume S.D p.1 * translation p.2

private def normalSpan (S : StandardModularData H) :=
  Submodule.span ℂ (Set.range (modularCoreMonomial S))

private lemma monomial_one (S : StandardModularData H) :
    modularCoreMonomial S (1, 0) = 1 := by
  simp [modularCoreMonomial, translation_zero]

private lemma monomial_mul (S : StandardModularData H)
    (p q : S.M.toStarSubalgebra × ℝ) :
    modularCoreMonomial S p * modularCoreMonomial S q =
      modularCoreMonomial S
        (⟨(p.1 : H →L[ℂ] H) * S.sigma p.2 q.1,
          mul_mem p.1.property (S.sigma_mem p.2 q.1.property)⟩, p.2 + q.2) := by
  dsimp [modularCoreMonomial]
  rw [map_mul]
  calc
    _ = modularLpRepresentation volume S.D p.1 *
        (translation p.2 * modularLpRepresentation volume S.D q.1) * translation q.2 := by
      simp only [mul_assoc]
    _ = _ := by rw [translation_coefficient]; simp only [mul_assoc, translation_add]

private lemma monomial_star (S : StandardModularData H)
    (p : S.M.toStarSubalgebra × ℝ) :
    star (modularCoreMonomial S p) = modularCoreMonomial S
      (⟨S.sigma (-p.2) (star (p.1 : H →L[ℂ] H)),
        S.sigma_mem (-p.2) (star_mem p.1.property)⟩, -p.2) := by
  dsimp [modularCoreMonomial]
  rw [star_mul, ← map_star, translation_star, translation_coefficient]

private lemma normalSpan_mul (S : StandardModularData H)
    {P Q : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)}
    (hP : P ∈ normalSpan S) (hQ : Q ∈ normalSpan S) : P * Q ∈ normalSpan S := by
  induction hQ using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨q, rfl⟩ := hq
      induction hP using Submodule.span_induction with
      | mem p hp =>
          obtain ⟨p, rfl⟩ := hp
          rw [monomial_mul]
          exact Submodule.subset_span ⟨_, rfl⟩
      | zero => simpa only [zero_mul] using (normalSpan S).zero_mem
      | add p q hp hq ihp ihq =>
          simpa only [add_mul] using (normalSpan S).add_mem ihp ihq
      | smul c p hp ih => simpa only [smul_mul_assoc] using (normalSpan S).smul_mem c ih
  | zero => simpa only [mul_zero] using (normalSpan S).zero_mem
  | add p q hp hq ihp ihq =>
      simpa only [mul_add] using (normalSpan S).add_mem ihp ihq
  | smul c p hp ih => simpa only [mul_smul_comm] using (normalSpan S).smul_mem c ih

private lemma normalSpan_star (S : StandardModularData H)
    {P : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)}
    (hP : P ∈ normalSpan S) : star P ∈ normalSpan S := by
  induction hP using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨p, rfl⟩ := hp
      rw [monomial_star]
      exact Submodule.subset_span ⟨_, rfl⟩
  | zero =>
      rw [star_zero (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))]
      exact (normalSpan S).zero_mem
  | add p q hp hq ihp ihq =>
      rw [star_add p q]
      exact (normalSpan S).add_mem ihp ihq
  | smul c p hp ih => simpa only [star_smul] using (normalSpan S).smul_mem (star c) ih

private def normalAlgebra (S : StandardModularData H) :
    StarSubalgebra ℂ (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) where
  carrier := normalSpan S
  zero_mem' := (normalSpan S).zero_mem
  one_mem' := by rw [← monomial_one S]; exact Submodule.subset_span ⟨_, rfl⟩
  add_mem' := (normalSpan S).add_mem
  mul_mem' := normalSpan_mul S
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one, ← monomial_one S]
    exact (normalSpan S).smul_mem c (Submodule.subset_span ⟨_, rfl⟩)
  star_mem' := normalSpan_star S

theorem algebraicModularCore_normal_form (S : StandardModularData H)
    (P : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hP : P ∈ algebraicModularCore (volume : Measure ℝ) S) :
    ∃ c : (S.M.toStarSubalgebra × ℝ) →₀ ℂ,
      (c.sum fun p z => z • modularCoreMonomial S p) = P := by
  have hle : algebraicModularCore (volume : Measure ℝ) S ≤ normalAlgebra S := by
    apply StarAlgebra.adjoin_le
    rintro T (⟨a, rfl⟩ | ⟨t, rfl⟩)
    · change modularLpRepresentation volume S.D a ∈ normalSpan S
      have he : modularCoreMonomial S (a, 0) = modularLpRepresentation volume S.D a := by
        rw [modularCoreMonomial, translation_zero, mul_one]
      rw [← he]
      exact Submodule.subset_span ⟨_, rfl⟩
    · change translation t ∈ normalSpan S
      have he : modularCoreMonomial S (1, t) = translation (H := H) t := by
        simp [modularCoreMonomial]
      rw [← he]
      exact Submodule.subset_span ⟨_, rfl⟩
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp (hle hP)

end WeakPureInfiniteness

end

end OAI
