import OAI.Analysis.KadisonSimilarity.Tensor.InvariantForms
import OAI.Analysis.KadisonSimilarity.Tensor.StableMatrixStages
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Matrix.Basis

namespace OAI

/-!
# Matrix realization of the invariant-intertwiner argument

Finite coefficient forms are constructed from explicit Hilbert-space matrix
realizations. Normalized Hilbert--Schmidt inner products supply the matrix-unit
norms, while left matrix actions supply endpoint transfer. The sole invariant
theory input remains finite-dimensional Schur--Weyl spanning.
-/

noncomputable section
namespace KadisonSimilarity

variable {E F α : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [Fintype α] [DecidableEq α]

/-- Local geometric data of one full matrix stage in a tracial Hilbert space.
The maps and identities describe its normalized Hilbert--Schmidt realization;
no coefficient expansion or intertwiner classification is included. -/
structure MatrixHilbertStage where
  full : Matrix α α ℂ →ₗ[ℂ] E
  center : Matrix α α ℂ →ₗ[ℂ] F
  left : Matrix α α ℂ → (E →L[ℂ] E)
  inner_full : ∀ a b, inner ℂ (full a) (full b) =
    (Fintype.card α : ℂ)⁻¹ * Matrix.trace (star a * b)
  norm_center_le : ∀ a, ‖center a‖ ≤ ‖full a‖
  left_apply : ∀ a b, left a (full b) = full (a * b)
  left_adjoint : ∀ a, (left a).adjoint = left (star a)

omit [Fintype α] in
@[simp] theorem tensorMatrixUnit_eq_single (a b : α) :
    tensorMatrixUnit a b = Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [tensorMatrixUnit, Matrix.single_apply]
  simp only [eq_comm]

omit [Fintype α] in
@[simp] theorem star_tensorMatrixUnit (a b : α) :
    star (tensorMatrixUnit a b) = tensorMatrixUnit b a := by
  ext i j
  change star (tensorMatrixUnit a b j i) = tensorMatrixUnit b a i j
  simp only [tensorMatrixUnit, and_comm]
  split_ifs <;> simp

@[simp] theorem tensorMatrixUnit_mul (a b c : α) :
    tensorMatrixUnit a b * tensorMatrixUnit b c = tensorMatrixUnit a c := by
  simp only [tensorMatrixUnit_eq_single, Matrix.single_mul_single_same, one_mul]

@[simp] theorem trace_tensorMatrixUnit (a : α) :
    Matrix.trace (tensorMatrixUnit a a) = 1 := by
  rw [tensorMatrixUnit_eq_single, Matrix.trace_single_eq_same]

/-- Every realized matrix unit has the normalized Hilbert--Schmidt norm. -/
theorem MatrixHilbertStage.norm_full_matrixUnit [Nonempty α]
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (a b : α) :
    ‖R.full (tensorMatrixUnit a b)‖ = (Fintype.card α : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hs : ‖R.full (tensorMatrixUnit a b)‖ ^ 2 = (Fintype.card α : ℝ)⁻¹ := by
    rw [@norm_sq_eq_re_inner ℂ, R.inner_full, star_tensorMatrixUnit,
      tensorMatrixUnit_mul, trace_tensorMatrixUnit, mul_one]
    simp
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.rpow_nonneg hm.le _)).mp
  rw [hs, ← Real.rpow_mul_natCast hm.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg_one]

/-- Centering is contractive on the normalized matrix units. -/
theorem MatrixHilbertStage.norm_center_matrixUnit_le [Nonempty α]
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (a b : α) :
    ‖R.center (tensorMatrixUnit a b)‖ ≤ (Fintype.card α : ℝ) ^ (-(1 : ℝ) / 2) := by
  simpa only [R.norm_full_matrixUnit] using R.norm_center_le (tensorMatrixUnit a b)

/-- The test endpoint map is conjugate-linear because matrix star is. -/
def MatrixHilbertStage.testEndpoint
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) : Matrix α α ℂ →ₗ⋆[ℂ] E :=
  R.full.comp (starLinearEquiv ℂ).toLinearMap

def MatrixHilbertStage.testLetter
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F) :
    Matrix α α ℂ →ₗ⋆[ℂ] F := J.toLinearMap.comp R.center

variable {k l : ℕ}

def MatrixHilbertStage.form
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) :
    MultilinearMap ℂ (fun _ : Option (Fin k ⊕ Fin l) => Matrix α α ℂ) ℂ :=
  invariantStageForm Y Ω R.testEndpoint R.center (R.testLetter J)

omit [DecidableEq α] in
@[simp] theorem MatrixHilbertStage.form_apply
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ) :
    R.form J Ω Y v =
      inner ℂ (endpointWord (R.full (star (v none)))
        (fun j => J (R.center (v (some (Sum.inr j))))))
      (Y (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))) := rfl

/-- Isometric word covariance gives precisely the finite conjugation invariance
required by Schur--Weyl, with no invariance of the coefficient form assumed. -/
theorem MatrixHilbertStage.form_invariant_of_word_covariance
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (Wk : Matrix.unitaryGroup α ℂ → EndpointTensor E F k →ₗᵢ[ℂ] EndpointTensor E F k)
    (Wl : Matrix.unitaryGroup α ℂ → EndpointTensor E F l →ₗᵢ[ℂ] EndpointTensor E F l)
    (hY : ∀ u, Y.comp (Wk u).toContinuousLinearMap = (Wl u).toContinuousLinearMap.comp Y)
    (hsource : ∀ (u : Matrix.unitaryGroup α ℂ) (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
      endpointWord Ω (fun i => R.center ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ))) =
        Wk u (endpointWord Ω (fun i => R.center (v (some (Sum.inl i))))))
    (htest : ∀ (u : Matrix.unitaryGroup α ℂ) (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
      endpointWord (R.full (star ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ))))
        (fun j => J (R.center ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ)))) =
        Wl u (endpointWord (R.full (star (v none)))
          (fun j => J (R.center (v (some (Sum.inr j))))))) :
    UnitaryConjugationInvariant (R.form J Ω Y) := by
  intro u v
  simp only [R.form_apply]
  rw [hsource u v, htest u v]
  have heq := congrArg (fun L : EndpointTensor E F k →L[ℂ] EndpointTensor E F l =>
    L (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))) (hY u)
  change Y (Wk u _) = Wl u (Y _) at heq
  rw [heq, (Wl u).inner_map_map]

/-- The matrix-unit endpoint estimate follows from the actual left matrix
projection and normalized Hilbert--Schmidt norms. -/
theorem MatrixHilbertStage.form_matrixUnit_bound [Nonempty α]
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (hΩ : R.full 1 = Ω)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hY : ∀ a : Matrix α α ℂ, Y.comp (endpointHeadAction (n := k) (R.left a)) =
      (endpointHeadAction (n := l) (R.left a)).comp Y)
    (labels : Option (Fin k ⊕ Fin l) → α) (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) :
    ‖R.form J Ω Y (permutationTest labels π)‖ ≤
      ‖Y‖ * (Fintype.card α : ℝ) ^ (-1 - ((k : ℝ) + l) / 2) := by
  let v := permutationTest labels π
  let b := labels (π none)
  let q := R.left (tensorMatrixUnit b b)
  let a := R.full (star (v none))
  let x : Fin k → F := fun i => R.center (v (some (Sum.inl i)))
  let z : Fin l → F := fun j => J (R.center (v (some (Sum.inr j))))
  have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hqa : q.adjoint a = a := by
    dsimp [q, a, v, permutationTest, b]
    rw [R.left_adjoint, star_tensorMatrixUnit, star_tensorMatrixUnit,
      R.left_apply, tensorMatrixUnit_mul]
  have hqΩ : q Ω = R.full (tensorMatrixUnit b b) := by
    rw [← hΩ]
    exact (R.left_apply _ _).trans (by rw [mul_one])
  have ht := endpoint_coefficient_transfer Y q (hY (tensorMatrixUnit b b)) Ω a x z
  rw [hqa] at ht
  have htest : ‖endpointWord a z‖ ≤
      (Fintype.card α : ℝ) ^ (-((l : ℝ) + 1) / 2) := by
    apply norm_endpointWord_le_matrix_units a z _ hm
    · dsimp [a, v, permutationTest]
      rw [star_tensorMatrixUnit, R.norm_full_matrixUnit]
    · intro j
      change ‖J (R.center (tensorMatrixUnit _ _))‖ ≤ _
      rw [J.norm_map]
      exact R.norm_center_matrixUnit_le _ _
  have hsource : ‖endpointWord (q Ω) x‖ ≤
      (Fintype.card α : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
    apply norm_endpointWord_le_matrix_units (q Ω) x _ hm
    · rw [hqΩ, R.norm_full_matrixUnit]
    · intro i
      exact R.norm_center_matrixUnit_le _ _
  change ‖inner ℂ (endpointWord a z) (Y (endpointWord Ω x))‖ ≤ _
  rw [← ht]
  calc
    _ ≤ ‖endpointWord a z‖ * ‖Y (endpointWord (q Ω) x)‖ := norm_inner_le_norm _ _
    _ ≤ ‖endpointWord a z‖ * (‖Y‖ * ‖endpointWord (q Ω) x‖) :=
      mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg _)
    _ = ‖Y‖ * (‖endpointWord a z‖ * ‖endpointWord (q Ω) x‖) := by ring
    _ ≤ ‖Y‖ * ((Fintype.card α : ℝ) ^ (-((l : ℝ) + 1) / 2) *
        (Fintype.card α : ℝ) ^ (-((k : ℝ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul htest hsource (norm_nonneg _) (by positivity))
        (norm_nonneg Y)
    _ = _ := by rw [← Real.rpow_add hm]; congr 2; ring

/-- Isometric simultaneous-conjugation covariance on source and test words.
These are local actions on the realized tensor words, not coefficient formulas. -/
structure MatrixWordCovariance
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) where
  sourceAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F k →ₗᵢ[ℂ] EndpointTensor E F k
  testAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F l →ₗᵢ[ℂ] EndpointTensor E F l
  intertwine : ∀ u, Y.comp (sourceAction u).toContinuousLinearMap =
    (testAction u).toContinuousLinearMap.comp Y
  source_covariance : ∀ (u : Matrix.unitaryGroup α ℂ) (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord Ω (fun i => R.center ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ))) =
      sourceAction u (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))
  test_covariance : ∀ (u : Matrix.unitaryGroup α ℂ) (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord (R.full (star ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ))))
      (fun j => J (R.center ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ)))) =
      testAction u (endpointWord (R.full (star (v none)))
        (fun j => J (R.center (v (some (Sum.inr j))))))

theorem MatrixWordCovariance.form_invariant
    {R : MatrixHilbertStage (E := E) (F := F) (α := α)} {J : F →ₗᵢ⋆[ℂ] F}
    {Ω : E} {Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l}
    (cov : MatrixWordCovariance R J Ω Y) : UnitaryConjugationInvariant (R.form J Ω Y) :=
  R.form_invariant_of_word_covariance J Ω Y cov.sourceAction cov.testAction
    cov.intertwine cov.source_covariance cov.test_covariance

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The coefficient forms agree under an inclusion agreeing on the full and
centered Hilbert realizations. Star compatibility is supplied by the actual
matrix star-algebra inclusion. -/
theorem MatrixHilbertStage.form_compatible
    (R : MatrixHilbertStage (E := E) (F := F) (α := α))
    (S : MatrixHilbertStage (E := E) (F := F) (α := β))
    (J : F →ₗᵢ⋆[ℂ] F) (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (e : Matrix α α ℂ →⋆ₐ[ℂ] Matrix β β ℂ)
    (hfull : ∀ a, S.full (e a) = R.full a)
    (hcenter : ∀ a, S.center (e a) = R.center a)
    (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ) :
    S.form J Ω Y (fun i => e (v i)) = R.form J Ω Y v := by
  simp only [MatrixHilbertStage.form_apply, ← map_star, hfull, hcenter]

/-- Moving a general source endpoint across the intertwiner turns the endpoint
trace into the full Hilbert inner product. The centered matrix pairing is the
ordinary normalized trace pairing on this local stage. -/
theorem MatrixHilbertStage.endpoint_pairing_of_form
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (hΩ : R.full 1 = Ω)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hY : ∀ a, Y.comp (endpointHeadAction (n := k) (R.left a)) =
      (endpointHeadAction (n := l) (R.left a)).comp Y)
    (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hB : ∀ a b, Matrix.trace a = 0 → Matrix.trace b = 0 →
      B (R.center a) (R.center b) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace (a * b))
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hform : ∀ v, (∀ i : Fin k ⊕ Fin l, Matrix.trace (v (some i)) = 0) →
      R.form J Ω Y v = ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        ∑ P, c P * ∏ i : MatchingRepresentatives sourceFirstRank P,
          (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i))))
    (d a : Matrix α α ℂ) (v : Fin k ⊕ Fin l → Matrix α α ℂ)
    (hv : ∀ i, Matrix.trace (v i) = 0) :
    inner ℂ (endpointWord (R.full a) (fun j => J (R.center (v (.inr j)))))
      (Y (endpointWord (R.full d) (fun i => R.center (v (.inl i))))) =
    inner ℂ (R.full a) (R.full d) *
      ∑ P, c P * pairingPolynomial sourceFirstRank B P (fun i => R.center (v i)) := by
  classical
  let w : Option (Fin k ⊕ Fin l) → Matrix α α ℂ := Option.elim' (star a * d) v
  have hp : R.left d Ω = R.full d := by rw [← hΩ, R.left_apply, mul_one]
  have hpa : (R.left d).adjoint (R.full a) = R.full (star d * a) := by
    rw [R.left_adjoint, R.left_apply]
  have ht := endpoint_coefficient_transfer Y (R.left d) (hY d) Ω (R.full a)
    (fun i => R.center (v (.inl i))) (fun j => J (R.center (v (.inr j))))
  rw [hp, hpa] at ht
  have hw : R.form J Ω Y w =
      inner ℂ (endpointWord (R.full (star d * a)) (fun j => J (R.center (v (.inr j)))))
        (Y (endpointWord Ω (fun i => R.center (v (.inl i))))) := by
    simp only [R.form_apply, w, Option.elim'_none, Option.elim'_some, star_mul,
      star_star]
  rw [ht, ← hw, hform w (fun i => hv i), R.inner_full]
  change _ * _ = _ * _
  congr 1
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  unfold pairingPolynomial
  simp only [hB _ _ (hv _) (hv _)]
  symm
  exact Finset.prod_subtype
    (Finset.univ.filter (fun i => sourceFirstRank i < sourceFirstRank (P.1 i)))
    (by simp) (fun i => (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v i * v (P.1 i)))


section GrowingStages

variable {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- Assemble the actual stage forms, their covariance, their left-matrix test
estimate, and the finite invariant theory. The only published assumption is
`spanning`; every other premise is explicit local realization data. -/
theorem exists_realized_matrix_pairing_expansion
    (R : ∀ s, MatrixHilbertStage (E := E) (F := F) (α := A s))
    (J : F →ₗᵢ⋆[ℂ] F) (Ω : E) (hΩ : ∀ s, (R s).full 1 = Ω)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hleft : ∀ s a, Y.comp (endpointHeadAction (n := k) ((R s).left a)) =
      (endpointHeadAction (n := l) ((R s).left a)).comp Y)
    (cov : ∀ s, MatrixWordCovariance (R s) J Ω Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (e : ∀ s, Matrix (A 0) (A 0) ℂ →⋆ₐ[ℂ] Matrix (A s) (A s) ℂ)
    (hfull : ∀ s a, (R s).full (e s a) = (R 0).full a)
    (hcenter : ∀ s a, (R s).center (e s a) = (R 0).center a)
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => e s (v i)) = normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s))
    (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop) :
    ∃ c : Equiv.Perm (Option (Fin k ⊕ Fin l)) → ℂ,
      (∀ s v, (R s).form J Ω Y v = ∑ π, c π * normalizedPermutationContraction π v) ∧
      (∀ π, 2 * permutationCycleCount π < Fintype.card (Option (Fin k ⊕ Fin l)) + 1 → c π = 0) ∧
      (∀ s v, (∀ i : Fin k ⊕ Fin l, Matrix.trace (v (some i)) = 0) →
        (R s).form J Ω Y v = ((Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (v none)) *
          ∑ P : PerfectMatching (Fin k ⊕ Fin l), c (endpointMatching P) *
            ∏ i : MatchingRepresentatives sourceFirstRank P,
              (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i)))) := by
  apply exists_stable_tail_pairing_expansion sourceFirstRank sourceFirstRank_injective
    spanning (fun s => (R s).form J Ω Y) (fun s => (cov s).form_invariant)
    (fun s => e s) ?_ hcontraction labels hlabels hsize ‖Y‖ ?_
  · intro s v
    exact (R 0).form_compatible (R s) J Ω Y (e s) (hfull s) (hcenter s) v
  · intro s π
    simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using
      (R s).form_matrixUnit_bound J Ω (hΩ s) Y (hleft s) (labels s) π

end GrowingStages

end KadisonSimilarity

end

end OAI
