import OAI.Analysis.KadisonSimilarity.FreeProduct.Propagation
import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem

namespace OAI

/-!
# Propagation from a full column through repeated reduced words

Only raw word identities and the elementary tracial operator relations are
supplied below. The error vector, its scaling, the vanishing exceptional
coefficient, and the propagation bound are all derived.
-/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMap
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Evaluate the full-column operator norm bound on a vector in that column. -/
theorem column_error_apply_le (G S : H →L[ℂ] H) (M : Submodule ℂ H)
    {η : ℝ} (hcolumn : ‖(G - S).comp M.subtypeL‖ ≤ η) (x : H) (hx : x ∈ M) :
    ‖G x - S x‖ ≤ η * ‖x‖ := by
  have h := ((G - S).comp M.subtypeL).le_opNorm (⟨x, hx⟩ : M)
  exact h.trans (mul_le_mul_of_nonneg_right hcolumn (norm_nonneg x))

/-- The relation `X*X = a⁻¹Q` gives the exact tracial scaling on the range
fixed by `Q`; no smallness assumption on `‖X‖` is used. -/
theorem norm_apply_of_scaled_support (X Q : H →L[ℂ] H) {a : ℝ} (ha : 0 < a)
    (hX : X.adjoint.comp X = ((a⁻¹ : ℝ) : ℂ) • Q) (y : H) (hy : Q y = y) :
    ‖X y‖ = (Real.sqrt a)⁻¹ * ‖y‖ := by
  have hi : inner ℂ (X y) (X y) = ((a⁻¹ : ℝ) : ℂ) * inner ℂ y y := by
    rw [← adjoint_inner_right X y (X y)]
    change inner ℂ y ((X.adjoint.comp X) y) = _
    rw [hX, smul_apply, hy, inner_smul_right]
  have hs : ‖X y‖ ^ 2 = a⁻¹ * ‖y‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hi]
    change Complex.re (((a⁻¹ : ℝ) : ℂ) * inner ℂ y y) =
      a⁻¹ * Complex.re (inner ℂ y y)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg a))
    (norm_nonneg y))).mp
  rw [hs, mul_pow, inv_pow, Real.sq_sqrt ha.le]

section WordData

variable {B V E F : Type*}
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Local tracial-word data for one fixed positive word level. The fields are
operator identities, word isometries, and the tensor-coordinate formula for
the exceptional projection. There is no approximation or propagation bound
among the fields. -/
structure RepeatedLetterWords (G : H →L[ℂ] H) (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection] (a : ℝ) where
  repeatVector : B →ₗᵢ[ℂ] V
  word : ℕ → V →ₗᵢ[ℂ] H
  small : B →L[ℂ] H
  small_norm : ∀ v, ‖small v‖ = Real.sqrt a * ‖v‖
  level_zero : ∀ v, G (small v) = small (B₀ v)
  level_repeated : ∀ n v, G (word n (repeatVector v)) = word n (Bₖ (repeatVector v))
  support : H →L[ℂ] H
  support_small : ∀ v, support (small v) = small v
  letter : ℕ → H →L[ℂ] H
  letter_scale : ∀ n, (letter n).adjoint.comp (letter n) = ((a⁻¹ : ℝ) : ℂ) • support
  wordPrefix : ℕ → H →L[ℂ] H
  word_factor : ∀ n v, word n (repeatVector v) = wordPrefix n (letter n (small v))
  prefix_isometry : ∀ n, ∀ z ∈ Pᗮ, ‖wordPrefix n z‖ = ‖z‖
  prefix_bound : ℝ
  prefix_bound_le : ∀ n, ‖wordPrefix n‖ ≤ prefix_bound
  tensor_coordinates : H →L[ℂ] HilbertTensor E F
  vacuum_insert : F →L[ℂ] H
  adjoint_letters : ℕ → E
  adjoint_letters_orthonormal : Orthonormal ℂ adjoint_letters
  vacuum_slice : ∀ n z, P.starProjection (letter n z) =
    vacuum_insert (tensorSlice (adjoint_letters n) (tensor_coordinates z))

namespace RepeatedLetterWords

variable {G : H →L[ℂ] H} {B₀ : B →L[ℂ] B} {Bₖ : V →L[ℂ] V}
  {P : Submodule ℂ H} [P.HasOrthogonalProjection] {a : ℝ}

/-- The exceptional first-coordinate coefficient vanishes on each fixed error
vector. This is a consequence of orthonormality and tensor completion. -/
theorem vacuum_projection_tendsto_zero
    (D : RepeatedLetterWords (E := E) (F := F) G B₀ Bₖ P a) (y : H) :
    Tendsto (fun n => P.starProjection (D.letter n y)) atTop (𝓝 0) := by
  have ht := tensorSlice_tendsto_zero_of_orthonormal D.adjoint_letters
    D.adjoint_letters_orthonormal (D.tensor_coordinates y)
  simpa only [D.vacuum_slice, Function.comp_def, map_zero] using
    (D.vacuum_insert.continuous.tendsto 0).comp ht

/-- The repeated-letter estimate for a vector supported in the full column.
The multiplier commutation hypotheses are the raw left/right action laws. -/
theorem propagation_of_column
    (D : RepeatedLetterWords (E := E) (F := F) G B₀ Bₖ P a) (ha : 0 < a)
    (M : Submodule ℂ H) (S : H →L[ℂ] H) {η : ℝ}
    (hcolumn : ‖(G - S).comp M.subtypeL‖ ≤ η)
    (hSsupport : D.support.comp S = S.comp D.support)
    (hSletter : ∀ n, S.comp (D.letter n) = (D.letter n).comp S)
    (hSprefix : ∀ n, S.comp (D.wordPrefix n) = (D.wordPrefix n).comp S)
    (hMletter : ∀ n z, z ∈ M → D.letter n z ∈ M)
    (hMprefix : ∀ n z, z ∈ M → D.wordPrefix n z ∈ M)
    (v : B) (hv : D.small v ∈ M) :
    ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  let y := S (D.small v) - D.small (B₀ v)
  have hy : ‖y‖ ≤ η * Real.sqrt a * ‖v‖ := by
    calc
      ‖y‖ = ‖G (D.small v) - S (D.small v)‖ := by
        dsimp [y]
        rw [D.level_zero, norm_sub_rev]
      _ ≤ η * ‖D.small v‖ := column_error_apply_le G S M hcolumn _ hv
      _ = η * Real.sqrt a * ‖v‖ := by rw [D.small_norm]; ring
  have hQy : D.support y = y := by
    have hc := congrArg (fun T : H →L[ℂ] H => T (D.small v)) hSsupport
    simp only [comp_apply, D.support_small] at hc
    simpa only [y, map_sub, D.support_small] using congrArg (fun z => z - D.small (B₀ v)) hc
  have hz (n : ℕ) : ‖D.letter n y‖ ≤ η * ‖v‖ := by
    rw [norm_apply_of_scaled_support (D.letter n) D.support ha (D.letter_scale n) y hQy]
    have h := corner_scaled_error_le (c := η) (ε := 1) (v := ‖v‖) ha
      (show ‖y‖ ≤ η * 1 * Real.sqrt a * ‖v‖ by simpa using hy)
    simpa using h
  have hword_mem (n : ℕ) : D.word n (D.repeatVector v) ∈ M := by
    rw [D.word_factor]
    exact hMprefix n _ (hMletter n _ hv)
  have hword_error (n : ℕ) :
      ‖G (D.word n (D.repeatVector v)) - S (D.word n (D.repeatVector v))‖ ≤ η * ‖v‖ := by
    simpa only [LinearIsometry.norm_map] using
      column_error_apply_le G S M hcolumn _ (hword_mem n)
  have hSletter_apply (n : ℕ) (z : H) : S (D.letter n z) = D.letter n (S z) :=
    congrArg (fun T : H →L[ℂ] H => T z) (hSletter n)
  have hSprefix_apply (n : ℕ) (z : H) : S (D.wordPrefix n z) = D.wordPrefix n (S z) :=
    congrArg (fun T : H →L[ℂ] H => T z) (hSprefix n)
  have hid (n : ℕ) :
      S (D.word n (D.repeatVector v)) - D.word n (D.repeatVector (B₀ v)) =
        D.wordPrefix n (D.letter n y) := by
    simp only [D.word_factor, hSprefix_apply, hSletter_apply, y, map_sub]
  have htest (n : ℕ) : ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤
      η * ‖v‖ + ‖D.wordPrefix n (D.letter n y)‖ := by
    calc
      _ = ‖G (D.word n (D.repeatVector v)) - D.word n (D.repeatVector (B₀ v))‖ := by
        rw [D.level_repeated, ← map_sub, LinearIsometry.norm_map]
      _ ≤ ‖G (D.word n (D.repeatVector v)) - S (D.word n (D.repeatVector v))‖ +
          ‖S (D.word n (D.repeatVector v)) - D.word n (D.repeatVector (B₀ v))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η * ‖v‖ + ‖D.wordPrefix n (D.letter n y)‖ := by
        rw [hid]
        exact add_le_add (hword_error n) le_rfl
  have hfinal := propagation_bound_of_vanishing_projection P D.wordPrefix
    (fun n => D.letter n y) D.prefix_isometry D.prefix_bound D.prefix_bound_le
    (η * ‖v‖) ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ hz
    (D.vacuum_projection_tendsto_zero y) htest
  simpa only [mul_assoc] using hfinal

/-- Feed a supported right multiplier obtained by the full-column theorem
into propagation. The support equality is retained in the supplied conclusion;
only the column error and left/right commutation enter the limit estimate. -/
theorem propagation_of_full_column
    {A : Type*} [CStarAlgebra A]
    (D : RepeatedLetterWords (E := E) (F := F) G B₀ Bₖ P a) (ha : 0 < a)
    (R : TracialRightAction (P := A) (H := H)) (r : A)
    (M : Submodule ℂ H) {η : ℝ}
    (fullColumn : ∃ b : A, r * b = b ∧ ‖(G - R.right b).comp M.subtypeL‖ ≤ η)
    (hRsupport : ∀ b, D.support.comp (R.right b) = (R.right b).comp D.support)
    (hRletter : ∀ b n, (R.right b).comp (D.letter n) = (D.letter n).comp (R.right b))
    (hRprefix : ∀ b n, (R.right b).comp (D.wordPrefix n) = (D.wordPrefix n).comp (R.right b))
    (hMletter : ∀ n z, z ∈ M → D.letter n z ∈ M)
    (hMprefix : ∀ n z, z ∈ M → D.wordPrefix n z ∈ M)
    (v : B) (hv : D.small v ∈ M) :
    ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  obtain ⟨b, _, hcolumn⟩ := fullColumn
  exact D.propagation_of_column ha M (R.right b) hcolumn (hRsupport b)
    (hRletter b) (hRprefix b) hMletter hMprefix v hv

end RepeatedLetterWords
/-- The bounded-vector argument extends to every vector by density and
continuity, yielding the operator norm formulation of propagation. -/
theorem norm_repeated_error_le_of_dense
    {I : Type*} (f : I → B) (hf : DenseRange f)
    (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V) (repeatVector : B →ₗᵢ[ℂ] V)
    {η : ℝ} (hη : 0 ≤ η)
    (hbound : ∀ i, ‖Bₖ (repeatVector (f i)) - repeatVector (B₀ (f i))‖ ≤ 2 * η * ‖f i‖) :
    ‖Bₖ.comp repeatVector.toContinuousLinearMap - repeatVector.toContinuousLinearMap.comp B₀‖ ≤ 2 * η := by
  apply opNorm_le_bound _ (mul_nonneg (by norm_num) hη)
  intro v
  have hclosed : IsClosed {w : B | ‖Bₖ (repeatVector w) - repeatVector (B₀ w)‖ ≤
      2 * η * ‖w‖} := isClosed_le (by fun_prop) (by fun_prop)
  have hv : ‖Bₖ (repeatVector v) - repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ :=
    hf.induction_on v hclosed hbound
  simpa only [sub_apply, comp_apply, LinearIsometry.coe_toContinuousLinearMap] using hv

end WordData
end KadisonSimilarity

end

end OAI
