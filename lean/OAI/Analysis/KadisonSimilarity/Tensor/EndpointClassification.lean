import OAI.Analysis.KadisonSimilarity.Tensor.InvariantIntertwiners
import OAI.Analysis.KadisonSimilarity.Tensor.EndpointDensity

namespace OAI

/-!
# Completed invariant intertwiners from matrix-stage geometry

Finite-dimensional Schur--Weyl spanning is the only invariant-theory input.
The remaining assumptions describe a nested dense tracial matrix realization,
its conjugation, and the operator's actual left and conjugation intertwinings.
The coefficient identity and completed permutation classification are derived.
-/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

def fullMatrixStage (R : ∀ s, MatrixHilbertStage (E := E) (F := F) (α := A s))
    (s : ℕ) : Set E := Set.range (R s).full

def centeredMatrixStage (R : ∀ s, MatrixHilbertStage (E := E) (F := F) (α := A s))
    (s : ℕ) : Set F := {x | ∃ a, Matrix.trace a = 0 ∧ (R s).center a = x}

/-- Local tracial realization data for the nested matrix stages. In particular,
there is no invariant coefficient formula or intertwiner classification here. -/
structure TracialMatrixTower where
  stage : ∀ s, MatrixHilbertStage (E := E) (F := F) (α := A s)
  traceVector : E
  norm_traceVector : ‖traceVector‖ = 1
  unit_realization : ∀ s, (stage s).full 1 = traceVector
  conjugation : F →ₗᵢ⋆[ℂ] F
  conjugation_involutive : Function.Involutive conjugation
  pairing : F →L[ℂ] F →L[ℂ] ℂ
  pairing_conjugation : ∀ x y, pairing x (conjugation y) = inner ℂ y x
  pairing_matrix : ∀ s a b, Matrix.trace a = 0 → Matrix.trace b = 0 →
    pairing ((stage s).center a) ((stage s).center b) =
      (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (a * b)
  inclusion : ∀ s, Matrix (A 0) (A 0) ℂ →⋆ₐ[ℂ] Matrix (A s) (A s) ℂ
  full_compatible : ∀ s a, (stage s).full (inclusion s a) = (stage 0).full a
  center_compatible : ∀ s a, (stage s).center (inclusion s a) = (stage 0).center a
  transition : ∀ s t, s ≤ t → Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] Matrix (A t) (A t) ℂ
  full_transition : ∀ s t h a, (stage t).full (transition s t h a) = (stage s).full a
  center_transition : ∀ s t h a, (stage t).center (transition s t h a) = (stage s).center a
  full_mono : Monotone (fullMatrixStage stage)
  center_mono : Monotone (centeredMatrixStage stage)
  full_dense : Dense (⋃ s, fullMatrixStage stage s)
  center_dense : Dense (⋃ s, centeredMatrixStage stage s)
  size_tendsto : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop
  realOrthonormal : ℕ → F
  realOrthonormal_orthonormal : Orthonormal ℂ realOrthonormal
  realOrthonormal_fixed : ∀ n, conjugation (realOrthonormal n) = realOrthonormal n

variable {k l : ℕ}

/-- The full completed coefficient formula is derived from stage geometry,
left intertwining, and finite Schur--Weyl, rather than assumed. -/
theorem exists_endpoint_pairing_expansion_of_schurWeyl
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hleft : ∀ s a, Y.comp (endpointHeadAction (n := k) ((T.stage s).left a)) =
      (endpointHeadAction (n := l) ((T.stage s).left a)).comp Y)
    (cov : ∀ s, MatrixWordCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) :
    ∃ c : PerfectMatching (Fin k ⊕ Fin l) → ℂ, ∀ d a v,
      inner ℂ (endpointWord a (fun j => T.conjugation (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank T.pairing P v := by
  obtain ⟨coeff, _, _, hforms⟩ := exists_realized_matrix_pairing_expansion T.stage
    T.conjugation T.traceVector T.unit_realization Y hleft cov spanning T.inclusion
    T.full_compatible T.center_compatible hcontraction labels hlabels T.size_tendsto
  refine ⟨fun P => coeff (endpointMatching P), ?_⟩
  apply endpoint_pairing_identity_of_stages Y T.conjugation T.conjugation.continuous T.pairing
    (fun P => coeff (endpointMatching P)) (fullMatrixStage T.stage)
    (centeredMatrixStage T.stage) T.full_mono T.center_mono T.full_dense T.center_dense
  intro s d a v hd ha hv
  obtain ⟨d', rfl⟩ := hd
  obtain ⟨a', rfl⟩ := ha
  choose v' htrace heq using hv
  have hv' : v = fun i => (T.stage s).center (v' i) := funext (fun i => (heq i).symm)
  rw [hv']
  exact (T.stage s).endpoint_pairing_of_form T.conjugation T.traceVector
    (T.unit_realization s) Y (hleft s) T.pairing (T.pairing_matrix s)
    (fun P => coeff (endpointMatching P)) (hforms s) d' a' v' htrace

omit [CompleteSpace E] in
/-- A full endpoint pairing formula reconstructs the identity on the endpoint
factor and the compression to the normalized trace vector. -/
theorem endpoint_reconstruct_from_pairing
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (J : F → F) (hJJ : Function.Involutive J)
    (B : F →L[ℂ] F →L[ℂ] ℂ) (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hfull : ∀ d a v,
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v) :
    Y = endpointAmplification (endpointCompression Ω Y) ∧
      (∀ v, tracialWordCoefficient (endpointCompression Ω Y) J v =
        ∑ P, c P * pairingPolynomial sourceFirstRank B P v) := by
  have hunit : inner ℂ Ω Ω = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  have hc : ∀ v, tracialWordCoefficient (endpointCompression Ω Y) J v =
      ∑ P, c P * pairingPolynomial sourceFirstRank B P v := by
    intro v
    rw [tracialWordCoefficient, endpointCompression_coefficient, hfull Ω Ω v, hunit, one_mul]
  refine ⟨?_, hc⟩
  apply endpointOperator_eq_amplification
  intro d x a z
  have hx := hfull d a (Sum.elim x (J ∘ z))
  have hz := hc (Sum.elim x (J ∘ z))
  have hJJ' (y : F) : J (J y) = y := hJJ y
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, hJJ'] at hx
  simp only [tracialWordCoefficient, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, hJJ'] at hz
  rw [hx, hz]

omit [CompleteSpace E] in
/-- Unequal degrees force the full endpoint operator to vanish. -/
theorem endpoint_zero_from_pairing
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (J : F → F) (hJ : Continuous J)
    (hJJ : Function.Involutive J) (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hB : ∀ x y, B x (J y) = inner ℂ y x)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (h : ℕ → F) (hh : Orthonormal ℂ h) (hfix : ∀ m, J (h m) = h m)
    (hfull : ∀ d a v,
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v)
    (hkl : k ≠ l) : Y = 0 := by
  obtain ⟨hrec, hcoeff⟩ := endpoint_reconstruct_from_pairing Y Ω hΩ J hJJ B c hfull
  have hlabels (a b : ℕ) : B (h a) (h b) = if a = b then 1 else 0 := by
    rw [← hfix b, hB]
    simpa only [eq_comm] using (orthonormal_iff_ite.mp hh b a)
  have hzero := tensorOperator_eq_zero_of_tracial_stages (endpointCompression Ω Y)
    J hJ hJJ B sourceFirstRank sourceFirstRank_injective c h hh hfix hlabels
    (fun _ => Set.univ) (fun _ _ _ => Set.Subset.refl _)
    (by simpa only [Set.iUnion_const] using (dense_univ : Dense (Set.univ : Set F)))
    (fun _ v _ => hcoeff v) hkl
  rw [hrec]
  apply continuousLinearMap_ext_endpointWords
  intro d x
  simp only [endpointWord, endpointAmplification_insert, hzero,
    zero_apply, map_zero]

omit [CompleteSpace E] in
/-- Equal degrees give an actual finite sum of position permutations, with
identity on the unrestricted endpoint. -/
theorem endpoint_permutations_from_pairing {n : ℕ}
    (Y : EndpointTensor E F n →L[ℂ] EndpointTensor E F n)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (J : F → F) (hJ : Continuous J)
    (hJJ : Function.Involutive J) (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hB : ∀ x y, B x (J y) = inner ℂ y x)
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ)
    (h : ℕ → F) (hh : Orthonormal ℂ h) (hfix : ∀ m, J (h m) = h m)
    (hfull : ∀ d a v,
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v) :
    Y = endpointAmplification (crossPairingOperator c) := by
  obtain ⟨hrec, hcoeff⟩ := endpoint_reconstruct_from_pairing Y Ω hΩ J hJJ B c hfull
  have hperm := tensorOperator_eq_crossPairingOperator_of_stages (endpointCompression Ω Y)
    J hJ hJJ B hB c h hh hfix (fun _ => Set.univ) (fun _ _ _ => Set.Subset.refl _)
    (by simpa only [Set.iUnion_const] using (dense_univ : Dense (Set.univ : Set F)))
    (fun _ v _ => hcoeff v)
  rwa [hperm] at hrec

/-- The unequal-degree invariant-intertwiner theorem, conditional only on
finite Schur--Weyl and explicit tracial matrix realization data. -/
theorem endpoint_intertwiner_zero_of_schurWeyl
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hleft : ∀ s a, Y.comp (endpointHeadAction (n := k) ((T.stage s).left a)) =
      (endpointHeadAction (n := l) ((T.stage s).left a)).comp Y)
    (cov : ∀ s, MatrixWordCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) (hkl : k ≠ l) : Y = 0 := by
  obtain ⟨c, hc⟩ := exists_endpoint_pairing_expansion_of_schurWeyl
    T Y hleft cov spanning hcontraction labels hlabels
  exact endpoint_zero_from_pairing Y T.traceVector T.norm_traceVector T.conjugation
    T.conjugation.continuous T.conjugation_involutive T.pairing T.pairing_conjugation
    c T.realOrthonormal T.realOrthonormal_orthonormal T.realOrthonormal_fixed hc hkl

/-- The equal-degree invariant-intertwiner theorem on the completed endpoint
Hilbert tensor space; the coefficient expansion is a proved conclusion. -/
theorem endpoint_intertwiner_permutations_of_schurWeyl {n : ℕ}
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : EndpointTensor E F n →L[ℂ] EndpointTensor E F n)
    (hleft : ∀ s a, Y.comp (endpointHeadAction (n := n) ((T.stage s).left a)) =
      (endpointHeadAction (n := n) ((T.stage s).left a)).comp Y)
    (cov : ∀ s, MatrixWordCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin n ⊕ Fin n)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin n ⊕ Fin n))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin n ⊕ Fin n) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) :
    ∃ c : PerfectMatching (Fin n ⊕ Fin n) → ℂ,
      Y = endpointAmplification (crossPairingOperator c) := by
  obtain ⟨c, hc⟩ := exists_endpoint_pairing_expansion_of_schurWeyl
    T Y hleft cov spanning hcontraction labels hlabels
  exact ⟨c, endpoint_permutations_from_pairing Y T.traceVector T.norm_traceVector
    T.conjugation T.conjugation.continuous T.conjugation_involutive T.pairing
    T.pairing_conjugation c T.realOrthonormal T.realOrthonormal_orthonormal
    T.realOrthonormal_fixed hc⟩

end KadisonSimilarity

end

end OAI
