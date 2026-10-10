import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExpandedSchemeAmplitudes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateSchemeSubmersion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SurjectiveColumns

namespace OAI

/-! # Full rank of one fixed independent generator word -/

noncomputable section

namespace PolycyclicRecognition

open Module

/-- The rank belongs to the full word, before any successful-parameter restriction. -/
theorem exists_submersive_amplitudeWord {I J : Type*} [Fintype I] {n c : ℕ}
    (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → Fin n → ℝ) (b₀ : Basis J ℝ (Fin n → ℝ)) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j) :
    ∃ (m : ℕ) (letters : Fin m → I) (t₀ : Fin m → ℝ),
      amplitudeWordEndpoint a letters (B, X) t₀ = 0 ∧
      Function.Surjective (fderiv ℝ (amplitudeWordEndpoint a letters (B, X)) t₀) := by
  obtain ⟨w, i, hz, hs⟩ := exists_coordinate_submersive_scheme a B hB hg hc X b₀ w₀ hw₀
  let l := schemeAmplitudeSlots w i
  let letters := fun j : Fin l.length => (l.get j).1
  let ψ := fun t : Fin (finrank ℝ (Fin n → ℝ)) → ℝ =>
    fun j : Fin l.length => evaluateAmplitudeSlot t (l.get j).2
  let f := amplitudeWordEndpoint a letters (B, X)
  have he : (fun t => f (ψ t)) = polynomialEndpointScheme a w i (B, X) := by
    funext t
    exact amplitudeWord_scheme_eq a B hB hg X w i t
  have hψ : DifferentiableAt ℝ ψ 0 :=
    ((contDiff_evaluateAmplitudeSlots (q := 1) l).differentiable one_ne_zero).differentiableAt
  have hf : DifferentiableAt ℝ f (ψ 0) := by
    exact (((contDiff_amplitudeWordEndpoint (q := 1) a letters).comp
      (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero).differentiableAt
  have hd0 := (contDiff_polynomialEndpointScheme (V := Fin n → ℝ) (k := 1) a w i).differentiable one_ne_zero
  have hd1 := (hd0 ((B, X), 0)).hasFDerivAt
  have hi := hasFDerivAt_prodMk_right (𝕜 := ℝ) (B, X) (0 : Fin (finrank ℝ (Fin n → ℝ)) → ℝ)
  have hd := hd1.comp (0 : Fin (finrank ℝ (Fin n → ℝ)) → ℝ) hi
  have hd' := hf.hasFDerivAt.comp 0 hψ.hasFDerivAt
  change HasFDerivAt (fun t => f (ψ t)) _ 0 at hd'
  rw [he] at hd'
  have hderiv := hd'.unique hd
  refine ⟨l.length, letters, ψ 0, ?_, ?_⟩
  · change f (ψ 0) = 0
    rw [congrFun he 0]
    exact hz
  · intro y
    obtain ⟨v, hv⟩ := hs y
    refine ⟨fderiv ℝ ψ 0 v, ?_⟩
    have hh := congrArg (fun A => A v) hderiv
    exact hh.trans hv

/-- Select a nonzero square minor of that same fixed word. -/
theorem exists_amplitudeWord_nonsingular_minor {I J : Type*} [Fintype I] {n c : ℕ}
    (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → Fin n → ℝ) (b₀ : Basis J ℝ (Fin n → ℝ)) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j) :
    ∃ (m : ℕ) (letters : Fin m → I) (t₀ : Fin m → ℝ) (j : Fin n → Fin m),
      Function.Injective j ∧ amplitudeWordEndpoint a letters (B, X) t₀ = 0 ∧
      (Matrix.of fun i k =>
        fderiv ℝ (amplitudeWordEndpoint a letters (B, X)) t₀ (Pi.single (j k) 1) i).det ≠ 0 := by
  obtain ⟨m, letters, t₀, hz, hs⟩ := exists_submersive_amplitudeWord a B hB hg hc X b₀ w₀ hw₀
  obtain ⟨j, hj, hdet⟩ := exists_nonsingular_column_minor
    (fderiv ℝ (amplitudeWordEndpoint a letters (B, X)) t₀).toLinearMap hs
  exact ⟨m, letters, t₀, j, hj, hz, hdet⟩

end PolycyclicRecognition

end

end OAI
