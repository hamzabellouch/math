import OAI.GroupTheory.PolycyclicRecognition.Algebra.AmplitudeWordRank

namespace OAI

/-! # Submersion of an alternating product from two linear images

If generators in the union of two images bracket-generate the limiting
algebra, one fixed alternating product has a surjective differential.
Identity factors pad the unused side of each generator slot. The rank is
proved for the full product map, before restricting any parameters.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def alternatingCoordinateProduct {c h : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (L₁ L₂ : U →L[ℝ] V)
    (z : Fin h → U × U) : V :=
  polynomialListProduct (dynkinProduct a B)
    (List.ofFn (fun j => dynkinProduct a B (L₁ (z j).1) (L₂ (z j).2)))

theorem contDiff_alternatingCoordinateProduct {c h : ℕ} {q : ℕ∞}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (L₁ L₂ : U →L[ℝ] V) :
    ContDiff ℝ q (alternatingCoordinateProduct (h := h) a B L₁ L₂) := by
  apply contDiff_polynomialListProduct_ofFn a (fun _ => B) _ contDiff_const
  intro j
  apply contDiff_dynkinProduct a (fun _ => B) _ _ contDiff_const
  · exact L₁.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ (U × U) j))
  · exact L₂.contDiff.comp (contDiff_snd.comp (contDiff_apply ℝ (U × U) j))

def generatorPair (side : Bool) (v : U) : U × U :=
  if side then (v, 0) else (0, v)

def generatorPairParameters {I : Type*} {m : ℕ}
    (side : I → Bool) (v : I → U) (letters : Fin m → I) :
    (Fin m → ℝ) →L[ℝ] (Fin m → U × U) :=
  ContinuousLinearMap.pi (fun j =>
    (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).smulRight
      (generatorPair (side (letters j)) (v (letters j))))

theorem alternatingCoordinateProduct_generatorPairParameters
    {I : Type*} {n c m : ℕ} (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hg : PolynomialGroupLaws (dynkinProduct a B))
    (L₁ L₂ : U →L[ℝ] (Fin n → ℝ)) (X : I → Fin n → ℝ)
    (side : I → Bool) (v : I → U)
    (hX : ∀ i, (if side i then L₁ (v i) else L₂ (v i)) = X i)
    (letters : Fin m → I) (t : Fin m → ℝ) :
    alternatingCoordinateProduct a B L₁ L₂ (generatorPairParameters side v letters t) =
      amplitudeWordEndpoint a letters (B, X) t := by
  unfold alternatingCoordinateProduct amplitudeWordEndpoint
  congr 1
  apply congrArg List.ofFn
  funext j
  change dynkinProduct a B
    (L₁ (t j • generatorPair (side (letters j)) (v (letters j))).1)
    (L₂ (t j • generatorPair (side (letters j)) (v (letters j))).2) = t j • X (letters j)
  have hx := hX (letters j)
  cases hs : side (letters j)
  · simp [hs] at hx
    simpa [generatorPair, hs, hx] using hg.2.1 (t j • X (letters j))
  · simp [hs] at hx
    simpa [generatorPair, hs, hx] using hg.2.2.1 (t j • X (letters j))

theorem exists_submersive_alternatingCoordinateProduct
    {I J : Type*} [Fintype I] {n c : ℕ} (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (L₁ L₂ : U →L[ℝ] (Fin n → ℝ)) (X : I → Fin n → ℝ)
    (b₀ : Basis J ℝ (Fin n → ℝ)) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)
    (hX : ∀ i, X i ∈ Set.range L₁ ∪ Set.range L₂) :
    ∃ (h : ℕ) (z₀ : Fin h → U × U), alternatingCoordinateProduct a B L₁ L₂ z₀ = 0 ∧
      Function.Surjective (fderiv ℝ (alternatingCoordinateProduct a B L₁ L₂) z₀) := by
  classical
  have hpre (i : I) : ∃ side : Bool, ∃ v : U,
      (if side then L₁ v else L₂ v) = X i := by
    rcases hX i with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨true, v, hv⟩
    · exact ⟨false, v, hv⟩
  choose side v hv using hpre
  obtain ⟨h, letters, t₀, hz, hsurj⟩ := exists_submersive_amplitudeWord a B hB hg hc X b₀ w₀ hw₀
  let ψ := generatorPairParameters side v letters
  let f := alternatingCoordinateProduct (h := h) a B L₁ L₂
  have he : (fun t => f (ψ t)) = amplitudeWordEndpoint a letters (B, X) := by
    funext t
    exact alternatingCoordinateProduct_generatorPairParameters a B hg L₁ L₂ X side v hv letters t
  have hf : DifferentiableAt ℝ f (ψ t₀) :=
    ((contDiff_alternatingCoordinateProduct (q := 1) a B L₁ L₂).differentiable one_ne_zero) _
  have hd := hf.hasFDerivAt.comp t₀ ψ.hasFDerivAt
  change HasFDerivAt (fun t => f (ψ t)) _ t₀ at hd
  rw [he] at hd
  refine ⟨h, ψ t₀, ?_, ?_⟩
  · change f (ψ t₀) = 0
    rw [congrFun he t₀]
    exact hz
  · intro y
    obtain ⟨t, ht⟩ := hsurj y
    refine ⟨ψ t, ?_⟩
    have hh := congrArg (fun L => L t) hd.fderiv
    exact hh.symm.trans ht

end PolycyclicRecognition

end

end OAI
