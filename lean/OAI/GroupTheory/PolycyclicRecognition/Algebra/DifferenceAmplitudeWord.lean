import OAI.GroupTheory.PolycyclicRecognition.Algebra.AmplitudeWordRank
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SubmersivePolynomialImage

namespace OAI

/-! # Two independent interval samples per generator switch -/

noncomputable section

namespace PolycyclicRecognition

open Module

/-- First samples minus second samples, with the same fixed order of letters. -/
def differenceParameters (m : ℕ) : (Fin (m + m) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun j =>
    (ContinuousLinearMap.proj (Fin.castAdd m j) : (Fin (m + m) → ℝ) →L[ℝ] ℝ) -
      ContinuousLinearMap.proj (Fin.natAdd m j))

@[simp] theorem differenceParameters_apply (m : ℕ) (t : Fin (m + m) → ℝ) (j : Fin m) :
    differenceParameters m t j = t (Fin.castAdd m j) - t (Fin.natAdd m j) := rfl

@[simp] theorem differenceParameters_append (m : ℕ) (x y : Fin m → ℝ) :
    differenceParameters m (Fin.append x y) = x - y := by ext j; simp only [differenceParameters_apply, Fin.append_left, Fin.append_right, Pi.sub_apply]

theorem differenceParameters_surjective (m : ℕ) : Function.Surjective (differenceParameters m) := by
  intro x
  exact ⟨Fin.append x 0, by simp⟩

def differenceAmplitudeWordEndpoint {I : Type*} {n m c : ℕ} (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (t : Fin (m + m) → ℝ) : Fin n → ℝ :=
  amplitudeWordEndpoint a letters p (differenceParameters m t)

theorem hasPolynomialCoordinates_differenceAmplitudeWord {I : Type*} {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I) :
    HasPolynomialCoordinates (differenceAmplitudeWordEndpoint (n := n) a letters) := by
  apply hasPolynomialCoordinates_listProduct a Prod.fst
  intro j
  apply HasPolynomialCoordinates.smul
  · exact hasPolynomialCoordinates_const (fun p :
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ) =>
      p.2 (letters j))
  · have h₁ := hasPolynomialFormula_coordinate (P :=
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) (Fin.castAdd m j)
    have h₂ := (hasPolynomialFormula_const (P :=
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
      (m := m + m) (fun _ => (-1 : ℝ))).mul (hasPolynomialFormula_coordinate (Fin.natAdd m j))
    simpa only [differenceParameters_apply, neg_one_mul, sub_eq_add_neg] using h₁.add h₂

theorem contDiff_differenceAmplitudeWord {I : Type*} [Fintype I] {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I) {q : ℕ∞} :
    ContDiff ℝ q (fun z :
      (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
        (Fin (m + m) → ℝ) => differenceAmplitudeWordEndpoint a letters z.1 z.2) := by
  change ContDiff ℝ q (fun z :
      (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
        (Fin (m + m) → ℝ) => polynomialListProduct (dynkinProduct a z.1.1)
          (List.ofFn fun j =>
            (z.2 (Fin.castAdd m j) - z.2 (Fin.natAdd m j)) • z.1.2 (letters j)))
  apply contDiff_polynomialListProduct_ofFn
  · exact contDiff_fst.fst
  · intro j
    exact (((contDiff_apply ℝ ℝ (Fin.castAdd m j)).comp contDiff_snd).sub
      ((contDiff_apply ℝ ℝ (Fin.natAdd m j)).comp contDiff_snd)).smul
      ((contDiff_apply ℝ (Fin n → ℝ) (letters j)).comp contDiff_fst.snd)

/-- The independent-difference parametrization retains the full rank proved
for the fixed generator word. -/
theorem differenceAmplitudeWord_surjective_fderiv {I : Type*} [Fintype I] {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (t₀ : Fin m → ℝ)
    (hs : Function.Surjective (fderiv ℝ (amplitudeWordEndpoint a letters p) t₀)) :
    Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p) (Fin.append t₀ 0)) := by
  have hf : DifferentiableAt ℝ (amplitudeWordEndpoint a letters p) t₀ :=
    (((contDiff_amplitudeWordEndpoint (n := n) (q := 1) a letters).comp
      ((contDiff_const (c := p)).prodMk contDiff_id)).differentiable one_ne_zero) t₀
  have hf' : HasFDerivAt (amplitudeWordEndpoint a letters p)
      (fderiv ℝ (amplitudeWordEndpoint a letters p) t₀) (differenceParameters m (Fin.append t₀ 0)) := by
    simpa only [differenceParameters_append, sub_zero] using hf.hasFDerivAt
  have hd := hf'.comp (Fin.append t₀ 0) ((differenceParameters m).hasFDerivAt)
  change HasFDerivAt (differenceAmplitudeWordEndpoint a letters p) _ (Fin.append t₀ 0) at hd
  rw [hd.fderiv]
  exact hs.comp (differenceParameters_surjective m)

theorem exists_submersive_differenceAmplitudeWord {I J : Type*} [Fintype I] {n c : ℕ}
    (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → Fin n → ℝ) (b₀ : Basis J ℝ (Fin n → ℝ)) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j) :
    ∃ (m : ℕ) (letters : Fin m → I) (t₀ : Fin (m + m) → ℝ),
      differenceAmplitudeWordEndpoint a letters (B, X) t₀ = 0 ∧
      Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters (B, X)) t₀) := by
  obtain ⟨m, letters, t₀, hz, hs⟩ := exists_submersive_amplitudeWord a B hB hg hc X b₀ w₀ hw₀
  refine ⟨m, letters, Fin.append t₀ 0, ?_, differenceAmplitudeWord_surjective_fderiv a letters (B, X) t₀ hs⟩
  simpa only [differenceAmplitudeWordEndpoint, differenceParameters_append, sub_zero] using hz

end PolycyclicRecognition

end

end OAI
