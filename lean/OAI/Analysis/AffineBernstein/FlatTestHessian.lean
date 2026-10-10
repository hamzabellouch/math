import Mathlib
import OAI.Analysis.AffineBernstein.TubeDensityVariation
import OAI.Analysis.AffineBernstein.SupportVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma flat_hessian_eq_second {n : ℕ} {η : Space n → ℝ} {x : Space n}
    (hη : ContDiffAt ℝ ∞ η x) (i j : Fin n) :
    hessian η x i j = fderiv ℝ (fderiv ℝ η) x (coordinateVector n i) (coordinateVector n j) := by
  have hd := ((hη.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (coordinateVector n j) x)
  change fderiv ℝ (fun y => fderiv ℝ η y (coordinateVector n j)) x (coordinateVector n i) = _
  rw [he.fderiv]
  simp

omit [CompleteSpace S] [CompleteSpace E]

lemma flatSupportVariation_second_on_chart (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    (x v w : F) :
    fderiv ℝ (fderiv ℝ (flatSupportVariation ℓ q₀ C η)) (q₀+J x) (J v) (J w) =
      fderiv ℝ (fderiv ℝ η) x v w := by
  have hG := contDiffAt_flatSupportVariation ℓ q₀ C hη
    (q := q₀+J x) (by simp [hℓ,hJ])
  rw [← second_fderiv_affine_comp J q₀ hG]
  have he : (fun x => flatSupportVariation ℓ q₀ C η (q₀+J x)) = η :=
    funext (flatSupportVariation_on_chart ℓ q₀ C J hℓ hJ hC η)
  rw [he]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ]

lemma flatSupportVariation_baseMatrix {n : ℕ} (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] Space n) (J : Space n →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) {η : Space n → ℝ} (hη : ContDiff ℝ ∞ η)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    (x : Space n) (i j : ι) :
    tubeBaseMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bS i j =
      -hessian η x (e.symm (Sum.inl i)) (e.symm (Sum.inl j)) := by
  have ht (i : ι) : J (coordinateVector n (e.symm (Sum.inl i))) = (bS i,0) := by
    simp [hJb,tubeTangent]
  have hh := flatSupportVariation_second_on_chart ℓ q₀ C J hℓ hJ hC hη x
    (coordinateVector n (e.symm (Sum.inl i))) (coordinateVector n (e.symm (Sum.inl j)))
  rw [ht,ht] at hh
  change -_ = -_
  congr 1
  rw [hh]
  exact (flat_hessian_eq_second hη.contDiffAt _ _).symm

lemma flatSupportVariation_radiusMatrix {n : ℕ} (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] Space n) (J : Space n →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) {η : Space n → ℝ} (hη : ContDiff ℝ ∞ η)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    (x : Space n) (i j : κ) :
    tubeRadiusMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bE i j =
      hessian η x (e.symm (Sum.inr i)) (e.symm (Sum.inr j)) := by
  have ht (i : κ) : J (coordinateVector n (e.symm (Sum.inr i))) = (0,bE (Sum.inl i)) := by
    simp [hJb,tubeTangent]
  have hh := flatSupportVariation_second_on_chart ℓ q₀ C J hℓ hJ hC hη x
    (coordinateVector n (e.symm (Sum.inr i))) (coordinateVector n (e.symm (Sum.inr j)))
  rw [ht,ht] at hh
  change _ = _
  rw [show tubeRadiusMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bE i j = _ from hh]
  exact (flat_hessian_eq_second hη.contDiffAt _ _).symm

end AffineBernstein
end

end OAI
