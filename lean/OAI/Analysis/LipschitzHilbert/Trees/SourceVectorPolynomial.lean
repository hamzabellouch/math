import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorSchwartz
import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialLocalization

namespace OAI

/-! Polynomial localization preserves the actual coordinate frequency
cutoffs of Hilbert-valued Schwartz packets. -/
noncomputable section
open FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

def vectorPolynomialLocalization (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ (EuclideanSpace ℂ κ)) : SchwartzMap ℝ (EuclideanSpace ℂ κ) :=
  vectorSchwartz (fun k => polynomialLocalization a r q (f.postcompCLM (vectorCoordinate k)))

@[simp] theorem vectorPolynomialLocalization_apply (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ (EuclideanSpace ℂ κ)) (x : ℝ) :
    vectorPolynomialLocalization a r q f x=(polynomialWeight a r q x:ℂ) • f x := by
  ext k
  simp only [vectorPolynomialLocalization,vectorSchwartz_apply,polynomialLocalization_apply,
    SchwartzMap.postcompCLM_apply,vectorCoordinate_apply,PiLp.smul_apply,smul_eq_mul]

theorem vectorPolynomialLocalization_high (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ (EuclideanSpace ℂ κ)) (hi : ℝ)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ=0) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (vectorPolynomialLocalization a r q f) ξ=0 := by
  apply vectorSchwartz_fourier_zero
  intro k
  apply polynomialLocalization_high a r q (f.postcompCLM (vectorCoordinate k)) 0 hi
    (fun η hη => (not_lt_of_ge (abs_nonneg η) hη).elim) _ ξ hξ
  intro η hη
  rw [←vector_fourier_coordinate,hhigh η hη]
  rfl

theorem vectorPolynomialLocalization_low (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ (EuclideanSpace ℂ κ)) (lo hi : ℝ)
    (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ=0) (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ=0)
    (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (vectorPolynomialLocalization a r q f) ξ=0 := by
  apply vectorSchwartz_fourier_zero
  intro k
  apply polynomialLocalization_low a r q (f.postcompCLM (vectorCoordinate k)) lo hi _ _ ξ hξ
  · intro η hη
    rw [←vector_fourier_coordinate,hlow η hη]
    rfl
  · intro η hη
    rw [←vector_fourier_coordinate,hhigh η hη]
    rfl

end LipschitzHilbert

end

end OAI
