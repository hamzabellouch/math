import OAI.Geometry.SurfaceImmersion.Correction.SupportedPolynomialMeanDifference
import OAI.Geometry.SurfaceImmersion.Geometry.JetVariationSupport

namespace OAI

/-! The actual polynomial quadratic mean preserves amplitude support, so
local smoothness near the support suffices for a global smooth coefficient. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma MixedExpression.evalComplex_congr (e : MixedExpression) (G : Base → Space)
    (J K : JetData) (z : Base × ℝ)
    (h : ∀ i w a, J i w a z.1 = K i w a z.1) :
    e.evalComplex G J z = e.evalComplex G K z := by
  induction e with
  | coeff c => rfl
  | atom i w a e ih => simp only [evalComplex, h, ih]
  | add e f ihe ihf => simp only [evalComplex, ihe, ihf]

lemma quadraticComplex_zero_at (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (z : Base × ℝ) (hJ : ∀ w a, J w a z.1 = 0) :
    quadraticComplex e G J K z = 0 := by
  have he : quadraticComplex e G J K z = quadraticComplex e G 0 K z := by
    apply MixedExpression.evalComplex_congr
    intro i w a
    fin_cases i
    · rfl
    · exact hJ w a
    · rfl
    · rfl
  rw [he]
  change quadraticComplexBilinear e G z 0 K = 0
  rw [map_zero, LinearMap.zero_apply]

lemma complexJet_zero_of_notMem {H : Base → Fin 4 → ℂ} {p : Base}
    (hp : p ∉ tsupport H) (w : List (Fin 2)) (a : Fin 4) : complexJet H w a p = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun hx => hp (((tsupport_iteratedDirectional (w.map coordinateVector) (fun p => H p a)).trans
    (tsupport_comp_subset (g := fun v : Fin 4 → ℂ => v a) rfl H)) hx)

namespace Perturbation

lemma quadraticMeanPair_zero_of_notMem {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ : Base → ℝ) (H J : Base → Fin 4 → ℂ)
    (τ t : ℝ) {p : Base} (hp : p ∉ tsupport H) :
    quadraticMeanPair P ε G φ H J τ t p = 0 := by
  have hp' : p ∉ tsupport (fun x => phase τ φ x • H x) :=
    fun hx => hp (tsupport_smul_subset_right (phase τ φ) H hx)
  apply Finset.sum_eq_zero
  intro l _
  rw [quadraticComplex_zero_at (P l) G _ _ (p, t)
    (fun w a => complexJet_zero_of_notMem hp' w a)]
  simp only [Complex.zero_re, mul_zero, zero_div]

lemma quadraticMeanPair_tsupport {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ : Base → ℝ) (H J : Base → Fin 4 → ℂ) (τ t : ℝ) :
    tsupport (quadraticMeanPair P ε G φ H J τ t) ⊆ tsupport H := by
  apply closure_minimal _ (isClosed_tsupport H)
  intro p hp
  by_contra hn
  exact hp (quadraticMeanPair_zero_of_notMem P ε G φ H J τ t hn)

lemma quadraticMeanCoefficient_tsupport {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (τ t : ℝ) :
    tsupport (quadraticMeanCoefficient P ε G φ H τ t) ⊆ tsupport H := by
  have he : quadraticMeanCoefficient P ε G φ H τ t = quadraticMeanPair P ε G φ H H τ t := by
    funext p
    exact (quadraticMeanPair_self P ε G hφ hH τ t p).symm
  rw [he]
  exact quadraticMeanPair_tsupport P ε G φ H H τ t

def polynomialMeanField {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (hP : ∀ l, (P l).SmoothCoeffs O) {G : Base → Space} {φ : Base → ℝ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (H : SupportedField (F := Fin 4 → ℂ) K) (ε τ t : ℝ) : SupportedField (F := ℝ) K :=
  let hs := (quadraticMeanCoefficient_tsupport P ε G hφ H.contDiff τ t).trans H.tsupport_subset
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset hU (hs.trans hKU)
      (quadraticMeanCoefficient_smooth hO hP hG hφ H.contDiff hQ ε τ t))
    (subset_closure.trans hs)

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
