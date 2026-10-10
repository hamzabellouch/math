import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticPhases

namespace OAI

/-! Finite sums in the actual complexified Hessian. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

def quadraticComplexBilinear (e : Expression) (G : Base → Space) (z : Base × ℝ) :
    DirectionJets →ₗ[ℂ] DirectionJets →ₗ[ℂ] ℂ where
  toFun J := {
    toFun := fun K => quadraticComplex e G J K z
    map_add' := fun K L => quadraticComplex_add_right e G J K L z
    map_smul' := fun c K => quadraticComplex_smul_right e G J K c z }
  map_add' J K := by
    ext L
    exact quadraticComplex_add_left e G J K L z
  map_smul' c J := by
    ext K
    exact quadraticComplex_smul_left e G J K c z

lemma quadraticComplex_sum {ι κ : Type*} (a : Finset ι) (b : Finset κ)
    (e : Expression) (G : Base → Space) (J : ι → DirectionJets) (K : κ → DirectionJets)
    (z : Base × ℝ) :
    quadraticComplex e G (∑ i ∈ a, J i) (∑ j ∈ b, K j) z =
      ∑ i ∈ a, ∑ j ∈ b, quadraticComplex e G (J i) (K j) z := by
  change quadraticComplexBilinear e G z (∑ i ∈ a, J i) (∑ j ∈ b, K j) = _
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm]
  rfl

lemma complexJet_add {H K : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    complexJet (fun p => H p + K p) = complexJet H + complexJet K := by
  funext w a p
  exact congrFun (directional_add (contDiff_pi.mp hH a) (contDiff_pi.mp hK a)
    (w.map coordinateVector)) p

lemma complexJet_zero : complexJet (0 : Base → Fin 4 → ℂ) = 0 := by
  funext w a p
  exact congrFun (iteratedDirectional_zero (w.map coordinateVector)) p

lemma complexJet_sum {ι : Type*} (a : Finset ι) (H : ι → Base → Fin 4 → ℂ)
    (hH : ∀ i ∈ a, ContDiff ℝ ∞ (H i)) :
    complexJet (fun p => ∑ i ∈ a, H i p) = ∑ i ∈ a, complexJet (H i) := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact complexJet_zero
  | @insert i a hi ih =>
    have hsm : ContDiff ℝ ∞ (fun p => ∑ j ∈ a, H j p) :=
      ContDiff.sum (fun j hj => hH j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    rw [complexJet_add (hH i (Finset.mem_insert_self _ _)) hsm,
      ih (fun j hj => hH j (Finset.mem_insert_of_mem hj))]

lemma starDirectionJets_sum {ι : Type*} (a : Finset ι) (J : ι → DirectionJets) :
    starDirectionJets (∑ i ∈ a, J i) = ∑ i ∈ a, starDirectionJets (J i) := by
  funext w b p
  simp [starDirectionJets, Finset.sum_apply, star_sum]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
