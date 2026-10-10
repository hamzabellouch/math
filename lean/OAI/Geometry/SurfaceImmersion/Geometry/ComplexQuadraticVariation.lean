import OAI.Geometry.SurfaceImmersion.Geometry.ComplexSlotAdditivity
import OAI.Geometry.SurfaceImmersion.Geometry.ComplexFirstVariation

namespace OAI

/-! Actual complexified second polynomial variation, with both direction
slots and their bilinear algebra made explicit. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

abbrev DirectionJets := List (Fin 2) → Fin 4 → Base → ℂ

def pairJetData (G : Base → Space) (J K : DirectionJets) : JetData :=
  ![fun w a p => (jet G w a p : ℂ), J, K, 0]

def quadraticComplex (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (z : Base × ℝ) : ℂ :=
  (e.variations 1).evalComplex G (pairJetData G J K) z

lemma quadraticComplex_add_left (e : Expression) (G : Base → Space)
    (J K L : DirectionJets) (z : Base × ℝ) :
    quadraticComplex e G (J + K) L z = quadraticComplex e G J L z + quadraticComplex e G K L z := by
  apply DegreeIn.evalComplex_add (j := 0)
    (show DegreeIn 0 (e.variations 1) 1 by simpa using e.variations_degree 1 0)
  · intro i hi w a
    fin_cases i <;> simp_all [pairJetData]
  · intro i hi w a
    fin_cases i <;> simp_all [pairJetData]
  · intro w a
    rfl

lemma quadraticComplex_add_right (e : Expression) (G : Base → Space)
    (J K L : DirectionJets) (z : Base × ℝ) :
    quadraticComplex e G J (K + L) z = quadraticComplex e G J K z + quadraticComplex e G J L z := by
  apply DegreeIn.evalComplex_add (j := 1)
    (show DegreeIn 1 (e.variations 1) 1 by simpa using e.variations_degree 1 1)
  · intro i hi w a
    fin_cases i <;> simp_all [pairJetData]
  · intro i hi w a
    fin_cases i <;> simp_all [pairJetData]
  · intro w a
    rfl

lemma quadraticComplex_smul_left (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (c : ℂ) (z : Base × ℝ) :
    quadraticComplex e G (c • J) K z = c * quadraticComplex e G J K z := by
  have hh := (show DegreeIn 0 (e.variations 1) 1 by simpa using e.variations_degree 1 0).evalComplex_scaleSlot
    G (pairJetData G J K) (fun _ => c) z
  have he : scaleJetSlot (pairJetData G J K) 0 (fun _ => c) = pairJetData G (c • J) K := by
    funext i w a p
    fin_cases i <;> simp [scaleJetSlot, pairJetData]
  rw [he, pow_one] at hh
  exact hh

lemma quadraticComplex_smul_right (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (c : ℂ) (z : Base × ℝ) :
    quadraticComplex e G J (c • K) z = c * quadraticComplex e G J K z := by
  have hh := (show DegreeIn 1 (e.variations 1) 1 by simpa using e.variations_degree 1 1).evalComplex_scaleSlot
    G (pairJetData G J K) (fun _ => c) z
  have he : scaleJetSlot (pairJetData G J K) 1 (fun _ => c) = pairJetData G J (c • K) := by
    funext i w a p
    fin_cases i <;> simp [scaleJetSlot, pairJetData]
  rw [he, pow_one] at hh
  exact hh

def starDirectionJets (J : DirectionJets) : DirectionJets := fun w a p => star (J w a p)

lemma evalComplex_star (e : MixedExpression) (G : Base → Space) (J : JetData) (z : Base × ℝ) :
    e.evalComplex G (fun i w a p => star (J i w a p)) z = star (e.evalComplex G J z) := by
  induction e with
  | coeff c => simp only [evalComplex, Complex.star_def, Complex.conj_ofReal]
  | atom i w a e ih => simp only [evalComplex, ih, star_mul']
  | add e f ihe ihf => simp only [evalComplex, ihe, ihf, star_add]

lemma quadraticComplex_star (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (z : Base × ℝ) :
    quadraticComplex e G (starDirectionJets J) (starDirectionJets K) z =
      star (quadraticComplex e G J K z) := by
  have he : pairJetData G (starDirectionJets J) (starDirectionJets K) =
      fun i w a p => star (pairJetData G J K i w a p) := by
    funext i w a p
    fin_cases i <;> simp [pairJetData, starDirectionJets]
  change (e.variations 1).evalComplex G _ z = _
  rw [he]
  exact evalComplex_star (e.variations 1) G (pairJetData G J K) z

end ClosedSurfaceR4.JetPolynomial

end

end OAI
