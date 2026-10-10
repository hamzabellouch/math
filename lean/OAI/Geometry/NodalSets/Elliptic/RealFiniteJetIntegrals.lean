import OAI.Geometry.NodalSets.Elliptic.RealCutoffIntegralsLemmas
import OAI.Geometry.NodalSets.Elliptic.RealFiniteJetSquare

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_cutoff_square_integrable (eta H : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta) (hH : Continuous H) :
    Integrable (fun x ↦ eta x^2*H x) := by
  have hsq : HasCompactSupport (fun x ↦ eta x^2) := by
    convert hc.mul_right (f' := eta) using 1
    first | rfl | (ext x; simp [pow_two])
  exact ((heta.pow 2).continuous.mul hH).integrable_of_hasCompactSupport hsq.mul_right

lemma realFiniteJetSquare_zero (W : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    realFiniteJetSquare W 0 x = W x^2 := by
  simp [realFiniteJetSquare,partialJet]

lemma realFiniteJetSquare_integrable (eta W : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hW : ContDiff ℝ ∞ W) (n : ℕ) :
    Integrable (fun x ↦ eta x^2*realFiniteJetSquare W n x) :=
  real_cutoff_square_integrable eta _ heta hc (realFiniteJetSquare_smooth W hW n).continuous

lemma realFiniteJetSquare_integral_sum (eta W : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hW : ContDiff ℝ ∞ W) (n : ℕ) :
    (∫ x, eta x^2*realFiniteJetSquare W n x) =
      ∑ r ∈ Finset.range (n+1), ∑ w : Fin r → Fin 4, ∫ x, eta x^2*(partialJet W (List.ofFn w) x)^2 := by
  have hi (r : ℕ) (w : Fin r → Fin 4) :
      Integrable (fun x ↦ eta x^2*(partialJet W (List.ofFn w) x)^2) :=
    real_cutoff_square_integrable eta _ heta hc ((partialJet_smooth W hW _).pow 2).continuous
  simp only [realFiniteJetSquare,Finset.mul_sum]
  rw [integral_finsetSum _ (fun r _ ↦ integrable_finsetSum _ (fun w _ ↦ hi r w))]
  apply Finset.sum_congr rfl
  intro r _
  exact integral_finsetSum _ (fun w _ ↦ hi r w)

end
end Yau.Geometry

end OAI
