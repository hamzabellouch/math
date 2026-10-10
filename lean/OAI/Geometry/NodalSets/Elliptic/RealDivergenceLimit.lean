import Mathlib.Topology.Algebra.Ring.Basic
import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets
import OAI.Geometry.NodalSets.Elliptic.RealWeightedElliptic

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Filter
open scoped Topology ContDiff
noncomputable section

lemma real_unweighted_divergence_expansion
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (W : Yau.Jets.Coord → ℝ)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) (hW : ContDiff ℝ ∞ W)
    (x : Yau.Jets.Coord) :
    Yau.coordDiv (realMatrixFlux C W) x = ∑ i, ∑ j,
      (partialJet (fun y ↦ C y i j) [i] x*partialJet W [j] x+
        C x i j*partialJet W [i,j] x) := by
  unfold Yau.coordDiv realMatrixFlux
  simp_rw [Yau.real_coordPartial_sum _ (fun j ↦ (hC _ j).mul (Yau.real_coordPartial_smooth W hW j)),
    Yau.real_coordPartial_mul _ _ (hC _ _) (Yau.real_coordPartial_smooth W hW _)]
  rfl

theorem real_divergence_limit_equation
    (C : ℕ → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (C0 : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : ℕ → Yau.Jets.Coord → ℝ) (V0 : Yau.Jets.Coord → ℝ)
    (W : ℕ → Yau.Jets.Coord → ℝ) (v : Yau.Jets.Coord → ℝ)
    (hC : ∀ n i j, ContDiff ℝ ∞ (fun x ↦ C n x i j))
    (hC0 : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C0 x i j))
    (hW : ∀ n, ContDiff ℝ ∞ (W n)) (hv : ContDiff ℝ ∞ v)
    (htC : ∀ i j ds x, Tendsto (fun n ↦ partialJet (fun y ↦ C n y i j) ds x) atTop
      (𝓝 (partialJet (fun y ↦ C0 y i j) ds x)))
    (htV : ∀ x, Tendsto (fun n ↦ V n x) atTop (𝓝 (V0 x)))
    (htW : ∀ ds x, Tendsto (fun n ↦ partialJet (W n) ds x) atTop (𝓝 (partialJet v ds x)))
    (he : ∀ n x, Yau.coordDiv (realMatrixFlux (C n) (W n)) x+V n x*W n x=0) :
    ∀ x, Yau.coordDiv (realMatrixFlux C0 v) x+V0 x*v x=0 := by
  intro x
  rw [real_unweighted_divergence_expansion C0 v hC0 hv]
  have hh : Tendsto (fun n ↦ (∑ i, ∑ j,
      (partialJet (fun y ↦ C n y i j) [i] x*partialJet (W n) [j] x+
        C n x i j*partialJet (W n) [i,j] x))+V n x*W n x) atTop
      (𝓝 ((∑ i, ∑ j, (partialJet (fun y ↦ C0 y i j) [i] x*partialJet v [j] x+
        C0 x i j*partialJet v [i,j] x))+V0 x*v x)) :=
    (tendsto_finsetSum _ (fun i _ ↦ tendsto_finsetSum _ (fun j _ ↦
      ((htC i j [i] x).mul (htW [j] x)).add ((htC i j [] x).mul (htW [i,j] x))))).add
      ((htV x).mul (htW [] x))
  apply tendsto_nhds_unique hh
  have hz (n : ℕ) := he n x
  simp only [real_unweighted_divergence_expansion (C _) (W _) (hC _) (hW _)] at hz
  simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))

end
end Yau.Geometry

end OAI
