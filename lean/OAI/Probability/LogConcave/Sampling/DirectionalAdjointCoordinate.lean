import Mathlib
import OAI.Probability.LogConcave.JetEstimates.PolyC1

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma directional_adjointCoordinate {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u v : Point d) :
    directional u (adjointCoordinate H v f)=fun x =>
      adjointCoordinate H v (directional u f) x+directional u (directional v H) x*f x := by
  have hD : Differentiable ℝ (directional v f) := (directional_smooth hf v).differentiable (by simp)
  have hS : Differentiable ℝ (directional v H) := (directional_smooth hH v).differentiable (by simp)
  change directional u (fun x => -directional v f x+directional v H x*f x)=_
  rw [directional_add (f:=fun x => -directional v f x)
    (g:=fun x => directional v H x*f x) hD.neg (hS.mul (hf.differentiable (by simp))),directional_neg hD,
    directional_mul hS (hf.differentiable (by simp)),directional_commute hf u v]
  funext x
  simp only [adjointCoordinate]
  ring

lemma adjointCoordinate_smooth {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Point d) :
    ContDiff ℝ (⊤ : ℕ∞) (adjointCoordinate H v f) :=
  (directional_smooth hf v).neg.add ((directional_smooth hH v).mul hf)

lemma directional_tensorAdjoint {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i))
    (b : ι → Point d) (u : Point d) :
    directional u (tensorAdjoint H b V)=fun x =>
      tensorAdjoint H b (fun i => directional u (V i)) x+
      ∑i,directional u (directional (b i) H) x*V i x := by
  unfold tensorAdjoint
  rw [directional_sum Finset.univ
    (fun i _ => (adjointCoordinate_smooth hH (hV i) (b i)).differentiable (by simp))]
  simp_rw [directional_adjointCoordinate hH (hV _)]
  funext x
  exact Finset.sum_add_distrib

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
