import Mathlib
import OAI.Computability.MinUncut.Analysis.HermiteComponent

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
local instance memLpMaskProjectDualFintype {U : Type*}
    [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

omit [AddCommGroup W] [Module F₂ W] in
lemma memLp_maskProject (S : Finset R) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (B : R → W) :
    MemLp (fun c => maskProject S (fun D => u D c) B) 2 (γpi ι) :=
  memLp_expect _ (fun D => (hu D).const_mul _)

lemma expect_sqrt_le {T : Type*} [Fintype T] [Nonempty T] (f : T → ℝ) (hf : ∀ t, 0 ≤ f t) :
    (𝔼 t, Real.sqrt (f t)) ≤ Real.sqrt (𝔼 t, f t) := by
  let g := fun t => Real.sqrt (f t)
  have hz := Finset.expect_nonneg (s := Finset.univ) (f := fun t => (g t - (𝔼 u, g u))^2)
    (fun _ _ => sq_nonneg _)
  have hg2 : ∀ t, g t ^ 2 = f t := fun t => Real.sq_sqrt (hf t)
  have hid : (𝔼 t, (g t - (𝔼 u, g u))^2) = (𝔼 t, f t) - (𝔼 t, g t)^2 := by
    simp only [sub_sq, hg2,
      Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.expect_mul,
      ← Finset.mul_expect, Fintype.expect_const]
    ring
  rw [hid] at hz
  exact (Real.le_sqrt (Finset.expect_nonneg (fun t _ => show 0≤g t from Real.sqrt_nonneg _)) (Finset.expect_nonneg (fun t _ => hf t))).2 (by linarith)
end MinUncut.RowNoise

end

end OAI
