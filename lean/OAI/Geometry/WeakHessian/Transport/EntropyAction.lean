import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatAction
import OAI.Geometry.WeakHessian.HeatFlow.HeatDiagonal

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma FormActionBound.regularize {ρ : X → ℝ} {v : Lp ℝ 2 m} {A ε B : ℝ}
    (hA : FormActionBound m ρ v A) (hρ : AEStronglyMeasurable ρ m)
    (hb : ∀ᵐ x ∂m, |ρ x| ≤ B) (hε : 0 ≤ ε) :
    FormActionBound m (fun x => ρ x+ε) v A := by
  intro f hf
  have hi : Integrable (fun x => ρ x*(weakGradient m f x)^2) m :=
    hf.2.2.integrable_sq.bdd_mul hρ (by simpa only [Real.norm_eq_abs] using hb)
  have he : (∫ x, (ρ x+ε)*(weakGradient m f x)^2 ∂m) =
      (∫ x, ρ x*(weakGradient m f x)^2 ∂m) + ε*(∫ x, (weakGradient m f x)^2 ∂m) := by
    simp_rw [add_mul]
    rw [integral_add hi (hf.2.2.integrable_sq.const_mul ε),integral_const_mul]
  rw [he]
  have hn : 0 ≤ ε*(∫ x, (weakGradient m f x)^2 ∂m) :=
    mul_nonneg hε (integral_nonneg fun _ => sq_nonneg _)
  linarith [hA f hf]

omit [SigmaFinite m] in
lemma cheegerHeat_diagonal_entropy_action
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s)
    {B : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂m, |u s x| ≤ B)
    (hun : ∀ᵐ x ∂m, 0 ≤ u s x) {c : ℝ} (hc : 0 < c)
    (hgrad : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      c*(∫ x, u s x*(weakGradient m (cheegerHeat h (θ s) f) x)^2 ∂m) ≤
        ∫ x, cheegerHeat h (θ s) (u s) x*(weakGradient m f x)^2 ∂m)
    {A : ℝ} (hA : FormActionBound m (u s) v A) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z)) w s ∧
      HasDerivAt (fun z => ∫ x, regularizedEntropy ε (cheegerHeat h (θ z) (u z) x) ∂m) e s ∧
      FormActionBound m (fun x => cheegerHeat h (θ s) (u s) x+ε) w (A/c-2*τ*e) := by
  obtain ⟨L,hL,hD,hE⟩ := cheegerHeat_diagonal_entropy_hasDerivAt hfin h hθ hu hpos hε
  refine ⟨_,_,hD,hE,?_⟩
  have hA0 : FormActionBound m (fun x => u s x+0) v A := by simpa only [add_zero] using hA
  have hP := hA0.heat_contraction_regularized hfin hID h hpos.le hc (le_refl 0) hB hub hgrad
  simp only [mul_zero,add_zero] at hP
  have hPB := cheegerHeat_bounded h hpos.le hB (u s) hub
  have hPε := hP.regularize (Lp.memLp _).aestronglyMeasurable hPB hε.le
  exact hPε.logarithmic_shift hfin hpar
    (identified_isLaplacian_of_formGenerator hfin hID h _ _ hL)
    (cheegerHeat_nonneg h hpos.le (u s) hun) hPB hε τ

end WeakHessian

end
end

end OAI
