import OAI.Geometry.EinsteinFour.ScalarH1CompositionL2
import Mathlib.MeasureTheory.Function.Holder

namespace OAI

/-! Strong convergence of the quadratic gradient term in the local H2
chain rule. The coefficient is bounded and converges almost everywhere;
the two first-derivative factors converge in L4. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

local instance : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  constructor
  change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
  norm_num

def scalarL4Product : Lp ℝ 4 μ →L[ℝ] Lp ℝ 4 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ 4 4 2

theorem scalarL4Product_coe (f g : Lp ℝ 4 μ) :
    scalarL4Product (μ := μ) f g =ᵐ[μ] fun x => f x * g x :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f g

theorem scalarL4Product_tendsto {f g : ℕ → Lp ℝ 4 μ} {F G : Lp ℝ 4 μ}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G)) :
    Tendsto (fun n => scalarL4Product (μ := μ) (f n) (g n)) atTop (𝓝 (scalarL4Product (μ := μ) F G)) := by
  let B : Lp ℝ 4 μ →L[ℝ] Lp ℝ 4 μ →L[ℝ] Lp ℝ 2 μ := scalarL4Product (μ := μ)
  have hB : Continuous (fun z : Lp ℝ 4 μ × Lp ℝ 4 μ => B z.1 z.2) := B.continuous₂
  have hp : Tendsto (fun n => (f n, g n)) atTop (𝓝 (F, G)) := hf.prodMk_nhds hg
  simpa only [Function.comp_def] using! (hB.tendsto (F, G)).comp hp

theorem scalarL4Product_coefficient_tendsto {a : ℕ → X → ℝ} {b : X → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ n x, |a n x| ≤ C) (hbC : ∀ x, |b x| ≤ C)
    (hab : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    {f g : ℕ → Lp ℝ 4 μ} {F G : Lp ℝ 4 μ}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G)) :
    Tendsto (fun n => scalarCompositionL2Multiply (a n) (ha n) (haC n)
        (scalarL4Product (μ := μ) (f n) (g n))) atTop
      (𝓝 (scalarCompositionL2Multiply b hb hbC (scalarL4Product (μ := μ) F G))) :=
  scalarCompositionL2Multiply_tendsto ha hb hC haC hbC hab (scalarL4Product_tendsto hf hg)

end
end PositiveEinsteinFour.Geometry

end OAI
