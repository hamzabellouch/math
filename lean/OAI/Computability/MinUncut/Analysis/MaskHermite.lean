import Mathlib
import OAI.Computability.MinUncut.Estimates.MemLpMaskProject

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
local instance maskHermiteDualFintype {U : Type*}
    [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

def maskHermite (S : Finset R) (I : ι → ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) (c : ι → ℝ) : ℝ := maskProject S (fun D => hermiteComponent I u D c) B

omit [AddCommGroup W] [Module F₂ W] in
lemma memLp_maskHermite (S : Finset R) (I : ι → ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) : MemLp (maskHermite S I u B) 2 (γpi ι) :=
  memLp_maskProject S _ (fun _ => (memLp_psi I).mul_const _) B

lemma oddAtom_maskHermite_mean (r : R) (one : W) (S : Finset R) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    (𝔼 D, ∫ c, oddAtom r one (fun B => maskHermite S I u B c) D ∂γpi ι) ≤
      (2:ℝ)^Fintype.card R * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
  have hh : ∀ B, MemLp (hermiteComponent I u B) 2 (γpi ι) := fun B => (memLp_psi I).mul_const _
  have hi (D : Rest (W := W) r) := (memLp_oddAtom r one (maskHermite S I u)
    (memLp_maskHermite S I u) D).integrable (by norm_num)
  have hj (D : Rest (W := W) r) := (memLp_oddAtom r one (hermiteComponent I u) hh D).integrable (by norm_num)
  calc
    _ = ∫ c, (𝔼 D, oddAtom r one (fun B => maskHermite S I u B c) D) ∂γpi ι := (integral_expect _ hi).symm
    _ ≤ ∫ c, (2:ℝ)^Fintype.card R * (𝔼 D, oddAtom r one (fun B => hermiteComponent I u B c) D) ∂γpi ι := by
      apply integral_mono
      · simp only [Finset.expect_eq_sum_div_card]
        exact (integrable_finsetSum _ (fun D _ => hi D)).div_const _
      · simp only [Finset.expect_eq_sum_div_card]
        exact ((integrable_finsetSum _ (fun D _ => hj D)).div_const _).const_mul _
      · intro c
        exact oddAtom_maskProject_mean r one S (fun B => hermiteComponent I u B c)
    _ = (2:ℝ)^Fintype.card R * (𝔼 D, ∫ c, oddAtom r one (fun B => hermiteComponent I u B c) D ∂γpi ι) := by
      rw [integral_const_mul, integral_expect _ hj]
    _ ≤ (2:ℝ)^Fintype.card R * (𝔼 D, Real.sqrt (∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι)) := by
      exact mul_le_mul_of_nonneg_left (Finset.expect_le_expect (fun D _ =>
        oddAtom_hermiteComponent_mean r one I u hu D)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (expect_sqrt_le _ (fun _ => integral_nonneg (fun _ => sq_nonneg _))) (by positivity)
end MinUncut.RowNoise

end

end OAI
