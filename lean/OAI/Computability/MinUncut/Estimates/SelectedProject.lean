import Mathlib
import OAI.Computability.MinUncut.Analysis.MaskHermite

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
local instance selectedProjectDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

def selectedProject (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) (c : ι → ℝ) : ℝ :=
  ∑ j ∈ J, maskHermite j.1 j.2 u B c

omit [AddCommGroup W] [Module F₂ W] in
lemma memLp_selectedProject (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) :
    MemLp (selectedProject J u B) 2 (γpi ι) :=
  memLp_finsetSum _ (fun j _ => memLp_maskHermite j.1 j.2 u B)

lemma selectedProject_atom_mean (J : Finset (Finset R × (ι → ℕ))) (r : R) (one : W)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    (𝔼 D, ∫ c, oddAtom r one (fun B => selectedProject J u B c) D ∂γpi ι) ≤
      J.card * (2:ℝ)^Fintype.card R * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
  have hi (D : Rest (W := W) r) := (memLp_oddAtom r one (selectedProject J u)
    (memLp_selectedProject J u) D).integrable (by norm_num)
  have hj (j : Finset R × (ι → ℕ)) (D : Rest (W := W) r) :=
    (memLp_oddAtom r one (maskHermite j.1 j.2 u) (memLp_maskHermite j.1 j.2 u) D).integrable (by norm_num)
  calc
    _ ≤ 𝔼 D, ∫ c, (∑ j ∈ J, oddAtom r one (fun B => maskHermite j.1 j.2 u B c) D) ∂γpi ι := by
      apply Finset.expect_le_expect
      intro D _
      exact integral_mono (hi D) (integrable_finsetSum _ (fun j _ => hj j D))
        (fun c => oddAtom_sum J r one (fun j B => maskHermite j.1 j.2 u B c) D)
    _ = ∑ j ∈ J, 𝔼 D, ∫ c, oddAtom r one (fun B => maskHermite j.1 j.2 u B c) D ∂γpi ι := by
      simp_rw [integral_finsetSum _ (fun j _ => hj j _), Finset.expect_sum_comm]
    _ ≤ ∑ _j ∈ J, (2:ℝ)^Fintype.card R * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) :=
      Finset.sum_le_sum (fun j _ => oddAtom_maskHermite_mean r one j.1 j.2 u hu)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
end MinUncut.RowNoise
open scoped BigOperators

end

end OAI
