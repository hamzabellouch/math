import OAI.Probability.InvariantIsing.Cavity.CavitySlowDepth

namespace OAI

/-! A single size sequence controls the two variance constants arising
from the GG and diagonal-minimum estimates. -/

noncomputable section
open Filter IsingPerceptron
open scoped Topology

namespace InvariantIsing

lemma cavity_choose_pair_depth_rates (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ℕ) (LG LD : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun r => diagonalContactRate (N (φ r)) (LD r)) atTop (𝓝 0) ∧
      ∀ j B, Tendsto (fun r => tensorContactGGRate (N (φ r)) j m (LG r) B) atTop (𝓝 0) := by
  let F := fun r k j => if j=0 then diagonalContactRate (N k) (LD r)
    else tensorContactGGRate (N k) (j-1) m (LG r) 1
  have hF r j : Tendsto (fun k => F r k j) atTop (𝓝 0) := by
    by_cases hj : j=0
    · simpa only [F, hj, ite_true, Function.comp_def] using (diagonalContactRate_tendsto (LD r)).comp hN
    · simpa only [F, ite_eq_right hj, Function.comp_def] using
        (tensorContactGGRate_tendsto (j-1) m (LG r) 1).comp hN
  obtain ⟨φ,hφ,hlim⟩ := cavity_choose_diagonal_errors F hF
  refine ⟨φ,hφ,?_,?_⟩
  · simpa only [F, ite_true] using hlim 0
  · intro j B
    have h := (hlim (j+1)).const_mul B
    have he r : B*F r (φ r) (j+1)=tensorContactGGRate (N (φ r)) j m (LG r) B := by
      have hj : j+1≠0 := Nat.succ_ne_zero j
      simp only [F, ite_eq_right hj, Nat.add_sub_cancel]
      unfold tensorContactGGRate contactGGRate
      ring
    simpa only [he, mul_zero] using h

end InvariantIsing

end

end OAI
