import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowActualBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowActualFirstBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLiouville

namespace OAI

/-! Discharge the finite C⁴ flow input by the four variational estimates. -/

noncomputable section
open Set
open scoped ContDiff
namespace ContinuumCoulomb

def UniformFlowDerivativeBound (B C : ℝ) (k : ℕ) : Prop :=
  ∀ (U : Set (ℝ × Position)), IsOpen U →
    Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U →
    ∀ v : ℝ → Position → Position,
    ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U →
    (∀ j ≤ 4, ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × Position => v p.1 p.2) (t,x)‖ ≤ B) →
    ∀ G : Position → ℝ → Position, IsUnitTimeFlow v G →
    ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun y => G y t) x‖ ≤ C

theorem flow_uniform_derivatives (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ UniformFlowDerivativeBound B C 4 := by
  have hind : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, 0 < C ∧ UniformFlowDerivativeBound B C k := by
    intro k
    induction k with
    | zero =>
      intro _hk
      refine ⟨1,by norm_num,?_⟩
      intro U hU hs v hv hb G hG r hr hr'
      omega
    | succ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k
        refine ⟨Real.exp B,Real.exp_pos B,?_⟩
        intro U hU hs v hv hb G hG r hr hr' t ht x
        have heq : r = 1 := by omega
        subst r
        exact flow_actual_first_bound hU hs v hv G hG B hB (hb 1 (by norm_num)) t ht x
      · obtain ⟨M,hM,hMb⟩ := ih (by omega)
        let D := M+1
        let A := ((k:ℝ)*2^k*(k.factorial:ℝ)*B*D^(k+1))*Real.exp (B+1)
        have hD : 1 ≤ D := by dsimp [D]; linarith
        have hA : 0 ≤ A := by dsimp [A]; positivity
        refine ⟨M+A+1,by linarith,?_⟩
        intro U hU hs v hv hb G hG r hr hr' t ht x
        by_cases hrk : r ≤ k
        · exact (hMb U hU hs v hv hb G hG r hr hrk t ht x).trans (by linarith)
        · have heq : r = k+1 := by omega
          subst r
          have hprev : ∀ j, 1 ≤ j → j ≤ k → ∀ s ∈ Icc (0:ℝ) 1, ∀ y,
              ‖iteratedFDeriv ℝ j (fun z => G z s) y‖ ≤ D^j := by
            intro j hj hj' s hs' y
            apply (hMb U hU hs v hv hb G hG j hj hj' s hs' y).trans
            exact (show M ≤ D by dsimp [D]; linarith).trans
              (le_self_pow₀ hD (by omega))
          have h := flow_actual_higher_bound hU hs v hv G hG k (by omega) (by omega)
            B D hB (le_trans zero_le_one hD) hb hprev t ht x
          exact h.trans (by change A ≤ M+A+1; linarith)
  exact hind 4 le_rfl

theorem publishedC4FlowInput : PublishedC4FlowInput where
  regularity := fun _U hU hs v hv G hG => flow_regularity hU hs v hv G hG
  uniform := flow_uniform_derivatives

end ContinuumCoulomb

end

end OAI
