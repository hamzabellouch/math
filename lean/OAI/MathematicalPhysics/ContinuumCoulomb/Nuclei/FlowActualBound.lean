import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocalBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocalEquation
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowSliceBound

namespace OAI

/-! Transfer the quantitative jet estimate to the actual closed-interval flow. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_actual_higher_bound {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ j ≤ 4, ∀ t ∈ Icc (0:ℝ) 1, ∀ z,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × Position => v p.1 p.2) (t,z)‖ ≤ B)
    (hprev : ∀ j, 1 ≤ j → j ≤ k → ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => G y t) x‖ ≤ D^j)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Position) :
    ‖iteratedFDeriv ℝ (k+1) (fun y => G y t) x‖ ≤
      ((k:ℝ)*2^k*(k.factorial:ℝ)*B*D^(k+1)) * Real.exp (B+1) := by
  obtain ⟨H,W,O,hH,hW,hO,hx,hEq,hODE,hWv⟩ := flow_local_equation hU hslab v hv G hG x
  have hder (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (j : ℕ) :
      iteratedFDeriv ℝ j (fun y => G y s) x =
        iteratedFDeriv ℝ j (fun y => H (s,y)) x := by
    have heq : (fun y => G y s) =ᶠ[𝓝 x] (fun y => H (s,y)) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact hEq y hy s hs
    exact (heq.iteratedFDeriv ℝ j).eq_of_nhds
  rw [hder t ht (k+1)]
  apply flow_local_higher_bound H W hH hW O hO x hx
    (fun y hy => (hEq y hy 0 ⟨le_rfl,zero_le_one⟩).symm.trans (hG.1 y))
    hODE k hk0 hk B D hB hD
  · intro s hs j hj hj'
    apply (flow_slice_derivative_bound W hW j (by omega) s (H (s,x))).trans
    rw [←hEq x hx s hs,(hWv s hs).iteratedFDeriv ℝ j |>.eq_of_nhds]
    exact hb j (by omega) s hs (G x s)
  · intro s hs j hj hj'
    rw [←hder s hs j]
    exact hprev j hj hj' s hs x
  · exact ht

end ContinuumCoulomb

end

end OAI
