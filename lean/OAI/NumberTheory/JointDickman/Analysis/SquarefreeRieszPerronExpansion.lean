import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszGlobalDecay

namespace OAI

/-! # The full normalized Perron integral has the local all-order expansion -/
namespace JointDickman
open Complex Filter Asymptotics Finset
open scoped Topology

theorem squarefreeRiesz_perron_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z/2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun L : ℝ =>
        (VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  obtain ⟨A,hA,hglobal⟩ := squarefreeRiesz_global_decay hz.le hz1
  obtain ⟨c,hc,hc0,hlocal⟩ := squarefreeRiesz_perron_local_expansion hz hz1 hA
  refine ⟨c,hc,hc0,fun H => ?_⟩
  have h := ((hglobal (z-2-H)).isBigO).add (hlocal H)
  apply h.congr_left
  intro L
  ring

end JointDickman

end OAI
