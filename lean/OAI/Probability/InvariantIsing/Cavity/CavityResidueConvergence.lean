import OAI.Probability.InvariantIsing.Cavity.CavityResidueFamily
import Mathlib.Order.Filter.Finite

namespace OAI

/-! Finitely many arithmetic progressions exhaust all sufficiently large sizes. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_residue_tendsto {n : ℕ} (hn : 0 < n) (q : ℕ) (f : ℕ → ℝ) (L : ℝ)
    (h : ∀ t : Fin n, Tendsto (fun r : ℕ => f ((r+q)*n+t)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ r in atTop, ∀ t : Fin n, dist (f ((r+q)*n+t)) L < ε :=
    Filter.eventually_all.mpr (fun t => Metric.tendsto_nhds.mp (h t) ε hε)
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  apply eventually_atTop.mpr
  refine ⟨(R+q)*n,fun N hN => ?_⟩
  have hdiv : R+q ≤ N/n := (Nat.le_div_iff_mul_le hn).mpr hN
  let t : Fin n := ⟨N%n,Nat.mod_lt _ hn⟩
  have hr : R ≤ N/n-q := by omega
  have hEq : (N/n-q+q)*n+t=N := by
    dsimp only [t]
    rw [Nat.sub_add_cancel (by omega)]
    simpa only [Nat.mul_comm] using Nat.div_add_mod N n
  simpa only [hEq] using hR (N/n-q) hr t

end InvariantIsing

end

end OAI
