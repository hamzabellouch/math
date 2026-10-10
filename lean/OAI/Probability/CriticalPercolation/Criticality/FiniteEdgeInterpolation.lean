import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.InterpolationUniform
import OAI.Probability.CriticalPercolation.GraphGeometry.RestrictVertices
import OAI.Probability.CriticalPercolation.Modular.FiniteClusterTransport

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem finite_edge_interpolation_measure [Fintype E]
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0<c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph ω).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real (G.twoClusterEvent (x 0) (x d) s)) :
    ∃ j<d, 0 < (G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s) ∧
      -Real.log ((G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s)) ≤
        interpolationConstant c ε *
          (Real.log (1/(G.law p).real (G.twoClusterEvent (x 0) (x d) s))+Nat.clog 2 d+1) := by
  let U : Set V := Set.range (fun j : Fin (d+1) => x j.val) ∪
    ⋃ e : E, {v | v ∈ G.ends e}
  have hUf : U.Finite := (Set.finite_range _).union
    (Set.finite_iUnion (fun e => by
      convert (G.ends e).toFinset.finite_toSet using 1
      ext v
      exact Sym2.mem_toFinset.symm))
  let : Fintype U := hUf.fintype
  have hU : ∀ e v, v∈G.ends e → v∈U := by
    intro e v hv
    exact Or.inr (Set.mem_iUnion.mpr ⟨e,hv⟩)
  let R := G.restrictVertices U hU
  let y (j : ℕ) : U := ⟨x (min j d),Or.inl ⟨⟨min j d,by omega⟩,rfl⟩⟩
  have hy (j : ℕ) (hj : j≤d) : (y j).val=x j := by simp only [y,min_eq_left hj]
  have hreach (j k : ℕ) (hj : j≤d) (hk : k≤d) :
      (R.law p).real {ω | (R.openGraph ω).Reachable (y j) (y k)} =
        (G.law p).real {ω | (G.openGraph ω).Reachable (x j) (x k)} := by
    change (G.law p).real _ = _
    congr 1
    ext ω
    exact (G.restrictVertices_reachable U hU ω (y j) (y k)).trans (by simp only [hy j hj,hy k hk,Set.mem_ofPred_eq])
  have htwo (j k : ℕ) (hj : j≤d) (hk : k≤d) :
      (R.law p).real (R.twoClusterEvent (y j) (y k) s) =
        (G.law p).real (G.twoClusterEvent (x j) (x k) s) := by
    change (G.law p).real _ = _
    congr 1
    ext ω
    exact (G.restrictVertices_twoClusterEvent U hU ω (y j) (y k) s).trans
      (by rw [hy j hj,hy k hk])
  have hconn' : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (R.law p).real {ω | (R.openGraph ω).Reachable (y j) (y k)} := by
    intro j k hj hk hjk
    rw [hreach j k (by omega) hk]
    exact hconn j k hj hk hjk
  have hδ' : 0 < (R.law p).real (R.twoClusterEvent (y 0) (y d) s) := by
    rwa [htwo 0 d (by omega) le_rfl]
  obtain ⟨j,hj,hpos,hcost⟩ := R.finite_interpolation_measure d y hd p hp hc hε hεp hεq hconn' s hδ'
  rw [htwo j (j+1) (by omega) (by omega)] at hpos hcost
  rw [htwo 0 d (by omega) le_rfl] at hcost
  exact ⟨j,hj,hpos,hcost⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
