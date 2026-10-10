import OAI.Combinatorics.GraphThreshold.ThresholdBounds
import OAI.Combinatorics.GraphThreshold.GraphCopies
import OAI.Combinatorics.GraphThreshold.GraphHierarchy
import OAI.Combinatorics.GraphThreshold.BernoulliMonotonicity
import OAI.Combinatorics.GraphThreshold.TreeCovering

namespace OAI

/-!
# The second Kahn–Kalai graph-threshold bounds

The graph-to-orbit bridge counts actual unlabelled subgraphs.  The hierarchy is
constructed from the constraints at the attained expectation threshold, and
covering one of its paths yields a copy of the original graph.
-/

noncomputable section

namespace LeanBlast.SecondKahnKalai

universe u

def FullStatement : Prop := SecondKahnKalaiStatement.{u}

theorem secondKahnKalaiBounds (n : ℕ) (V : Type u) [Fintype V]
    (H : SimpleGraph V) (hn : 2 ≤ n) (hcard : Fintype.card V ≤ n)
    (hedge : 1 ≤ edgeCount H) : SecondKahnKalaiBounds n H := by
  classical
  let q := expectationThreshold n H
  have hq : 0 < q := expectationThreshold_pos n H hcard hedge
  obtain ⟨E, hEcard, hEevent, hEconstraint⟩ :=
    exists_graphRepresentationWithConstraints n H hcard q
      (expectationThreshold_attained n H hcard).2
  have hEnonempty : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨k, m, T, hk, hdisjoint, hcapacity, hspread, hpositive, hgrowth, hlast, hpath⟩ :=
    exists_spread_orbit_tree (Equiv.Perm (Fin n)) E q hq hEnonempty
      (fun S hS _ => hEconstraint S hS)
  have hm : 0 < m (k - 1) := hpositive (k - 1) (by omega)
  have hmh : m (k - 1) ≤ edgeCount H := by omega
  let p := min 1 (2048 * Real.exp 50 * q * (1 + logTwo (edgeCount H : ℝ)))
  let pTree := min 1 (16 * Real.exp 50 * (128 * q) *
    (1 + Real.logb 2 (m (k - 1) : ℝ)))
  have hp : p ∈ Set.Icc 0 1 := graphThresholdParameter_mem_unitInterval q _ hq.le hedge
  have hpTree : pTree ∈ Set.Icc 0 1 := treeSamplingParameter_mem_unitInterval q _ hq.le hm
  have hpTree_le : pTree ≤ p :=
    treeSamplingParameter_le_graphParameter q _ _ hq.le hm hmh
  have hcovered : (2 / 3 : ℝ) ≤ bernoulliProbability pTree T.CoveredBy :=
    tree_covering T hk hdisjoint m hcapacity hpositive hgrowth (128 * q)
      (by positivity) hspread
  have hincrease : bernoulliProbability pTree T.CoveredBy ≤
      bernoulliProbability p T.CoveredBy := by
    apply bernoulliProbability_mono_parameter hpTree.1 hpTree_le hp.2 T.CoveredBy
    rintro W W' hWW' ⟨path, hpathW⟩
    exact ⟨path, hpathW.trans hWW'⟩
  have hevent : bernoulliProbability p T.CoveredBy ≤ containmentProbability n p H := by
    change (bernoulliLaw p hp.1 hp.2).prob T.CoveredBy ≤
      (bernoulliLaw p hp.1 hp.2).prob (fun W => 0 < (graphOfEdges W).copyCount H)
    apply FiniteLaw.prob_mono
    rintro W ⟨path, hpathW⟩
    exact (hEevent W).mpr ⟨T.pathUnion path, hpath path, hpathW⟩
  have hpc : criticalThreshold n H ≤ p := by
    apply criticalThreshold_le_of_probability n H hp
    exact (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans
      (hcovered.trans (hincrease.trans hevent))
  exact ⟨hpc, hpc.trans (graphThresholdParameter_le_vertexBound n H q hn hcard hedge hq.le)⟩

theorem secondKahnKalai : FullStatement.{u} := by
  intro n V inst H hn hcard hedge
  exact secondKahnKalaiBounds n V H hn hcard hedge

end LeanBlast.SecondKahnKalai

end

end OAI
