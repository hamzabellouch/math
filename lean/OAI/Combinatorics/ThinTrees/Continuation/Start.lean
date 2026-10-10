import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.GraphRealization

namespace OAI

/-! Continuation start. -/

section

namespace AlgorithmicThinTrees.MetricTests
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma rankOne_le_laplacian (H : MultiGraph n m) (e : Fin m) :
    vecMulVec (H.incidence e) (H.incidence e) ≤ H.laplacian univ := by
  apply Finset.single_le_sum _ (mem_univ e)
  intro f _
  apply Matrix.nonneg_iff_posSemidef.mpr
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (H.incidence f)

lemma initial_resistance_le_one (H : MultiGraph n m) (hn : 0 < n)
    (hc : H.Connected univ) (e : Fin m) : resistance H (H.laplacian univ) e ≤ 1 := by
  have hh := (centered_resistance_order hn (domain_positive H hn hc (laplacian_mem_domain H))
    (incidence_sum H e) (by norm_num : (0:ℝ)<1)).mp
    (by simpa only [one_smul] using Matrix.le_iff.mp (rankOne_le_laplacian H e))
  simpa only [one_mul,MetricTests.resistance] using hh

lemma initial_ramp (H : MultiGraph n m) (hn : 0 < n) (hc : H.Connected univ)
    (e : Fin m) : ramp H (1/2) (H.laplacian univ) e=1 := by
  have hR := initial_resistance_le_one H hn hc e
  have hRp := centered_resistance_pos H hn (domain_positive H hn hc (laplacian_mem_domain H)) e
  have hi : 2 ≤ ((1/2)*resistance H (H.laplacian univ) e)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (by positivity : 0 < (1/2:ℝ)*resistance H (H.laplacian univ) e)).mpr
    linarith only [hR]
  unfold ramp cappedParameter
  rw [min_eq_left hi]
  norm_num

lemma packing_connected (H : MultiGraph n m) {r : ℕ} (hr : 0 < r)
    (hp : H.TreePackable univ r) : H.Connected univ := by
  intro S hS hS'
  apply card_pos.mp
  exact hr.trans_le (H.treePackable_edgeConnected hp S hS hS')

lemma packing_count_le_edges (H : MultiGraph n m) (hn : 2 ≤ n) {r : ℕ}
    (hp : H.TreePackable univ r) : r ≤ m := by
  let v : Fin n := ⟨0,by omega⟩
  have hS : ({v}:Finset (Fin n))≠univ := by
    intro he
    have hh := congrArg Finset.card he
    simp only [card_singleton,card_univ,Fintype.card_fin] at hh
    omega
  exact (H.treePackable_edgeConnected hp {v} (singleton_nonempty v) hS).trans
    (by simpa only [Fintype.card_fin] using Finset.card_le_univ (H.cut univ {v}))

lemma packing_partition_slack (H : MultiGraph n m) (hn : 0 < n) {r : ℕ}
    (hp : H.TreePackable univ r) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∀p, 0 ≤ slack H.left H.right (fun _ => 1+κ) r p := by
  obtain ⟨F,hF⟩ := Orientations.packed_exact_flow H hn hp
  have hf := hF.mono (fun e => show (1:ℝ) ≤ 1+κ by linarith only [hκ])
  have hfe : F.Feasible H (fun _ => 1+κ) r 0 := by
    refine ⟨hf.1,fun r e => ⟨(hf.2.1 r e).1,(hf.2.1 r e).2.1,(hf.2.1 r e).2.2.le⟩,
      fun r v => (hf.2.2.1 r v).le,?_⟩
    simpa only [sub_zero] using hf.2.2.2.ge
  intro p
  have hh := Orientations.flow_partition_bound H (fun _ => 1+κ) hfe p
  simpa only [zero_mul,sub_zero,sub_nonneg,slack] using hh

end AlgorithmicThinTrees.MetricTests

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

def initial (H : MultiGraph n m) (r : ℕ) : State n m :=
  ⟨1/2,r,qlap H,fun _ => 1⟩

lemma initial_invariant (H : MultiGraph n m) (hn : 0 < n) {r : ℕ}
    (hr : 0 < r) (hp : H.TreePackable univ r) : Invariant H (initial H r) := by
  have hc := packing_connected H hr hp
  have hm : (initial H r).realMatrix=H.laplacian univ := by
    ext i j
    exact cast_qlap H i j
  refine ⟨by norm_num [initial],hm.symm ▸ laplacian_mem_domain H,?_,?_⟩
  · intro e
    have hs : ((initial H r).scale:ℝ)=1/2 := by norm_num [initial]
    rw [hm,hs,initial_ramp H hn hc e]
    norm_num [initial]
  · simpa only [initial,Rat.cast_one,Rat.cast_natCast] using
      packing_partition_slack H hn hp (continuationBaseline m) (continuation_parameters m).1.le

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
