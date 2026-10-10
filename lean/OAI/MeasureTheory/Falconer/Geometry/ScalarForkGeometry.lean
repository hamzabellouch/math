import OAI.MeasureTheory.Falconer.Recursion.ScalarBranchingLevel

namespace OAI

/-! A witnessed pair of regularized child centers separates their entire
 descendant fibers. This supplies the nonporous binary fork geometry. -/
namespace Falconer.Regularization

 theorem scalar_prefix_leaf_center_dist {N b : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hb : b ≤ N) {c u : CellPath 1}
    (hu : u ∈ prefixFiber L b c) :
    |scalarPathCenter u-scalarPathCenter c| ≤ (1/2:ℝ)^b := by
  classical
  have huL := (Finset.mem_filter.mp hu).1
  have huc := (Finset.mem_filter.mp hu).2
  have huN := (mem_cubePaths 1 N u).mp (hL huL)
  have hcc : c.take b = c := by rw [← huc,List.take_take,min_self]
  exact scalarPathCenter_same_parent huN hb (huc.trans hcc.symm)

 theorem scalar_fork_leaf_bounds {N a b k n : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hb : b ≤ N) (hlevel : ScalarBranchingLevel L a b k n)
    (hk : k ≠ 0) {p : CellPath 1} (hp : p ∈ L.image (List.take a)) :
    ∃ c ∈ prefixChildren L a b p, ∃ d ∈ prefixChildren L a b p, c ≠ d ∧
      ∀ u ∈ prefixFiber L b c, ∀ v ∈ prefixFiber L b d,
        6*(1/2:ℝ)^n ≤ |scalarPathCenter u-scalarPathCenter v| ∧
        |scalarPathCenter u-scalarPathCenter v| ≤ 18*(1/2:ℝ)^n := by
  rcases hlevel.fork_geometry p hp with hz | ⟨_,_,hsep,c,hc,d,hd,hcd,hpair⟩
  · exact False.elim (hk hz)
  refine ⟨c,hc,d,hd,hcd,?_⟩
  intro u hu v hv
  have hu0 := scalar_prefix_leaf_center_dist hL hb hu
  have hv0 := scalar_prefix_leaf_center_dist hL hb hv
  have hsc := hsep c hc d hd hcd
  have hscale : (1/2:ℝ)^b ≤ (1/2:ℝ)^n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hlevel.level_hi
  have hlow : |scalarPathCenter c-scalarPathCenter d| ≤
      |scalarPathCenter u-scalarPathCenter c|+|scalarPathCenter u-scalarPathCenter v|+
        |scalarPathCenter v-scalarPathCenter d| := by
    calc
      _ ≤ |scalarPathCenter c-scalarPathCenter u|+|scalarPathCenter u-scalarPathCenter d| := abs_sub_le _ _ _
      _ ≤ |scalarPathCenter c-scalarPathCenter u|+
          (|scalarPathCenter u-scalarPathCenter v|+|scalarPathCenter v-scalarPathCenter d|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (scalarPathCenter c) (scalarPathCenter u)]; ring
  have hupp : |scalarPathCenter u-scalarPathCenter v| ≤
      |scalarPathCenter u-scalarPathCenter c|+|scalarPathCenter c-scalarPathCenter d|+
        |scalarPathCenter v-scalarPathCenter d| := by
    calc
      _ ≤ |scalarPathCenter u-scalarPathCenter c|+|scalarPathCenter c-scalarPathCenter v| := abs_sub_le _ _ _
      _ ≤ |scalarPathCenter u-scalarPathCenter c|+
          (|scalarPathCenter c-scalarPathCenter d|+|scalarPathCenter d-scalarPathCenter v|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (scalarPathCenter d) (scalarPathCenter v)]; ring
  constructor <;> linarith

end Falconer.Regularization

end OAI
