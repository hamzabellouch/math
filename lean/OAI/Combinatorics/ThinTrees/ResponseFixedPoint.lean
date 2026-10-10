import OAI.Combinatorics.ThinTrees.FixedPoint

namespace OAI

universe uE

section

noncomputable section
open Finset
namespace StrongThinTree

theorem response_fixed_point {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hc : Convex ℝ K)
    (R : K → K) {ε : ℝ} (hε : 0 < ε) :
    ∃X : K, ∃C : Finset K, ∃w : K → ℝ,
      (∀c ∈ C, 0 ≤ w c) ∧ (∑c ∈ C, w c)=1 ∧
      (∑c ∈ C, w c • (R c).val)=X.val ∧
      (∀c ∈ C, 0 < w c → dist c X < ε) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨U,_,hUfin,hUcover⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).finite_cover_balls hε
  let C := hUfin.toFinset
  have hcover (x : K) : ∃c ∈ C, dist x c < ε := by
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (hUcover (Set.mem_univ x))
    obtain ⟨hcU,hxc⟩ := Set.mem_iUnion.mp hc
    exact ⟨c,hUfin.mem_toFinset.mpr hcU,hxc⟩
  let bump (x c : K) : ℝ := max 0 (ε-dist x c)
  let total (x : K) : ℝ := ∑c ∈ C, bump x c
  have hbump (x c : K) : 0 ≤ bump x c := le_max_left _ _
  have ht (x : K) : 0 < total x := by
    obtain ⟨c,hc,hxc⟩ := hcover x
    exact sum_pos' (fun c _ => hbump x c) ⟨c,hc,lt_of_lt_of_le (sub_pos.mpr hxc) (le_max_right _ _)⟩
  let w (x c : K) : ℝ := bump x c/total x
  have hw (x c : K) : 0 ≤ w x c := div_nonneg (hbump x c) (ht x).le
  have hw1 (x : K) : (∑c ∈ C, w x c)=1 := by
    dsimp [w]
    rw [←sum_div]
    exact div_self (ht x).ne'
  have cb (c : K) : Continuous (fun x => bump x c) :=
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have ct : Continuous total := continuous_finsetSum _ (fun c _ => cb c)
  have cw (c : K) : Continuous (fun x => w x c) := (cb c).div ct (fun x => (ht x).ne')
  let F (x : K) : K := ⟨∑c ∈ C, w x c • (R c).val,
    hc.sum_mem (fun c _ => hw x c) (hw1 x) (fun c _ => (R c).property)⟩
  have cF : Continuous F := by
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ (fun c _ => (cw c).smul continuous_const)
  obtain ⟨X,hX⟩ := FixedPoint.compact_convex_fixed_point hK hne hc F cF
  refine ⟨X,C,w X,fun c _ => hw X c,hw1 X,congrArg Subtype.val hX,?_⟩
  intro c _ hpos
  have hp : 0 < bump X c := (div_pos_iff_of_pos_right (ht X)).mp hpos
  have hh : dist X c < ε := sub_pos.mp ((lt_max_iff.mp hp).resolve_left (lt_irrefl 0))
  simpa only [dist_comm] using hh

end StrongThinTree

end
end

end OAI
