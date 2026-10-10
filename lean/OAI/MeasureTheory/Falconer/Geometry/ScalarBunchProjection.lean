import OAI.MeasureTheory.Falconer.Measures.ScalarBunchProducts
import OAI.MeasureTheory.Falconer.Estimates.ScalarSubsetTransfer

namespace OAI

/-! Porous amplification on the original path set after actual bunch
 pruning. The hypotheses are explicit scalar scale inequalities. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_bunch_projection_gain_of_leaves {N top lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (hne : Q.Nonempty) (d k : ℕ → ℕ)
    (hd : Monotone d) (hdtop : d top ≤ N)
    (hleaf : ∀ p ∈ Q.image (List.take (d top)), (prefixFiber Q (d top) p).card = 1)
    (n H M : ScalarBunch → ℕ)
    (hlevels : ∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
      (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (4*(1/2:ℝ)^(n b)))
    (hH : ∀ b ∈ bs, 2 ≤ H b)
    (hmargin : ∀ b ∈ bs, n b+H b ≤ d b.stop)
    {K κ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ t ∈ B, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (hM : ∀ b ∈ bs, 83521 ≤ M b)
    (hbranch : ∀ b ∈ bs, 2*M b ≤ 2^(∑ i ∈ Finset.Ico b.start b.cut, k i))
    (hsmall : ∀ b ∈ bs, 16*(M b:ℝ)^4*K*((5/4:ℝ)*(1/2:ℝ)^(H b))^κ ≤ 1/4) :
    ∃ t ∈ B,
      (2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, k i)).sum) : ℝ)*
        Real.exp ((1/2:ℝ)*(bs.map (fun b => Real.log (M b:ℝ))).sum) ≤
      ((scalarCells ((1/2:ℝ)^N) ((Q.image scalarPathCenter)+
        (Q.image scalarPathCenter).image (fun x => t*x))).card : ℝ) := by
  classical
  have hgeo (b : ScalarBunch) (hb : b ∈ bs) :
      15*(1/2:ℝ)^(d b.stop) < 4*(1/2:ℝ)^(n b) ∧
      (1/2:ℝ)^N ≤ 5*(1/2:ℝ)^(d b.stop)/(4*(1/2:ℝ)^(n b)) := by
    exact scalar_dyadic_gap_geometry
      (by have h1 := hH b hb; have h2 := hmargin b hb; omega)
      ((hd (hchain.mem_bounds b hb).2).trans hdtop)
  let T := scalarBunchSeparatedTreeOfLeaves hchain Q hQ d k hd hdtop
    (fun b => 4*(1/2:ℝ)^(n b)) hlevels (fun b hb => by
      have hr : 0 < (1/2:ℝ)^(d b.stop) := by positivity
      linarith [(hgeo b hb).1]) hleaf
  let m : ℕ → ℕ := fun i => (bs.map M).getD i 1
  have hbound : ∀ i ≤ bs.length, ∀ x ∈ T.nodes i, |x| ≤ 1 := by
    intro i _hi x hx
    change x ∈ (Q.image (List.take (d (scalarBunchBoundary lo bs i)))).image scalarPathCenter at hx
    obtain ⟨p,_hp,rfl⟩ := Finset.mem_image.mp hx
    have hh := scalarPathCenter_unit p
    exact abs_le.mpr ⟨by linarith,hh.2⟩
  have hm : ∀ i < bs.length, 83521 ≤ m i := by
    intro i hi
    dsimp [m]
    rw [scalarBunchValue_at M 1 hi]
    exact hM bs[i] (List.getElem_mem hi)
  have hbr : ∀ i < bs.length, 2*m i ≤ T.branching i := by
    intro i hi
    change 2*(bs.map M).getD i 1 ≤
      (bs.map (fun b => 2^(∑ j ∈ Finset.Ico b.start b.cut, k j))).getD i 1
    rw [scalarBunchValue_at _ _ hi,scalarBunchValue_at _ _ hi]
    exact hbranch bs[i] (List.getElem_mem hi)
  have hgap : ∀ i < bs.length, 15*T.radius i < T.gap i := by
    intro i hi
    change 15*(1/2:ℝ)^(d (scalarBunchBoundary lo bs i)) <
      (bs.map (fun b => 4*(1/2:ℝ)^(n b))).getD i 1
    rw [(hchain.boundary_edges i hi).1,scalarBunchValue_at _ _ hi]
    exact (hgeo bs[i] (List.getElem_mem hi)).1
  have hscale : ∀ i < bs.length, (1/2:ℝ)^N ≤ 5*T.radius i/T.gap i := by
    intro i hi
    change (1/2:ℝ)^N ≤ 5*(1/2:ℝ)^(d (scalarBunchBoundary lo bs i))/
      (bs.map (fun b => 4*(1/2:ℝ)^(n b))).getD i 1
    rw [(hchain.boundary_edges i hi).1,scalarBunchValue_at _ _ hi]
    exact (hgeo bs[i] (List.getElem_mem hi)).2
  have hsm : ∀ i < bs.length, 16*(m i:ℝ)^4*K*(5*T.radius i/T.gap i)^κ ≤ 1/4 := by
    intro i hi
    change 16*((bs.map M).getD i 1:ℝ)^4*K*
      (5*(1/2:ℝ)^(d (scalarBunchBoundary lo bs i))/
        (bs.map (fun b => 4*(1/2:ℝ)^(n b))).getD i 1)^κ ≤ 1/4
    rw [(hchain.boundary_edges i hi).1,scalarBunchValue_at _ _ hi,scalarBunchValue_at _ _ hi]
    exact scalar_dyadic_bunch_small (hmargin bs[i] (List.getElem_mem hi)) hK hκ
      (hsmall bs[i] (List.getElem_mem hi))
  obtain ⟨q,hq⟩ := hne
  let x := scalarPathCenter (q.take (d lo))
  have hx : x ∈ T.nodes bs.length := by
    change x ∈ (Q.image (List.take (d (scalarBunchBoundary lo bs bs.length)))).image scalarPathCenter
    rw [scalarBunchBoundary_length]
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hq)
  obtain ⟨t,ht,hgain⟩ := T.grouped_projection_gain (by positivity) hK hbound B hB hBb hball
    m hm hbr hgap hscale hsm x hx x hx
  have hcard : (T.points bs.length x).card =
      2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, k i)).sum) := by
    rw [T.points_card (by positivity) bs.length le_rfl x hx]
    exact scalar_list_product_powers bs _
  have hlog : (∑ i ∈ Finset.range bs.length, Real.log (m i:ℝ)) =
      (bs.map (fun b => Real.log (M b:ℝ))).sum := scalar_list_sum_logs bs M
  rw [hcard,hlog] at hgain
  have hsub : T.points bs.length x ⊆ Q.image scalarPathCenter :=
    scalar_prefix_points_subset Q _ x
  have hsub' := scalarCells_mono ((1/2:ℝ)^N)
    (Finset.add_subset_add hsub (Finset.image_subset_image (f := fun x => t*x) hsub))
  refine ⟨t,ht,?_⟩
  have hnat := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub')
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hgain.trans hnat

 theorem scalar_bunch_projection_gain {N top lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (hne : Q.Nonempty) (d k : ℕ → ℕ)
    (hd : Monotone d) (hdtop : d top = N) (n H M : ScalarBunch → ℕ)
    (hlevels : ∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
      (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (4*(1/2:ℝ)^(n b)))
    (hH : ∀ b ∈ bs, 2 ≤ H b)
    (hmargin : ∀ b ∈ bs, n b+H b ≤ d b.stop)
    {K κ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ t ∈ B, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (hM : ∀ b ∈ bs, 83521 ≤ M b)
    (hbranch : ∀ b ∈ bs, 2*M b ≤ 2^(∑ i ∈ Finset.Ico b.start b.cut, k i))
    (hsmall : ∀ b ∈ bs, 16*(M b:ℝ)^4*K*((5/4:ℝ)*(1/2:ℝ)^(H b))^κ ≤ 1/4) :
    ∃ t ∈ B,
      (2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, k i)).sum) : ℝ)*
        Real.exp ((1/2:ℝ)*(bs.map (fun b => Real.log (M b:ℝ))).sum) ≤
      ((scalarCells ((1/2:ℝ)^N) ((Q.image scalarPathCenter)+
        (Q.image scalarPathCenter).image (fun x => t*x))).card : ℝ) := by
  apply scalar_bunch_projection_gain_of_leaves hchain Q hQ hne d k hd hdtop.le _
    n H M hlevels hH hmargin hK hκ B hB hBb hball hM hbranch hsmall
  rw [hdtop]
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 1 N q).mp (hQ hq)
  have ht : q.take N = q := by rw [← hlen,List.take_length]
  rw [ht,prefixFiber_leaf hQ hq]
  simp

end Falconer.Regularization

end OAI
