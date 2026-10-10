import OAI.MeasureTheory.Falconer.Geometry.ScalarClusterProjection
import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchBudget

namespace OAI

/-! Greedy porous gain retaining all original points in the terminal fibers. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_cluster_porous_gain {N B0 C P M T mass : ℕ}
    (hC2 : 2 ≤ C) (hP : 18 ≤ P) (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (hN : B0*M ≤ N) (hmass : 0 < mass)
    (hleaf : ∀ p ∈ L.image (List.take (B0*M)), (prefixFiber L (B0*M) p).card = mass)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B0*i) (B0*(i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T = M)
    (hporous : ∀ j, 0 < j → j ≤ T → n (e j-1)+C ≤ B0*e j)
    {K κ : ℝ} (hK : 0 < K) (hκ : 0 ≤ κ)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB0 : 800*(P:ℝ) ≤ κ*(B0:ℝ))
    (S : Finset ℝ) (hS : S.Nonempty) (hSb : ∀ t ∈ S, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass S u t ≤ K*t^κ*(S.card : ℝ)) :
    ∃ lo : ℕ, ∃ bs : List ScalarBunch, ScalarBunchChain T lo bs ∧
      (∀ b ∈ bs, ScalarBunchGood (fun i => (scalarCompressedBranch e k i:ℝ)) (2*(P:ℝ)) b) ∧
      (∑ i ∈ Finset.range lo, (scalarCompressedBranch e k i:ℝ)) ≤ 2*(P:ℝ)*(lo:ℝ) ∧
      ((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        (scalarCompressedBranch e k i:ℝ))).sum ≤ 2*(P:ℝ)*((T-lo:ℕ):ℝ)/100) ∧
      ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
        L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
          scalarCompressedBranch e k i)).sum)*Q.card ∧
        ∃ t ∈ S,
          (mass:ℝ)*(2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut,
            scalarCompressedBranch e k i)).sum):ℝ)*
            Real.exp ((1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) ≤
          ((scalarCells ((1/2:ℝ)^N) ((L.image scalarPathCenter)+
            (L.image scalarPathCenter).image (fun x => t*x))).card : ℝ) := by
  classical
  obtain ⟨lo,bs,hchain,hgoods,hprefix,hloss,_⟩ :=
    scalar_bunching_total_weights (fun i => (scalarCompressedBranch e k i:ℝ))
      (by positivity : 0 ≤ 2*(P:ℝ)) T
  have hd : Monotone (fun i : ℕ => B0*i) := fun _ _ hij => Nat.mul_le_mul_left B0 hij
  have hdN : ∀ i ≤ M, B0*i ≤ N := fun i hi => (Nat.mul_le_mul_left B0 hi).trans hN
  obtain ⟨Q,hQL,hQne,hsize,_,hleafQ,hQlevels⟩ := scalar_cluster_bunch_pruning hchain L hL hne
    (fun i => B0*i) k n hd hdN hleaf hlevel e he heT
  let w := scalarCompressedBranch e k
  let H := fun b : ScalarBunch => C+B0*(b.stop-b.cut)
  have hmargin : ∀ b ∈ bs, n (e b.cut-1)+H b ≤ B0*e b.stop := by
    intro b hb
    have hbc : b.cut ≤ T := b.cut_le_stop.trans (hchain.mem_bounds b hb).2
    exact scalar_bunch_margin e n he B0 C b
      (hporous b.cut (by have hh := b.start_lt_cut; omega) hbc)
  have hgroups : ∀ b ∈ bs, 2*scalarBunchGroup P b ≤
      2^(∑ i ∈ Finset.Ico b.start b.cut, w i) :=
    fun b hb => scalar_bunch_group_room w (by omega) b (hgoods b hb)
  have hsmall : ∀ b ∈ bs, 16*(scalarBunchGroup P b:ℝ)^4*K*
      ((5/4:ℝ)*(1/2:ℝ)^(H b))^κ ≤ 1/4 :=
    fun b hb => scalar_bunch_uniform_budget hK hC hB0 b (hgoods b hb)
  obtain ⟨t,ht,hgain⟩ := scalar_bunch_cluster_projection_gain hchain Q (hQL.trans hL) hQne
    (fun j => B0*e j) w (fun i j hij => Nat.mul_le_mul_left B0 (he.monotone hij))
    (by rw [heT]; exact hN) hmass hleafQ (fun b => n (e b.cut-1)) H (scalarBunchGroup P) hQlevels
    (fun b _ => by dsimp [H]; omega) hmargin hK.le hκ S hS hSb hball
    (fun b _ => scalar_bunch_group_large hP b) hgroups hsmall
  rw [hchain.group_log_sum] at hgain
  have hsub := Finset.image_subset_image (f := scalarPathCenter) hQL
  have hcover := scalarCells_mono ((1/2:ℝ)^N)
    (Finset.add_subset_add hsub (Finset.image_subset_image (f := fun x => t*x) hsub))
  refine ⟨lo,bs,hchain,hgoods,hprefix,hloss,Q,hQL,hQne,hsize,t,ht,?_⟩
  dsimp [w] at hgain
  have he : (1/2:ℝ)*((P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) =
      (1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2 := by ring
  rw [he] at hgain
  exact hgain.trans (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hcover))

end Falconer.Regularization

end OAI
