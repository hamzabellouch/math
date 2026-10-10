import OAI.MeasureTheory.Falconer.Estimates.ScalarNonporousTail
import OAI.MeasureTheory.Falconer.Estimates.ScalarClusterPorousGain
import OAI.MeasureTheory.Falconer.Recursion.ScalarTerminalFiberMass

namespace OAI

/-! Selecting the actual porous endpoints while retaining every point of
 every terminal fiber. Only the scalar parameter inequalities remain. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_actual_cluster_gain {B C P M : ℕ}
    (hC2 : 2 ≤ C) (hCB : C ≤ B) (hP : 18 ≤ P)
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i))
    {K κ : ℝ} (hK : 0 < K) (hκ : 0 ≤ κ)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (A : Finset ℝ) (hA : A.Nonempty) (hAb : ∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass A u t ≤ K*t^κ*(A.card : ℝ)) :
    let T := (scalarPorousLevels M B C k n).card
    ∃ e : ℕ → ℕ, StrictMono e ∧ e 0 = 0 ∧ e T ≤ M ∧
    ∃ lo : ℕ, ∃ bs : List ScalarBunch, ScalarBunchChain T lo bs ∧
      (∀ b ∈ bs, ScalarBunchGood (fun i => (scalarCompressedBranch e k i:ℝ)) (2*(P:ℝ)) b) ∧
      (∑ i ∈ Finset.range lo, (scalarCompressedBranch e k i:ℝ)) ≤ 2*(P:ℝ)*(lo:ℝ) ∧
      ((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        (scalarCompressedBranch e k i:ℝ))).sum ≤ 2*(P:ℝ)*((T-lo:ℕ):ℝ)/100) ∧
      (∑ i ∈ Finset.Ico (e T) M, k i) ≤ B*(scalarNonporousLevels M B C k n).card ∧
      ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
        L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
          scalarCompressedBranch e k i)).sum)*Q.card ∧
        ∃ t ∈ A,
          (2^(∑ i ∈ Finset.Ico (e T) M, k i):ℝ)*(2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut,
            scalarCompressedBranch e k i)).sum):ℝ)*
            Real.exp ((1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) ≤
          ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
            (L.image scalarPathCenter).image (fun x => t*x))).card : ℝ) := by
  classical
  let S := scalarPorousLevels M B C k n
  let T := S.card
  obtain ⟨e,he,he0,heT,heMem,heMax⟩ :=
    scalar_porous_endpoint_enumeration M S (Finset.filter_subset _ _)
  let n' := scalarEffectiveLevel B k n
  have hn' : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n' i) :=
    fun i hi => scalar_effective_branching_level k n (hlevel i hi)
  have hd : Monotone (fun i : ℕ => B*i) := fun _ _ hij => Nat.mul_le_mul_left B hij
  have hmass : 0 < 2^(∑ i ∈ Finset.Ico (e T) M, k i) := by positivity
  have hleaf : ∀ p ∈ L.image (List.take (B*e T)),
      (prefixFiber L (B*e T) p).card = 2^(∑ i ∈ Finset.Ico (e T) M, k i) :=
    scalar_uniform_terminal_mass L hL (fun i => B*i) k hd rfl
      (fun i hi => (hlevel i hi).children_card) heT
  have hends : ∀ j, 0 < j → j ≤ T → n' (e j-1)+C ≤ B*e j := by
    intro j hj hjT
    have hmem := heMem j hj hjT
    have hh := scalar_porous_margin hCB k n hmem
    have hepos : 0 < e j := by rw [← he0]; exact he hj
    rwa [Nat.sub_add_cancel hepos] at hh
  obtain ⟨lo,bs,hchain,hgoods,hprefix,hloss,Q,hQL,hQne,hcostQ,t,ht,hgain⟩ :=
    scalar_cluster_porous_gain hC2 hP L hL hne
      (Nat.mul_le_mul_left B heT) hmass hleaf k n'
      (fun i hi => hn' i (hi.trans_le heT)) e he rfl hends
      hK hκ hC hB A hA hAb hball
  have hweight := scalar_nonporous_tail_weight k n hlevel heMax
  refine ⟨e,he,he0,heT,lo,bs,hchain,hgoods,hprefix,hloss,hweight,
    Q,hQL,hQne,hcostQ,t,ht,?_⟩
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hgain

end Falconer.Regularization

end OAI
