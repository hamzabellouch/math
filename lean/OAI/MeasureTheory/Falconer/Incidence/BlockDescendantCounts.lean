import OAI.MeasureTheory.Falconer.Recursion.ProfileBranchCounts

namespace OAI

/-! Local descendant counts in a retained block class, with both binning
losses explicit. These are the finite covering counts used by regularity. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockClass_descendant_count {N : ℕ} {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let T := prefixChildren C (blockDepth N B i) (blockDepth N B j) P
    ((blockProduct L F N B i p : ℝ)/(blockProduct L F N B j p : ℝ))/(2 : ℝ)^j ≤ T.card ∧
      (T.card : ℝ) ≤ (2 : ℝ)^i*((blockProduct L F N B i p : ℝ)/(blockProduct L F N B j p : ℝ)) := by
  classical
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  let T := prefixChildren C (blockDepth N B i) (blockDepth N B j) P
  have hab := blockDepth_antitone N B hji
  have hparent := blockClass_leaf_count hL B f K p hi hP
  have hparent' : (blockProduct L F N B i p : ℝ) ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      ((prefixFiber C (blockDepth N B i) P).card : ℝ) ≤ (2 : ℝ)^i*(blockProduct L F N B i p : ℝ) := by
    exact_mod_cast hparent
  have hchild (q : CellPath d) (hq : q ∈ T) :
      (blockProduct L F N B j p : ℝ) ≤ (prefixFiber C (blockDepth N B j) q).card ∧
      ((prefixFiber C (blockDepth N B j) q).card : ℝ) ≤ (2 : ℝ)^j*(blockProduct L F N B j p : ℝ) := by
    have hh := blockClass_leaf_count hL B f K p (hji.trans hi) (prefixChildren_mem_image hq)
    exact_mod_cast hh
  have hsum : ((prefixFiber C (blockDepth N B i) P).card : ℝ) =
      ∑ q ∈ T, ((prefixFiber C (blockDepth N B j) q).card : ℝ) := by
    exact_mod_cast prefixFiber_card_sum (C := C) hab P
  have hlow : (T.card : ℝ)*(blockProduct L F N B j p : ℝ) ≤
      ((prefixFiber C (blockDepth N B i) P).card : ℝ) := by
    rw [hsum]
    calc
      _ = ∑ _q ∈ T, (blockProduct L F N B j p : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hchild q hq).1
  have hupp : ((prefixFiber C (blockDepth N B i) P).card : ℝ) ≤
      (T.card : ℝ)*((2 : ℝ)^j*(blockProduct L F N B j p : ℝ)) := by
    rw [hsum]
    calc
      _ ≤ ∑ _q ∈ T, (2 : ℝ)^j*(blockProduct L F N B j p : ℝ) :=
        Finset.sum_le_sum fun q hq => (hchild q hq).2
      _ = _ := by simp
  have hpj : 0 < (blockProduct L F N B j p : ℝ) := by exact_mod_cast blockProduct_pos L F N B j p
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^j)).2
    apply (div_le_iff₀ hpj).2
    nlinarith [hparent'.1.trans hupp]
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hpj).2
    exact hlow.trans hparent'.2

end Falconer.Regularization

end OAI
