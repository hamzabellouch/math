import OAI.MeasureTheory.Falconer.Recursion.ProfileBranchCounts

namespace OAI

/-! Transfer a finite prefix-count bound through the retained block class,
keeping the exact class-selection and dyadic-bin losses. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockClass_ratio_le {N : ℕ} {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) {B : ℕ} (hB : 0 < B)
    (f : CellPath d → List ℕ) {p : CellPath d} (hp : p ∈ L)
    {i : ℕ} (hi : i ≤ N/B+1) {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hsize : (L.card : ℝ) ≤ A*(classLeaves L (blockLabel L N B f (N/B+1))
      (blockLabel L N B f (N/B+1) p)).card)
    (hprefix : ∀ P : CellPath d,
      ((prefixFiber L (blockDepth N B i) P).card : ℝ) ≤ M*(L.card : ℝ)) :
    let F := blockLabel L N B f (N/B+1)
    (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) ≤
      M*A*(2 : ℝ)^(N/B+1) := by
  classical
  let K := N/B+1
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hpC : p ∈ C := by simp [C,classLeaves,hp]
  have hnode : p.take (blockDepth N B i) ∈ C.image (List.take (blockDepth N B i)) :=
    Finset.mem_image.mpr ⟨p,hpC,rfl⟩
  have hc := (blockClass_leaf_count hL B f K p hi hnode).1
  have hroot := (blockClass_root_count hL hB f hp).2
  have hsub : prefixFiber C (blockDepth N B i) (p.take (blockDepth N B i)) ⊆
      prefixFiber L (blockDepth N B i) (p.take (blockDepth N B i)) := by
    intro q hq
    obtain ⟨hq,hqp⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,hqp⟩
  have hcard : ((prefixFiber C (blockDepth N B i) (p.take (blockDepth N B i))).card : ℝ) ≤
      ((prefixFiber L (blockDepth N B i) (p.take (blockDepth N B i))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hlo : (blockProduct L F N B i p : ℝ) ≤
      ((prefixFiber C (blockDepth N B i) (p.take (blockDepth N B i))).card : ℝ) := by exact_mod_cast hc
  have hrt : (C.card : ℝ) ≤ (2 : ℝ)^K*(blockProduct L F N B K p : ℝ) := by
    exact_mod_cast hroot
  have hpK : 0 < (blockProduct L F N B K p : ℝ) := by
    exact_mod_cast blockProduct_pos L F N B K p
  apply (div_le_iff₀ hpK).2
  calc
    _ ≤ M*(L.card : ℝ) := hlo.trans (hcard.trans (hprefix _))
    _ ≤ M*(A*(C.card : ℝ)) := mul_le_mul_of_nonneg_left hsize hM
    _ ≤ M*(A*((2 : ℝ)^K*(blockProduct L F N B K p : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrt hA) hM
    _ = _ := by ring

end Falconer.Regularization

end OAI
