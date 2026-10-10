import OAI.MeasureTheory.Falconer.Incidence.BlockPrefixRetention
import OAI.MeasureTheory.Falconer.Estimates.PlanarTreeUniformization

namespace OAI

/-! Re-regularize an actual retained subset. The resulting class retains
mass in every occupied block parent, with a single explicit global loss. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem refine_planar_block_class {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) (p : CellPath 2)
    (S : Finset (CellPath 2))
    (hSC : S ⊆ classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    (hS : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).card:ℝ) ≤
      M*(S.card:ℝ)) :
    ∃ q ∈ S,
      let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
      let G := blockLabel S N B (fun _ => []) K
      let T := classLeaves S G (G q)
      T ⊆ S ∧ T.Nonempty ∧ (C.card:ℝ) ≤ (M*((2*B+1:ℕ):ℝ)^K)*(T.card:ℝ) ∧
      ∀ i, i ≤ K → ∀ p₀ ∈ T.image (List.take (blockDepth N B i)),
        ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
          ((M*((2*B+1:ℕ):ℝ)^K)*(2:ℝ)^(2*i))*
            ((prefixFiber T (blockDepth N B i) p₀).card:ℝ) := by
  have hSN : S ⊆ cubePaths 2 N :=
    hSC.trans ((Finset.filter_subset _ _).trans hL)
  obtain ⟨q,hq,hsize⟩ := exists_large_planar_block_class hSN hS B K
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let G := blockLabel S N B (fun _ => []) K
  let T := classLeaves S G (G q)
  have hT : T ⊆ S := Finset.filter_subset _ _
  have hTne : T.Nonempty := ⟨q,by simp [T,classLeaves,hq]⟩
  have hsizeR : (S.card:ℝ) ≤ ((2*B+1:ℕ):ℝ)^K*(T.card:ℝ) := by exact_mod_cast hsize
  have hmassT : (C.card:ℝ) ≤ (M*((2*B+1:ℕ):ℝ)^K)*(T.card:ℝ) := by
    calc
      _ ≤ M*(S.card:ℝ) := hmass
      _ ≤ M*(((2*B+1:ℕ):ℝ)^K*(T.card:ℝ)) := mul_le_mul_of_nonneg_left hsizeR hM
      _ = _ := by ring
  refine ⟨q,hq,hT,hTne,hmassT,?_⟩
  intro i hi p₀ hp₀
  exact blockClass_prefix_retention hL hSN B f (fun _ => []) K p q (hT.trans hSC)
    (by positivity) hmassT hi hp₀

end Falconer.Regularization

end OAI
