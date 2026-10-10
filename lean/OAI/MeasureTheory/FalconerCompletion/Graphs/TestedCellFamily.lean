import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Estimates.AdjustedProfile

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

def TestedCellFamily (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (a g p : ℕ) (X : CellPath d) (S : Finset (CellPath d))
    (v : EuclideanSpace ℝ (Fin d)) (δ W K : ℝ) : Prop :=
  S ⊆ dyadicPaths p ∧ ∀ P ∈ S,
    P.take a = X ∧ 0 < ρ (treeCell P) ∧
    ∃ w : EuclideanSpace ℝ (Fin d), ‖w‖ = 1 ∧ dist v w ≤ δ ∧
      (fullParallelCount ρ g p P W w : ℝ) ≤ K

noncomputable def retainedPairs (S T : Finset (CellPath d))
    (v w x y : EuclideanSpace ℝ (Fin d)) (τ : ℝ) : Finset (CellPath d × CellPath d) :=
  (S.product T).filter fun z =>
    ‖graphPerpND v (treeCenter z.1-x)‖ ≤ τ ∧
    ‖graphPerpND w (treeCenter z.2-y)‖ ≤ τ ∧
    |inner ℝ (treeCenter z.1-x) v + inner ℝ (treeCenter z.2-y) w| ≤ τ

def RetainedDegreeTarget : Prop :=
  ∀ (d : ℕ) (ρ₁ ρ₂ : Measure (EuclideanSpace ℝ (Fin d)))
    (a g₁ g₂ p : ℕ) (X Y : CellPath d) (S T : Finset (CellPath d))
    (v w x y : EuclideanSpace ℝ (Fin d)) (δ τ W₁ W₂ K₁ K₂ : ℝ),
    a ≤ g₁ → a ≤ g₂ → g₁ ≤ p → g₂ ≤ p →
    ‖v‖ = 1 → ‖w‖ = 1 → 0 ≤ δ → 0 ≤ τ → 0 ≤ K₁ → 0 ≤ K₂ →
    2*τ+2*((d+1:ℝ)/(2:ℝ)^g₁)*δ ≤ W₁ →
    2*τ+2*((d+1:ℝ)/(2:ℝ)^g₂)*δ ≤ W₂ →
    TestedCellFamily ρ₁ a g₁ p X S v δ W₁ K₁ →
    TestedCellFamily ρ₂ a g₂ p Y T w δ W₂ K₂ →
    ((retainedPairs S T v w x y τ).card : ℝ) ≤
      min (((2:ℝ)^d)^(g₁-a)*K₁) (((2:ℝ)^d)^(g₂-a)*K₂) *
        (4*(2:ℝ)^p*τ+5)^d

end CurrentFalconer.TreeND
end
end

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

lemma graph_ancestor_count {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (X : CellPath d) (S : Finset (CellPath d)) (hS : S ⊆ dyadicPaths p)
    (hX : ∀ P ∈ S, P.take a = X) :
    (S.image (List.take g)).card ≤ (2^d)^(g-a) := by
  classical
  let U := S.image (List.take g)
  have hlen : ∀ Q ∈ U, Q.length = g := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hQ
    rw [List.length_take,(mem_dyadicPaths _ _).mp (hS hP),Nat.min_eq_left hgp]
  have hprefix : ∀ Q ∈ U, Q.take a = X := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hQ
    simpa only [List.take_take,Nat.min_eq_left hag] using hX P hP
  have hsub : U.image (List.drop a) ⊆ dyadicPaths (g-a) := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hQ
    simp only [mem_dyadicPaths,List.length_drop,hlen P hP]
  have hinj : Set.InjOn (List.drop a) (↑U : Set (CellPath d)) := by
    intro P hP Q hQ he
    calc
      P = P.take a ++ P.drop a := (List.take_append_drop a P).symm
      _ = Q.take a ++ Q.drop a := by rw [hprefix P hP,hprefix Q hQ,he]
      _ = Q := List.take_append_drop a Q
  calc
    _ = (U.image (List.drop a)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (dyadicPaths (d := d) (g-a)).card := Finset.card_le_card hsub
    _ ≤ _ := dyadicPaths_card_le _

theorem graph_candidates_card (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (X : CellPath d) (S : Finset (CellPath d))
    (v x : EuclideanSpace ℝ (Fin d)) {δ τ W K : ℝ}
    (hv : ‖v‖=1) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hW : 2*τ+2*((d+1:ℝ)/(2:ℝ)^g)*δ ≤ W)
    (htest : TestedCellFamily ρ a g p X S v δ W K) :
    (((S.filter fun P => ‖graphPerpND v (treeCenter P-x)‖ ≤ τ).card) : ℝ) ≤
      ((2:ℝ)^d)^(g-a)*K := by
  classical
  let F := S.filter fun P => ‖graphPerpND v (treeCenter P-x)‖ ≤ τ
  let U := F.image (List.take g)
  have hF : F ⊆ dyadicPaths p := fun P hP => htest.1 (Finset.mem_filter.mp hP).1
  have hparent : ∀ P ∈ F, P.take a = X :=
    fun P hP => (htest.2 P (Finset.mem_filter.mp hP).1).1
  have hfiber : ∀ Q ∈ U, (((F.filter fun P => P.take g = Q).card) : ℝ) ≤ K := by
    intro Q hQ
    obtain ⟨P₀,hP₀,hP₀Q⟩ := Finset.mem_image.mp hQ
    obtain ⟨_,_,w,hw,hvw,hcount⟩ := htest.2 P₀ (Finset.mem_filter.mp hP₀).1
    have hQlen : Q.length = g := by
      rw [← hP₀Q,List.length_take,(mem_dyadicPaths _ _).mp (hF hP₀),Nat.min_eq_left hgp]
    have hzero : treeCenter P₀ ∈ treeCell Q := by
      rw [← hP₀Q]
      exact treeCell_subset_take P₀ g (treeCenter_mem P₀)
    have hsub : (F.filter fun P => P.take g = Q) ⊆
        (dyadicPaths p).filter (fun P => 0 < ρ (treeCell P) ∧
          dist (treeCenter P) (treeCenter P₀) < 10*(d+1)/(2:ℝ)^g ∧
          ‖graphPerpND w (treeCenter P-treeCenter P₀)‖ ≤ W) := by
      intro P hP
      obtain ⟨hPF,hPQ⟩ := Finset.mem_filter.mp hP
      have hPS := (Finset.mem_filter.mp hPF).1
      have hmem : treeCenter P ∈ treeCell Q := by
        rw [← hPQ]
        exact treeCell_subset_take P g (treeCenter_mem P)
      have hdist : dist (treeCenter P) (treeCenter P₀) ≤ (d+1:ℝ)/(2:ℝ)^g := by
        simpa only [treeCell,hQlen] using ambientGridCell_dist_le hzero hmem
      have hball : dist (treeCenter P) (treeCenter P₀) < 10*(d+1)/(2:ℝ)^g := by
        apply hdist.trans_lt
        have hpos : 0 < (d+1:ℝ)/(2:ℝ)^g := by positivity
        calc
          (d+1:ℝ)/(2:ℝ)^g < 10*((d+1:ℝ)/(2:ℝ)^g) := by linarith
          _ = _ := by ring
      have htube := graph_witness_tubeND v w x (treeCenter P) (treeCenter P₀)
        hv hw hδ hdist hvw (Finset.mem_filter.mp hPF).2 (Finset.mem_filter.mp hP₀).2
      exact Finset.mem_filter.mpr ⟨hF hPF,(htest.2 P hPS).2.1,hball,htube.trans hW⟩
    exact (show (((F.filter fun P => P.take g = Q).card) : ℝ) ≤
      (fullParallelCount ρ g p P₀ W w : ℝ) from by
        exact Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcount
  have hU : (U.card : ℝ) ≤ ((2:ℝ)^d)^(g-a) := by
    exact_mod_cast graph_ancestor_count hag hgp X F hF hparent
  have he : (F.card : ℝ) = ∑ Q ∈ U, (((F.filter fun P => P.take g = Q).card) : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (List.take g) F
  calc
    _ = ∑ Q ∈ U, (((F.filter fun P => P.take g = Q).card) : ℝ) := he
    _ ≤ ∑ _Q ∈ U, K := Finset.sum_le_sum hfiber
    _ = (U.card : ℝ)*K := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hU hK

end CurrentFalconer.TreeND
end
end

end OAI
