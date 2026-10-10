import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.GreedyTree
import OAI.Combinatorics.ThinTrees.Encoding.OrderedGraph
import OAI.Combinatorics.ThinTrees.Iteration
import OAI.Combinatorics.ThinTrees.Sparsification.IterationPotential
import OAI.Combinatorics.ThinTrees.Sparsification.Step

namespace OAI

/-! Rational iteration. -/

section

namespace AlgorithmicThinTrees.Iteration
open Finset StrongThinTree StrongThinTree.MultiGraph GraphicHalf
open MetricTests MetricTests.RationalStep

def iterate (R : ℕ) : (fuel r d m : ℕ) →
    MultiGraph (d+1) m → Finset (Fin m)
  | 0,_,_,_,G => GreedyTree.tree G
  | fuel+1,r,d,_,G =>
    if R ≤ r then
      let A := sparsify G r
      OrderedGraph.liftEdges A
        (iterate R fuel (nextCount r) d A.card (OrderedGraph.restrict G A))
    else GreedyTree.tree G

def RoundBound (R : ℕ) : Prop := ∀r : ℕ, R ≤ r →
    ∀(d m : ℕ) (G : MultiGraph (d+1) m), 2 ≤ d+1 → G.TreePackable univ r →
      (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r ∧
      G.TreePackable (sparsify G r) (nextCount r) ∧
      (∀S : Finset (Fin (d+1)), ((G.cut (sparsify G r) S).card:ℝ) ≤
        (1/2+3*halfError r)*(G.cut univ S).card) ∧
      (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r

lemma iterate_bound {R : ℕ} (hR : 4 ≤ R) (hround : RoundBound R) (fuel r d m : ℕ)
    (G : MultiGraph (d+1) m) (hr : 1 ≤ r) (hfuel : r ≤ fuel)
    (hn : 2 ≤ d+1) (hp : G.TreePackable univ r) :
    G.SpanningTree (iterate R fuel r d m G) ∧
      ∀S : Finset (Fin (d+1)), ((G.cut (iterate R fuel r d m G) S).card:ℝ) ≤
        R*(potential r/(r:ℝ))*(G.cut univ S).card := by
  induction fuel generalizing r m with
  | zero => omega
  | succ fuel ih =>
    have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hRR : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    by_cases hlarge : R ≤ r
    · obtain ⟨_,hhalf,hpos,hpack,hcut,hratio⟩ := hround r hlarge d m G hn hp
      have hlt : nextCount r < r := by
        exact_mod_cast (show (nextCount r:ℝ)<(r:ℝ) by linarith only [hhalf,hrR])
      have ih' := ih (nextCount r) (sparsify G r).card (OrderedGraph.restrict G (sparsify G r))
        hpos (by omega) (OrderedGraph.restrict_packable G _ hpack)
      rw [iterate,ite_eq_left hlarge]
      refine ⟨(OrderedGraph.restrict_spanningTree G _ _).mp ih'.1,?_⟩
      intro S
      have ht := ih'.2 S
      rw [OrderedGraph.restrict_cut_card,OrderedGraph.restrict_cut_card,OrderedGraph.lift_univ] at ht
      have hcoef : 0 ≤ R*(potential (nextCount r)/(nextCount r:ℝ)) := by
        exact mul_nonneg hRR.le (div_nonneg (potential_pos _).le (Nat.cast_nonneg _))
      calc
        _ ≤ R*(potential (nextCount r)/(nextCount r:ℝ))*(G.cut (sparsify G r) S).card := ht
        _ ≤ R*(potential (nextCount r)/(nextCount r:ℝ))*
            ((1/2+3*halfError r)*(G.cut univ S).card) :=
          mul_le_mul_of_nonneg_left (hcut S) hcoef
        _ = R*(potential (nextCount r)/(nextCount r:ℝ)*(1/2+3*halfError r))*
            (G.cut univ S).card := by ring
        _ ≤ R*(potential r/(r:ℝ))*(G.cut univ S).card :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (coefficient_step (by omega) hpos hhalf hratio) hRR.le)
            (Nat.cast_nonneg _)
    · rw [iterate,ite_eq_right hlarge]
      refine ⟨GreedyTree.tree_correct G (packing_connected G (by omega) hp),?_⟩
      intro S
      have hrleR : (r:ℝ) ≤ R := by exact_mod_cast (show r ≤ R by omega)
      have hcoef : 1 ≤ R*(potential r/(r:ℝ)) := by
        rw [←mul_div_assoc]
        apply (le_div_iff₀ hrR).mpr
        have hh := mul_le_mul_of_nonneg_left (potential_one_le hr) hRR.le
        nlinarith only [hh,hrleR]
      have hc : ((G.cut (GreedyTree.tree G) S).card:ℝ) ≤ (G.cut univ S).card := by
        exact_mod_cast G.cut_card_le_full (GreedyTree.tree G) S
      exact hc.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hcoef)

def initialCount (k : ℕ) : ℕ := max 1 (k/2)
lemma initialCount_pos (k : ℕ) : 1 ≤ initialCount k := le_max_left _ _
lemma initialCount_lower (k : ℕ) : k ≤ 3*initialCount k := by
  unfold initialCount
  omega

lemma initial_packable {n m k : ℕ} (G : MultiGraph n m) (hn : 0 < n) (hk : 1 ≤ k)
    (hc : G.EdgeConnected k) : G.TreePackable univ (initialCount k) := by
  by_cases hk2 : 2 ≤ k
  · have hr : 0 < k/2 := Nat.div_pos hk2 (by norm_num)
    have he : initialCount k=k/2 := max_eq_right hr
    rw [he]
    apply G.edgeConnected_treePackable hr hn
    intro S hS hS'
    exact (show 2*(k/2) ≤ k by omega).trans (hc S hS hS')
  · have hconn : G.Connected univ := by
      intro S hS hS'
      apply card_pos.mp
      exact hk.trans (hc S hS hS')
    have he : initialCount k=1 := by unfold initialCount; omega
    rw [he]
    refine ⟨fun _ => GreedyTree.tree G,fun _ => ⟨subset_univ _,GreedyTree.tree_correct G hconn⟩,?_⟩
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

def tree (R k : ℕ) {d m : ℕ} (G : MultiGraph (d+1) m) : Finset (Fin m) :=
  iterate R (initialCount k) (initialCount k) d m G

theorem tree_correct : ∃R : ℕ, 4 ≤ R ∧ ∃C : ℝ, 0 < C ∧
    ∀(d m k : ℕ) (G : MultiGraph (d+1) m), 2 ≤ d+1 → 1 ≤ k → G.EdgeConnected k →
      G.SpanningTree (tree R k G) ∧
        ∀S : Finset (Fin (d+1)), ((G.cut (tree R k G) S).card:ℝ) ≤
          C/(k:ℝ)*(G.cut univ S).card := by
  obtain ⟨R,hR,hround⟩ := sparsification_correct
  have hRR : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  let C : ℝ := 3*R*Real.exp lossB
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨R,hR,C,hC,?_⟩
  intro d m k G hn hk hc
  have hr := initialCount_pos k
  obtain ⟨hT,hthin⟩ := iterate_bound hR hround (initialCount k) (initialCount k) d m G
    hr le_rfl hn (initial_packable G (by omega) hk hc)
  refine ⟨hT,fun S => (hthin S).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have hrR : (0:ℝ) < initialCount k := by exact_mod_cast hr
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hrR hkR).mpr
  have hrk : (k:ℝ) ≤ 3*(initialCount k:ℝ) := by exact_mod_cast initialCount_lower k
  have hx := mul_le_mul_of_nonneg_left (potential_le (initialCount k)) hRR.le
  have hm := mul_le_mul_of_nonneg_left hrk (mul_pos hRR (Real.exp_pos lossB)).le
  have hl := mul_le_mul_of_nonneg_right hx hkR.le
  dsimp [C]
  nlinarith only [hm,hl]

end AlgorithmicThinTrees.Iteration
end

end OAI
