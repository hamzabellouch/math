import OAI.Combinatorics.ThinTrees.IterationBounds

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph

lemma cut_card_le_full {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m))
    (S : Finset (Fin n)) : (G.cut T S).card ≤ (G.cut univ S).card := by
  exact card_le_card (filter_subset_filter _ (subset_univ T))

theorem packing_thinness : ∃C : ℝ, 0 < C ∧ ∀r : ℕ, 1 ≤ r →
    ∀(n m : ℕ) (G : MultiGraph n m), 2 ≤ n → G.TreePackable univ r →
      ∃T : Finset (Fin m), G.SpanningTree T ∧
        ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
          ((G.cut T S).card:ℝ) ≤ C/(r:ℝ)*(G.cut univ S).card := by
  obtain ⟨R,hR,hstep⟩ := sparsification
  have hRR : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hI : ∀r : ℕ, 1 ≤ r → ∀(n m : ℕ) (G : MultiGraph n m),
      2 ≤ n → G.TreePackable univ r →
        ∃T : Finset (Fin m), G.SpanningTree T ∧
          ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
            ((G.cut T S).card:ℝ) ≤
              R*(iterationPotential r/(r:ℝ))*(G.cut univ S).card := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr n m G hn hp
      have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      by_cases hlarge : R ≤ r
      · obtain ⟨hnum,hstep'⟩ := hstep r hlarge
        obtain ⟨A,hA,hcuts⟩ := hstep' n m G hn hp
        have hsR : (0:ℝ) < stepCount r :=
          lt_of_lt_of_le (by positivity) hnum.lower
        have hs : 1 ≤ stepCount r := by exact_mod_cast hsR
        have hlt : stepCount r < r := by
          have hh : (stepCount r:ℝ) < r := by linarith [hnum.upper]
          exact_mod_cast hh
        obtain ⟨T,hT,hthin⟩ := ih (stepCount r) hlt hs n A.card (G.restrict A) hn
          (G.restrict_packable A hA)
        refine ⟨liftEdges A T,(G.restrict_spanningTree A T).mp hT,?_⟩
        intro S hS hS'
        have ht := hthin S hS hS'
        rw [G.restrict_cut_card,G.restrict_cut_card,lift_univ] at ht
        have hcoef : 0 ≤ R*(iterationPotential (stepCount r)/(stepCount r:ℝ)) :=
          mul_nonneg hRR.le (div_nonneg (iterationPotential_pos _).le hsR.le)
        calc
          _ ≤ R*(iterationPotential (stepCount r)/(stepCount r:ℝ))*(G.cut A S).card := ht
          _ ≤ R*(iterationPotential (stepCount r)/(stepCount r:ℝ))*
              ((1/2+3*splitTau r)*(G.cut univ S).card) :=
            mul_le_mul_of_nonneg_left (hcuts S hS hS') hcoef
          _ = R*(iterationPotential (stepCount r)/(stepCount r:ℝ)*(1/2+3*splitTau r))*
              (G.cut univ S).card := by ring
          _ ≤ R*(iterationPotential r/(r:ℝ))*(G.cut univ S).card :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (iteration_coefficient_step hnum) hRR.le)
              (Nat.cast_nonneg _)
      · obtain ⟨F,hF,_⟩ := hp
        let i : Fin r := ⟨0,by omega⟩
        refine ⟨F i,(hF i).2,?_⟩
        intro S _ _
        have hrleR : (r:ℝ) ≤ R := by exact_mod_cast (show r ≤ R by omega)
        have hcoef : 1 ≤ R*(iterationPotential r/(r:ℝ)) := by
          rw [←mul_div_assoc]
          apply (le_div_iff₀ hrR).mpr
          have hh := mul_le_mul_of_nonneg_left (iterationPotential_one_le hr) hRR.le
          nlinarith
        have hc : ((G.cut (F i) S).card:ℝ) ≤ (G.cut univ S).card := by
          exact_mod_cast G.cut_card_le_full (F i) S
        exact hc.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hcoef)
  refine ⟨R*Real.exp iterationB,mul_pos hRR (Real.exp_pos _),?_⟩
  intro r hr n m G hn hp
  obtain ⟨T,hT,hthin⟩ := hI r hr n m G hn hp
  refine ⟨T,hT,fun S hS hS' => (hthin S hS hS').trans ?_⟩
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [←mul_div_assoc]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (iterationPotential_le r) hRR.le) hrR.le

end StrongThinTree.MultiGraph

end
end

end OAI
