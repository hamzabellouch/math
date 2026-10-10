import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.Specification
import OAI.Combinatorics.ThinTrees.Sparsification.IterationRealization

namespace OAI

/-! Explicit algorithm. -/

section

namespace AlgorithmicThinTrees.Iteration
open StrongThinTree Finset GraphicHalf MetricTests.RationalStep
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack Stack

lemma tree_bound {R : ℕ} (hR : 4 ≤ R) (hb : RoundBound R)
    (d m k : ℕ) (G : MultiGraph (d+1) m) (hn : 2 ≤ d+1) (hk : 1 ≤ k)
    (hc : G.EdgeConnected k) :
    G.SpanningTree (tree R k G) ∧ ∀S : Finset (Fin (d+1)),
      ((G.cut (tree R k G) S).card:ℝ) ≤
        (3*R*Real.exp lossB)/(k:ℝ)*(G.cut univ S).card := by
  have hRR : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  obtain ⟨hT,hthin⟩ := iterate_bound hR hb (initialCount k) (initialCount k) d m G
    (initialCount_pos k) le_rfl hn (initial_packable G (by omega) hk hc)
  refine ⟨hT,fun S => (hthin S).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have hrR : (0:ℝ) < initialCount k := by exact_mod_cast initialCount_pos k
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hrR hkR).mpr
  have hrk : (k:ℝ) ≤ 3*(initialCount k:ℝ) := by exact_mod_cast initialCount_lower k
  have hx := mul_le_mul_of_nonneg_left (potential_le (initialCount k)) hRR.le
  have hm := mul_le_mul_of_nonneg_left hrk (mul_pos hRR (Real.exp_pos lossB)).le
  have hl := mul_le_mul_of_nonneg_right hx hkR.le
  nlinarith only [hm,hl]

theorem explicit_program : ∃R : ℕ, ∃C : ℝ, 0 < C ∧
    (∀p : Problem,2 ≤ p.d+1 → 1 ≤ p.r → p.G.EdgeConnected p.r →
      ThinTree C p.r p.G (tree R p.r p.G)) ∧
    (∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i,2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) →
      RunsPoly L (treeProgram R) a) := by
  obtain ⟨R,hR,hb⟩ := sparsification_correct
  obtain ⟨T,_,ht⟩ := sparsify_program_polynomial
  let R' := max R T
  have hR' : 4 ≤ R' := hR.trans (le_max_left _ _)
  have hb' : RoundBound R' := fun r hr => hb r ((le_max_left R T).trans hr)
  have hpos : (0:ℝ) < R' := by exact_mod_cast (show 0<R' by omega)
  refine ⟨R',3*R'*Real.exp lossB,by positivity,?_,?_⟩
  · intro p hn hk hc
    have h := tree_bound hR' hb' p.d p.m p.r p.G hn hk hc
    exact ⟨h.1,fun S _ _ => h.2 S⟩
  · exact fun a ha hp => runsPoly_tree hR' hb' (le_max_right R T) ht a ha hp

end AlgorithmicThinTrees.Iteration
end

end OAI
