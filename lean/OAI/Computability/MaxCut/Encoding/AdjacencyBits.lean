import Mathlib
import OAI.Computability.MaxCut.Encoding.VerticesBits
import OAI.Computability.MaxCut.Estimates.VecEquivSymmVal

namespace OAI

noncomputable section
namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad
open LongCode LongCode.InstanceAdapter CounterMachine.Expr
attribute [local instance] Classical.propDecidable

 theorem adjacency_bits {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (K L : ℕ)
    (anchor : Fin (g.vertices*2^q))
    (i j : Fin ((g.vertices*2^q)*(Unweighted.searchPrime (L*(g.vertices*2^q+1)^2))^6)) :
    let w := (ofInstance g).gridWeights t ht (vertexEquiv g.vertices q) anchor K
    let out := Unweighted.deterministicOutput L w (aggregate_symm _)
    out.graph.adj i j = decide (adjacency q t ht K L (bits g) i.val j.val ≠ 0) := by
  dsimp only
  let p := Unweighted.searchPrime (L*(g.vertices*2^q+1)^2)
  let : Fact p.Prime := ⟨(Unweighted.searchPrime_spec _).1⟩
  have hparam : param q L (bits g) = p := by simp [param,p]
  change decide (_ ∧ _ ∈ _) = _
  apply Bool.decide_congr
  rw [Unweighted.residue_membership]
  rw [weights_bits]
  have hf : ⌊(p:ℚ)*((weights q t ht K (bits g) (i.val/p^6) (j.val/p^6):ℕ):ℚ)/
      (gridSize q K (bits g):ℚ)⌋₊ = p*weights q t ht K (bits g) (i.val/p^6) (j.val/p^6)/gridSize q K (bits g) := by
    rw [← Nat.cast_mul,Nat.floor_div_natCast,Nat.floor_natCast]
  have hd : (Unweighted.dot ((Unweighted.vertexEquiv (g.vertices*2^q)).symm i).2
      ((Unweighted.vertexEquiv (g.vertices*2^q)).symm j).2).val = pairing p i.val j.val := by
    rw [Unweighted.dot_val]
    simp only [Unweighted.vertexEquiv_symm_second,pairing]
    rfl
  simp only [mul_div_assoc, Unweighted.vertexEquiv_symm_first] at *
  rw [hf,hd]
  have hne : ((Unweighted.vertexEquiv (g.vertices*2^q)).symm i).1 ≠
      ((Unweighted.vertexEquiv (g.vertices*2^q)).symm j).1 ↔ i.val/p^6 ≠ j.val/p^6 := by
    rw [ne_eq, Fin.ext_iff]
    rfl
  rw [hne]
  unfold adjacency
  rw [hparam]
  change (_ ∧ _) ↔ ((if i.val/p^6=j.val/p^6 then 0 else _) ≠ 0)
  by_cases hij : i.val/p^6=j.val/p^6
  · simp [hij]
  · simp only [ne_eq,hij,not_false_eq_true,true_and,ite_false]
    simp only [sum_eq_zero_iff,mem_range,ite_eq_right_iff,one_ne_zero,imp_false,not_forall,not_not]
    constructor
    · rintro ⟨r,hr,he⟩; exact ⟨r,hr,he⟩
    · rintro ⟨r,hr,he⟩; exact ⟨r,hr,he⟩
end OptimalMaxCut.RawGrid

end

end OAI
