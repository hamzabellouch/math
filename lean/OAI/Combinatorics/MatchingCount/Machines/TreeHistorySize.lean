import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.EmpiricalDenom
import OAI.Combinatorics.MatchingCount.Algorithm.TreeScalingCorrect

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableScaling BitArithmetic

lemma fraction_weight_of_bound {B : ℕ} {q : ℚ} (h : FractionBound B (q:ℝ)) :
    TreeTyped.weight (TreeFraction.repr q)≤8*B.size+3 := by
  obtain ⟨hn,hd⟩:=h.num_den
  have hn':=Nat.size_le_size hn
  have hd':=Nat.size_le_size hd
  have h₁:=weight_nat_le q.num.natAbs
  have h₂:=weight_nat_le q.den
  simp only [TreeFraction.repr,weight_prod]
  omega

lemma vectorRep_weight_of_bound {n B : ℕ} (s : Fin n→ℚ)
    (h : ∀ i,FractionBound B (s i:ℝ)) :
    TreeTyped.weight (vectorRep s)≤n*(4*n.size+8*B.size+6)+1 := by
  have hb : ∀ i : Fin n,TreeTyped.weight (i.val,TreeFraction.repr (s i))≤4*n.size+8*B.size+5 := by
    intro i
    have h₁:=fraction_weight_of_bound (h i)
    have h₂:=weight_nat_le i.val
    have h₃:=Nat.size_le_size i.isLt.le
    simp only [weight_prod]
    omega
  unfold vectorRep
  rw [List.ofFn_eq_map]
  have hh:=weight_map_bound (as:=List.finRange n)
    (f:=fun i : Fin n=>(i.val,TreeFraction.repr (s i))) (N:=4*n.size+8*B.size+5)
    (fun i _=>hb i)
  simpa only [List.length_finRange] using hh

lemma history_vector_weight {G : GraphInput} [Nontrivial (Fin G.n)]
    (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    TreeTyped.weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)≤
      G.n*(4*G.n.size+8*((G.n+1).size+j*(G.n+1)*
        (19+(p.D+1).size+2*(p.S.size+
          Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1))+1)+6)+1 := by
  have h:=vectorRep_weight_of_bound ((FiniteTrial.layers p j hj).state x).scale
    (FiniteTrial.layers_scale_bits p j hj x)
  have h₁:=size_scaleBound p j
  have h₂:=size_matrixBound p
  have h₃:=size_empiricalBound p
  have hb : (p.scaleBound j).size≤
      (G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*(p.S.size+
        Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1))+1 := by
    calc
      _ ≤ (G.n+1).size+j*(G.n+1)*p.matrixBound.size+1 := h₁
      _ ≤ (G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*p.empiricalBound.size)+1 := by gcongr
      _ ≤ _ := by gcongr
  exact h.trans (by gcongr)

end MatchingFPRAS.ExecutableSource

end OAI
