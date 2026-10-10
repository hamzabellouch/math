import OAI.Combinatorics.ContingencyTables.Transport.EdmondsKarpTrace

namespace OAI

/-!
# The shortest-augmentation bound

Charge an augmentation to a critical directed arc and its previous tail
label. A repeated directed arc has strictly larger label, so the charge
is injective into n×n×n.
-/
namespace ContingencyTables.EdmondsKarpBound
open PublishedEdmondsKarp EdmondsKarpDistance EdmondsKarpAugmentation EdmondsKarpTrace
open scoped Classical
noncomputable section
variable {n K : ℕ}

theorem shortest_trace_bound (c : Capacity n) (s t : Fin n) (F : Fin (K+1)→Flow n)
    (h : ∀ i : Fin K,ShortestAugmentation c s t (F i.castSucc) (F i.succ)) : K ≤ n^3 := by
  choose u v hu using (fun i : Fin K => critical_arc (h i))
  let code : Fin K→Fin n×Fin n×Fin n := fun i =>
    (u i,v i,⟨label c (F i.castSucc) s (u i),(hu i).2.2.2⟩)
  have hordered (i j : Fin K) (hij : i < j) (huv : u i=u j) (hvv : v i=v j) :
      label c (F i.castSucc) s (u i) < label c (F j.castSucc) s (u j) := by
    have hres : F j.castSucc (u i) (v i) < (c (u i) (v i):ℤ) := by
      simpa only [huv,hvv] using (hu j).1
    have hr := repeated_critical h i j hij (u i) (v i) (hu i).2.1 (hu i).2.2.1 hres
    rw [←huv]
    omega
  have hinj : Function.Injective code := by
    intro i j he
    have huij := congrArg Prod.fst he
    have hvij := congrArg (fun p : Fin n×Fin n×Fin n => p.2.1) he
    have hdij := congrArg (fun p : Fin n×Fin n×Fin n => p.2.2.val) he
    dsimp only [code] at huij hvij hdij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij|hji
    · exact (ne_of_lt (hordered i j hij huij hvij)) hdij
    · exact (ne_of_lt (hordered j i hji huij.symm hvij.symm)) hdij.symm
  have hc := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_fin,Fintype.card_prod,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hc

/-- Edmonds and Karp (1972), Theorem 1, in the exact integral-skew-flow
specialization for the sampling and counting algorithms. -/
theorem edmondsKarp1972Theorem1 : EdmondsKarp1972Theorem1 := by
  intro n c _ s t _ K F hF
  exact shortest_trace_bound c s t F hF.2.2

end
end ContingencyTables.EdmondsKarpBound

end OAI
