import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.SequentialLaw
import OAI.Combinatorics.RamseyFive.Entropy.RelationMassCrossed
import OAI.Combinatorics.RamseyFive.Geometry.Cores

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
noncomputable section
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
lemma eventWeight_map (p : Law Ω) (f : Ω → Ξ) (P : Ξ → Prop) :
    eventWeight (map p f) P = eventWeight p (fun x => P (f x)) := by
  have h := sum_map p f (fun z => if P z then (1:ℝ) else 0)
  simpa only [eventWeight,mul_ite,mul_one,mul_zero,ite_mul,one_mul,zero_mul] using h
end
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
noncomputable section
variable {K V α β : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype α] [Fintype β] {n : ℕ}

def tupleMarginal (p : Law (Fin n → α × β)) (i : Fin n) : Law (α × β) :=
  map p (fun x => x i)

def tupleCapture (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V) (good : Fin n → Fin n → α → β → Prop)
    (i j : Fin n) (x : Fin n → α × β) : Prop :=
  i<j ∧ capturedEvent (tupleMarginal p i) (tupleMarginal p j) w v (good i j)
    (x i).1 (x i).2 (x j).1 (x j).2

def tupleCollision (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V) (good : Fin n → Fin n → α → β → Prop)
    (i j : Fin n) : ℝ := eventWeight p (tupleCapture p v w good i j)

omit [FiniteDimensional K V] in
lemma tupleCollision_nonneg (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V) (good : Fin n → Fin n → α → β → Prop)
    (i j : Fin n) : 0≤tupleCollision p v w good i j := eventWeight_nonneg _ _

omit [FiniteDimensional K V] in
lemma tuple_flag_marginal (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V)
    (hp : ∀ x,0<p x → ∀ i,w (x i).2 (v (x i).1)=0)
    (i : Fin n) (a : α) (b : β) (h : 0<tupleMarginal p i (a,b)) : w b (v a)=0 := by
  obtain ⟨x,hx,hxi⟩ := map_positive p (fun x => x i) (a,b) h
  simpa only [hxi] using hp x hx i

theorem tuple_low_conflict (hdim : finrank K V=5)
    (p : Law (Fin n → α × β)) (v : α → V) (w : β → Module.Dual K V)
    (good : Fin n → Fin n → α → β → Prop)
    (hc : ∀ x,0<p x → ∀ i j,i<j → good i j (x i).1 (x j).2 →
      w (x i).2 (v (x j).1)=0) (i j : Fin n) (hij : i<j) :
    relationMass (good i j) (first (tupleMarginal p i)) (second (tupleMarginal p j)) ≤
      80004*(entropy (tupleMarginal p i)+entropy (tupleMarginal p j)-
        entropy (pair p (fun x => x i) (fun x => x j)) + tupleCollision p v w good i j) := by
  let pp := pair p (fun x => x i) (fun x => x j)
  have he : eventWeight pp (fun z => capturedEvent (first pp) (second pp) w v
      (good i j) z.1.1 z.1.2 z.2.1 z.2.2) = tupleCollision p v w good i j := by
    dsimp only [pp]
    rw [first_pair, second_pair, pair, eventWeight_map]
    unfold tupleCollision
    congr 1
    funext x
    simp only [tupleCapture,tupleMarginal,hij,true_and]
  have h := low_conflict_bound hdim pp w v (good i j) (by
    intro z hz hg
    obtain ⟨x,hx,he⟩ := map_positive p (fun x => (x i,x j)) z hz
    subst z
    exact hc x hx i j hij hg)
  rw [he] at h
  simpa only [pp,first_pair,second_pair,tupleMarginal,relationMass_crossed] using h

omit [FiniteDimensional K V] in
lemma tuple_collision_count (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V) (good : Fin n → Fin n → α → β → Prop) (M : ℝ)
    (hc : ∀ x,0<p x → ∀ i j,tupleCapture p v w good i j x →
      RectangleCharge
        (fun t => firstCore (tupleMarginal p t) w (x t).1)
        (fun t => (secondCore (K := K) (tupleMarginal p t) v (x t).2).dualAnnihilator)
        (fun t => (v (x t).1,w (x t).2)) i j)
    (hocc : ∀ x,0<p x → ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (v (x i).1) (w (x i).2) then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,tupleCollision p v w good i j)≤2*n*M := by
  apply le_trans _ (expected_rectangle_charge p
    (fun x t => firstCore (tupleMarginal p t) w (x t).1)
    (fun x t => (secondCore (K := K) (tupleMarginal p t) v (x t).2).dualAnnihilator)
    (fun x t => (v (x t).1,w (x t).2)) M hocc)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : p x=0
  · simp [hp]
  · have hp' : 0<p x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hp)
    by_cases ht : tupleCapture p v w good i j x
    · simp only [ht,ite_true,hc x hp' i j ht,mul_one,le_refl]
    · simp only [ht,ite_false]
      exact mul_nonneg (p.nonneg x) (by split_ifs <;> norm_num)

theorem closed_tuple_collision_bound (hdim : finrank K V=5) (r : ℕ) (hr : r≤5)
    (p : Law (Fin n → α × β)) (v : α → V) (w : β → Module.Dual K V)
    (good : Fin n → Fin n → α → β → Prop) (M : ℝ)
    (hp : ∀ x,0<p x → ∀ i,w (x i).2 (v (x i).1)=0)
    (hg : ∀ i j a y,good i j a y →
      0<first (tupleMarginal p i) a ∧ 0<second (tupleMarginal p j) y)
    (hU : ∀ i j a y, good i j a y → r ≤ finrank K (firstCore (tupleMarginal p i) w a))
    (hW : ∀ i j a y, good i j a y →
      5-r ≤ finrank K (secondCore (K := K) (tupleMarginal p j) v y))
    (hocc : ∀ x,0<p x → ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (v (x i).1) (w (x i).2) then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,tupleCollision p v w good i j)≤2*n*M := by
  apply tuple_collision_count p v w good M ?_ hocc
  intro x hx i j ht
  refine ⟨ht.1,Or.inl ?_⟩
  exact actual_integer_rectangle hdim r hr _ _ v w
    (tuple_flag_marginal p v w hp i) (tuple_flag_marginal p v w hp j)
    (good i j) (hg i j) (hU i j) (hW i j) _ _ _ _ ht.2

theorem high_tuple_collision_bound (hdim : finrank K V=5)
    (p : Law (Fin n → α × β)) (v : α → V) (w : β → Module.Dual K V)
    (good : Fin n → Fin n → α → β → Prop) (M : ℝ)
    (hp : ∀ x,0<p x → ∀ i,w (x i).2 (v (x i).1)=0)
    (hg : ∀ i j a y,good i j a y →
      0<first (tupleMarginal p i) a ∧ 0<second (tupleMarginal p j) y ∧ w y (v a)=0)
    (hU : ∀ i j a y, good i j a y → 2 ≤ finrank K (firstCore (tupleMarginal p i) w a))
    (hW : ∀ i j a y, good i j a y →
      2 ≤ finrank K (secondCore (K := K) (tupleMarginal p j) v y))
    (hocc : ∀ x,0<p x → ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (v (x i).1) (w (x i).2) then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,tupleCollision p v w good i j)≤2*n*M := by
  apply tuple_collision_count p v w good M ?_ hocc
  intro x hx i j ht
  refine ⟨ht.1,?_⟩
  exact actual_high_rectangles hdim _ _ v w
    (tuple_flag_marginal p v w hp i) (tuple_flag_marginal p v w hp j)
    (good i j) (hg i j) (hU i j) (hW i j) _ _ _ _ ht.2

theorem open_tuple_collision_zero (hdim : finrank K V=5) (r : ℕ) (hr : r≤6)
    (p : Law (Fin n → α × β)) (v : α → V) (w : β → Module.Dual K V)
    (good : Fin n → Fin n → α → β → Prop)
    (hU : ∀ i j a y, good i j a y → r ≤ finrank K (firstCore (tupleMarginal p i) w a))
    (hW : ∀ i j a y, good i j a y →
      6-r ≤ finrank K (secondCore (K := K) (tupleMarginal p j) v y))
    (i j : Fin n) : tupleCollision p v w good i j=0 := by
  apply Finset.sum_eq_zero
  intro x _
  have hn : ¬ tupleCapture p v w good i j x := by
    intro ht
    exact actual_open_impossible hdim r hr _ _ v w (good i j) (hU i j) (hW i j)
      _ _ _ _ ht.2
  simp only [hn,ite_false]

end
end SharpRamseyFive.LowConflict

end OAI
