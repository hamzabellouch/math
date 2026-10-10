import OAI.Combinatorics.MatchingPSD.AdmissibleTables

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma predicateAverage_fiberEquiv {X : Type u_1} {Y : Type u_2} [Fintype X] [Fintype Y]
    (P : X → Prop) (Q : Y → Prop) (e : {x // P x} ≃ {y // Q y})
    (f : X → ℝ) (g : Y → ℝ) (h : ∀ x, f x.1 = g (e x).1) :
    predicateAverage P f = predicateAverage Q g := by
  rw [predicateAverage_eq_expect, predicateAverage_eq_expect]
  apply Fintype.expect_equiv e
  exact h

lemma coordinates_eq_of_cross_eq {V : Type u_3} [Fintype V]
    (z : V → Fin 3) (M N : Pairing V)
    (h : crossVector z M = crossVector z N) : ∀ a b, tableCoordinate z (a,b) M = tableCoordinate z (a,b) N := by
  have hb (a b : Fin 3) (hab : a ≠ b) : tableCoordinate z (a,b) M = tableCoordinate z (a,b) N := by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    fin_cases a <;> fin_cases b
    all_goals first | exact (hab rfl).elim | exact h0 | exact h1 | exact h2 |
      rwa [tableCoordinate_symm]
  intro a b
  by_cases hab : a = b
  · subst b
    rw [tableCoordinate_diagonal]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb'
    exact hb a b hb'.symm
  · exact hb a b hab

lemma table_eq_iff_cross {H : Type u_4} [Fintype H] [DecidableEq H]
    (z : H × Bool → Fin 3) (M N : Pairing (H × Bool)) :
    M.table z = N.table z ↔ crossVector z M = crossVector z N := by
  constructor
  · intro h
    funext i
    simp only [crossVector, crossCoordinate_eq_table, h]
  · intro h
    have hh := coordinates_eq_of_cross_eq z M N h
    have get (a b : Fin 3) : M.table z (threeEdgeType (a,b)) = N.table z (threeEdgeType (a,b)) := by
      have he := hh a b
      rw [tableCoordinate_eq_table, tableCoordinate_eq_table] at he
      split_ifs at he <;> exact_mod_cast (by linarith : (M.table z (threeEdgeType (a,b)) : ℝ) = N.table z (threeEdgeType (a,b)))
    funext i
    fin_cases i
    · exact get 0 0
    · exact get 0 1
    · exact get 0 2
    · exact get 1 1
    · exact get 1 2
    · exact get 2 2

lemma crossVector_transport {V : Type u_5} {W : Type u_6} [Fintype V] [Fintype W]
    (e : V ≃ W) (z : W → Fin 3) (M : Pairing V) :
    crossVector z (Pairing.transport e M) = crossVector (z ∘ e) M := by
  funext i
  exact tableCoordinate_transport e z (crossPair i) M

lemma histogram_comp_equiv {V : Type u_7} {W : Type u_8} {C : Type u_9} [Fintype V] [Fintype W] [DecidableEq C]
    (z : W → C) (e : V ≃ W) : histogram (z ∘ e) = histogram z := by
  funext c
  apply Fintype.card_congr
  exact e.subtypeEquiv (fun _ => Iff.rfl)

end MatchingSmoothing

end OAI
