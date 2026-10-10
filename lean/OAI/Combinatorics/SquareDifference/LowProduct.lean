import OAI.Combinatorics.SquareDifference.ActualIntervalPair

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section GenericLow

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma interval_low_product_bound (hinj : Function.Injective p)
    (Llaw : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀j F,(∀z,0≤F z) → 0≤Llaw j F) (hmass : ∀j,Llaw j (fun _ => 1)=1)
    (u v : V) (huv : u≠v) (a : V → ℕ) (L : ℕ) (f : V → ℕ → ℝ)
    (M : ℝ) (hM : 0≤M) (hf : ∀v n,|f v n|≤M) (T : ℕ)
    (s : Finset (Finset J)) (hcard : s.card≤T) (hs : ∀U∈s,∏j∈U,p j≤T)
    (F G : ResidueSpace p → ℝ) (E : ℝ) (hE : 0≤E)
    (hpair : ∀(B : Finset J),(∏j∈B,p j)≤T^(Fintype.card (OtherVertices u v)) →
      ∀z,lawDensity (tensorLaw Llaw) z≠0 →
      |tensorLaw Llaw (fun x => F (freezeCoordinates B (z u) (x u))*
        G (freezeCoordinates B (z v) (x v)))|≤E) :
    |multilinearIntegral (tensorLaw Llaw) (fun w => if w=u then F else if w=v then G else
      fun x => ∑U∈s,intervalPiece p (a w) L (f w) U x)|≤
      (M*(T:ℝ)^2)^(Fintype.card (OtherVertices u v))*E := by
  classical
  have he := multilinear_pair_expand (tensorLaw Llaw) u v huv F G
    (fun w (U : s) => intervalPiece p (a w.val) L (f w.val) U.val)
  simp only [dite_eq_ite] at he
  have hsum (w : V) (x : ResidueSpace p) :
      (∑U : s,intervalPiece p (a w) L (f w) U.val x)=∑U∈s,intervalPiece p (a w) L (f w) U x :=
    sum_coe_sort s (fun U => intervalPiece p (a w) L (f w) U x)
  simp_rw [hsum] at he
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  have ht : 0≤(M*T)^(Fintype.card (OtherVertices u v))*E := mul_nonneg (pow_nonneg (mul_nonneg hM (Nat.cast_nonneg T)) _) hE
  calc
    _ ≤ ∑U : OtherVertices u v → s,(M*T)^(Fintype.card (OtherVertices u v))*E := by
      apply sum_le_sum
      intro U _
      have hb := interval_piece_product_bound p hinj Llaw hpos hmass u v a L f M hM hf T
        (fun w => (U w).val) (fun w => hs _ (U w).property) F G E hE hpair
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hb
    _ = (s.card:ℝ)^(Fintype.card (OtherVertices u v))*((M*T)^(Fintype.card (OtherVertices u v))*E) := by
      rw [sum_const,card_univ,Fintype.card_fun,Fintype.card_coe,nsmul_eq_mul,Nat.cast_pow]
    _ ≤ (T:ℝ)^(Fintype.card (OtherVertices u v))*((M*T)^(Fintype.card (OtherVertices u v))*E) := by
      apply mul_le_mul_of_nonneg_right _ ht
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hcard) _
    _ = _ := by rw [←mul_assoc,←mul_pow]; congr 2; ring

end GenericLow

section Retained

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]

lemma retainedInterval_pair {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (a : TupleVertex → ℕ) (L Q T : ℕ)
    (u v : TupleVertex) (_ : u≠v) (f : TupleVertex → ℕ → ℝ) (w : TupleVertex) :
    retainedIntervalLift p a L Q T {u,v} f w =
      if w=u then intervalLift p (a u) L Q (f u) else
      if w=v then intervalLift p (a v) L Q (f v) else
      fun x => ∑U∈(liftSupportFamily p Q).filter (fun U => ∏j∈U,p j≤T),intervalPiece p (a w) L (f w) U x := by
  funext x
  by_cases hwu : w=u
  · subst w; simp only [retainedIntervalLift,retainedFamily,mem_insert,mem_singleton,true_or,ite_true,intervalLift]
  by_cases hwv : w=v
  · subst w; simp only [retainedIntervalLift,retainedFamily,mem_insert,mem_singleton,or_true,ite_true,hwu,ite_false,intervalLift]
  · simp only [retainedIntervalLift,retainedFamily,mem_insert,mem_singleton,hwu,hwv,false_or,ite_false]

lemma filteredFamily_card (hinj : Function.Injective p) (Q T : ℕ) :
    ((liftSupportFamily p Q).filter (fun U => ∏j∈U,p j≤T)).card≤T := by
  apply (card_le_card (show (liftSupportFamily p Q).filter (fun U => ∏j∈U,p j≤T)⊆liftSupportFamily p T from ?_)).trans
  · exact liftSupportFamily_card_le p hinj T
  · intro U hU
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hU).2⟩

end Retained

end SquareDifference

end

end OAI
