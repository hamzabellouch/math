import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.UniformFiniteProbability

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma coordinateLayer_apply_at (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i≠j} → Bool) → Bool) (x : Slot d) :
    coordinateLayer d j c x j = (x j ^^ c (fun i => x i)) := by
  simp [coordinateLayer,Equiv.piSplitAt_symm_apply]

lemma coordinateLayer_apply_other (d : ℕ) (j i : Fin d) (hi : i≠j)
    (c : ({i : Fin d // i≠j} → Bool) → Bool) (x : Slot d) :
    coordinateLayer d j c x i = x i := by
  simp [coordinateLayer,Equiv.piSplitAt_symm_apply,hi]

def binaryPosition {d : ℕ} (x y : Slot d) (t : Fin (d+1)) : Slot d :=
  fun i => if i.val<t.val then y i else x i

def binaryPartialSweep (d : ℕ) (c : SweepCoins d) (t : Fin (d+1)) : Equiv.Perm (Slot d) :=
  ((List.ofFn (fun j => coordinateLayer d j (c j))).take t.val).reverse.prod

@[simp] lemma binaryPartialSweep_zero (d : ℕ) (c : SweepCoins d) : binaryPartialSweep d c 0=1 := by
  simp [binaryPartialSweep]

@[simp] lemma binaryPartialSweep_last (d : ℕ) (c : SweepCoins d) :
    binaryPartialSweep d c (Fin.last d)=binarySweep d c := by
  unfold binaryPartialSweep binarySweep
  rw [List.take_of_length_le (by simp)]

lemma binaryPartialSweep_succ (d : ℕ) (c : SweepCoins d) (j : Fin d) :
    binaryPartialSweep d c j.succ=coordinateLayer d j (c j)*binaryPartialSweep d c j.castSucc := by
  unfold binaryPartialSweep
  simp only [Fin.val_succ,Fin.val_castSucc]
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp only [List.reverse_append,List.reverse_singleton,List.prod_append,
    List.prod_singleton,List.getElem_ofFn,Fin.eta]

lemma singleCoordinate_trajectory {d : ℕ} {β : Fin d → Type*}
    (x : Fin (d+1) → ∀i, β i)
    (hmov : ∀j i : Fin d, i≠j → x j.succ i=x j.castSucc i)
    (t : Fin (d+1)) (i : Fin d) :
    x t i = if i.val<t.val then x (Fin.last d) i else x 0 i := by
  have hbefore : ∀t : Fin (d+1), t.val ≤ i.val → x t i=x 0 i := by
    intro t
    induction t using Fin.induction with
    | zero => intro _; rfl
    | succ j ih =>
      intro ht
      have hij : i≠j := by intro h; subst j; simp at ht
      rw [hmov j i hij,ih]
      exact Nat.le_trans (Nat.le_succ j.val) ht
  have hafter : ∀t : Fin (d+1), i.val<t.val → x t i=x (Fin.last d) i := by
    intro t
    induction t using Fin.reverseInduction with
    | last => intro _; rfl
    | cast j ih =>
      intro ht
      have hij : i≠j := by intro h; subst j; simp at ht
      rw [← hmov j i hij,ih]
      exact Nat.lt_succ_of_lt ht
  split_ifs with h
  · exact hafter t h
  · exact hbefore t (Nat.le_of_not_lt h)

lemma binarySweep_endpoint_iff (d : ℕ) (c : SweepCoins d) (x y : Slot d) :
    binarySweep d c x=y ↔ ∀j, c j (fun i => binaryPosition x y j.castSucc i)= (x j ^^ y j) := by
  constructor
  · intro he j
    have hp (t : Fin (d+1)) : binaryPartialSweep d c t x=binaryPosition x y t := by
      funext i
      rw [singleCoordinate_trajectory (fun t => binaryPartialSweep d c t x)
        (by intro j i hi; rw [binaryPartialSweep_succ,Equiv.Perm.mul_apply,
          coordinateLayer_apply_other d j i hi])]
      simp only [binaryPartialSweep_last,binaryPartialSweep_zero,Equiv.Perm.one_apply,he,binaryPosition]
    have hj := congrFun (hp j.succ) j
    rw [binaryPartialSweep_succ,Equiv.Perm.mul_apply,hp j.castSucc,coordinateLayer_apply_at] at hj
    simp only [binaryPosition,Fin.val_succ,Fin.val_castSucc,lt_self_iff_false,ite_false,
      Nat.lt_succ_self,ite_true] at hj
    cases hx : x j <;> cases hy : y j <;> cases hc : c j (fun i => binaryPosition x y j.castSucc i) <;>
      simp_all [binaryPosition]
  · intro he
    have hp (t : Fin (d+1)) : binaryPartialSweep d c t x=binaryPosition x y t := by
      induction t using Fin.induction with
      | zero => ext i; simp [binaryPosition]
      | succ j ih =>
        rw [binaryPartialSweep_succ,Equiv.Perm.mul_apply,ih]
        funext i
        by_cases hi : i=j
        · subst i
          rw [coordinateLayer_apply_at,he j]
          simp [binaryPosition]
        · rw [coordinateLayer_apply_other d j i hi]
          dsimp [binaryPosition]
          congr 1
          exact propext (by have hij : i.val≠j.val := fun h => hi (Fin.ext h); omega)
    have hy : binaryPosition x y (Fin.last d)=y := by ext i; simp [binaryPosition]
    simpa only [binaryPartialSweep_last,hy] using hp (Fin.last d)

lemma uniform_coin_evaluation {I : Type*} [Fintype I] [DecidableEq I] (i : I) (b : Bool) :
    (∑c : I → Bool, if c i=b then (Fintype.card (I → Bool):ℝ)⁻¹ else 0) = (1/2:ℝ) := by
  have h := Sparse.uniform_projection_probability (Equiv.piSplitAt i (fun _ : I => Bool)) b
  simpa only [Sparse.finiteProbability,Sparse.uniformWeight,Equiv.piSplitAt_apply,
    Fintype.card_bool,Nat.cast_ofNat,one_div,mul_ite,mul_one,mul_zero] using h

lemma uniform_independent_event {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    [∀j, Fintype (X j)] (P : ∀j, X j → Prop) :
    (∑x : ∀j, X j, if ∀j, P j (x j) then (Fintype.card (∀j, X j):ℝ)⁻¹ else 0) =
      ∏j, ∑a : X j, if P j a then (Fintype.card (X j):ℝ)⁻¹ else 0 := by
  have h := independent_event_weight (fun j (_ : X j) => (Fintype.card (X j):ℝ)⁻¹) P
  have hc : (∏j, (Fintype.card (X j):ℝ)⁻¹) = (Fintype.card (∀j, X j):ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib,← Nat.cast_prod,Fintype.card_pi]
  refine Eq.trans ?_ h
  apply Finset.sum_congr
  · ext x; simp only [Finset.mem_univ]
  intro x _
  split_ifs <;> simp only [hc]

lemma uniform_pi_coin_evaluation {J : Type*} [Fintype J] [DecidableEq J] {I : J → Type*}
    [∀j,Fintype (I j)] [∀j,DecidableEq (I j)] (i : ∀j,I j) (b : J → Bool) :
    (∑c : ∀j,I j → Bool, if ∀j,c j (i j)=b j then
      (Fintype.card (∀j,I j → Bool):ℝ)⁻¹ else 0) = (1/2:ℝ)^Fintype.card J := by
  have h := uniform_independent_event (X:=fun j => I j → Bool) (fun j a => a (i j)=b j)
  refine Eq.trans ?_ (Eq.trans h ?_)
  · apply Finset.sum_congr rfl
    intro c _
    by_cases hc : ∀j,c j (i j)=b j <;> simp [hc]
  · calc
      _ = ∏j, (1/2:ℝ) := by
        apply Finset.prod_congr rfl
        intro j _
        refine Eq.trans ?_ (uniform_coin_evaluation (i j) (b j))
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : c (i j)=b j <;> simp [hc]
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ]

lemma binary_one_card (d : ℕ) (x y : Slot d) :
    ∑σ, binaryLaw d σ * (if σ x=y then (1:ℝ) else 0) = (Fintype.card (Slot d):ℝ)⁻¹ := by
  rw [binaryLaw,finiteLaw_expectation]
  simp_rw [binarySweep_endpoint_iff]
  rw [Finset.mul_sum]
  simp only [mul_ite,mul_one,mul_zero]
  have h := uniform_pi_coin_evaluation (J:=Fin d)
    (I:=fun j => {i : Fin d // i≠j} → Bool)
    (fun j i => binaryPosition x y j.castSucc i) (fun j => (x j ^^ y j))
  have hc : (1/2:ℝ)^Fintype.card (Fin d) = (Fintype.card (Slot d):ℝ)⁻¹ := by
    simp [Slot,inv_pow,one_div]
  refine Eq.trans ?_ (h.trans hc)
  apply Finset.sum_congr
  · ext c; simp only [Finset.mem_univ]
  intro c _
  by_cases hh : ∀j, c j (fun i => binaryPosition x y j.castSucc i)= (x j ^^ y j)
  · simp only [hh]
  · simp only [hh,ite_false]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma uniform_one_card {X : Type*} [Fintype X] [DecidableEq X] (x y : X) :
    (∑σ : Equiv.Perm X, uniformLaw (Equiv.Perm X) σ * (if σ x=y then (1:ℝ) else 0)) =
      (Fintype.card X:ℝ)⁻¹ := by
  let A : Unit ↪ X := ⟨fun _ => x,fun _ _ _ => Subsingleton.elim _ _⟩
  let B : Unit ↪ X := ⟨fun _ => y,fun _ _ _ => Subsingleton.elim _ _⟩
  have h := assignmentWeight_uniform A B
  have he (σ : Equiv.Perm X) : Assigns A B σ ↔ σ x=y := by
    change (∀u : Unit, σ x=y) ↔ σ x=y
    simp only [forall_const]
  simp only [assignmentWeight,he,uniformLaw,mul_ite,mul_one,mul_zero,
    Fintype.card_unique,Nat.descFactorial_one] at h ⊢
  refine Eq.trans ?_ h
  apply Finset.sum_congr
  · ext σ; simp only [Finset.mem_univ]
  intro σ _
  split_ifs <;> simp only [Fintype.card_perm]

lemma line_one_card (d : ℕ) (z : ℝ) (x y : Slot d) :
    (∑σ, lineLaw d z σ * (if σ x=y then (1:ℝ) else 0)) = (Fintype.card (Slot d):ℝ)⁻¹ := by
  simp only [lineLaw,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [uniform_one_card (X:=Slot d) x y,binary_one_card d x y]
  ring

lemma line_one_card_ite (d : ℕ) (z : ℝ) (x y : Slot d) :
    (∑σ, if σ x=y then lineLaw d z σ else 0) = (Fintype.card (Slot d):ℝ)⁻¹ := by
  simpa only [mul_ite,mul_one,mul_zero] using line_one_card d z x y

end BinaryCoordinateSweeps

end

end OAI
