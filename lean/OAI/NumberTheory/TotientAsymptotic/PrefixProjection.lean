import OAI.NumberTheory.TotientAsymptotic.ProjectedGrid
import OAI.NumberTheory.TotientAsymptotic.FirstCollision

namespace OAI

/-! Projection preserves the nonnegative simplex inequalities. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma sum_restrict_le {n N : ℕ} (hn : n ≤ N) (f : Fin N → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j : Fin n, f (Fin.castLE hn j)) ≤ ∑ j : Fin N, f j := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image (Fin.castLE hn), f j := by
      rw [Finset.sum_image]
      intro j _ k _ he
      exact Fin.ext (congrArg (fun z : Fin N => z.val) he)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hf j)

lemma enlargedSimplex_project {n N : ℕ} {x : ℝ} (hn : n ≤ N) {u : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N (B x) (xi x 0) (fun i => xi x (i.val+1))) :
    (fun j : Fin n => u (Fin.castLE hn j)) ∈
      enlargedSimplex n (B x) (xi x 0) (fun i => xi x (i.val+1)) := by
  refine ⟨fun j => hu.1 _,?_,?_⟩
  · intro i
    have hs := sum_restrict_le hn
      (fun j : Fin N => if Fin.castLE hn i < j then a (j.val-i.val)*u j else 0) (by
        intro j
        split_ifs with hij
        · exact mul_nonneg (a_pos (by have := hij; simp only [Fin.lt_def,Fin.val_castLE] at this; omega)).le (hu.1 j)
        · rfl)
    apply le_trans _ (hu.2.1 (Fin.castLE hn i))
    simpa only [Fin.castLE_mk,Fin.val_castLE,Fin.lt_def] using hs
  · exact (sum_restrict_le hn (fun j : Fin N => a (j.val+1)*u j)
      (fun j => mul_nonneg (a_pos (by omega)).le (hu.1 j))).trans hu.2.2

def tupleInnerPrefix {N : ℕ} (τ : TotientTuple N) (n : ℕ) : Fin n → ℕ :=
  fun j => if hj : j.val < N then τ.tail.primes ⟨j.val,hj⟩ else 1

lemma tupleInnerPrefix_eq {x t : ℝ} {H n : ℕ} (hPH : P H ≤ H) (hn : n ≤ R x H)
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ) (j : Fin n) :
    tupleInnerPrefix τ n j=(chosenRemainder x H τ.tail).primes
      ⟨j.val,by have := j.isLt; unfold R L at *; omega⟩ := by
  have hj : j.val < R x H := lt_of_lt_of_le j.isLt hn
  simp only [tupleInnerPrefix,dite_eq_left hj]
  have hp := congrArg PrefixDatum.primes (chosenRemainder_spec hτ.2.2.1).2
  have he := congrFun hp ⟨j.val,hj⟩
  change remainderPrime (chosenRemainder x H τ.tail) (j.val+1)=τ.tail.primes ⟨j.val,hj⟩ at he
  rw [← he]
  have hjL : 1 ≤ j.val+1 ∧ j.val+1 ≤ L x H := by
    have := j.isLt
    unfold R L at *
    omega
  simp [remainderPrime,hjL]

/-- Every inner prefix of an actual tuple retains all the projected bands
and simplex inequalities; the removed suffix terms were nonnegative. -/
lemma tupleInnerPrefix_geometry {x t : ℝ} {H K : ℕ} (hPH : P H ≤ H)
    (hn : R x K ≤ R x H) (hL : 0 < L x H)
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ) :
    (∀ j, (tupleInnerPrefix τ (R x K) j).Prime) ∧
    primePrefixCoord (tupleInnerPrefix τ (R x K)) ∈ prefixBandRegion x K ∧
    primePrefixCoord (tupleInnerPrefix τ (R x K)) ∈
      enlargedSimplex (R x K) (B x) (xi x 0) (fun j => xi x (j.val+1)) := by
  let η := chosenRemainder x H τ.tail
  have hη : IsBasicRemainder x H η := (chosenRemainder_spec hτ.2.2.1).1
  have hnL : R x K ≤ L x H := by unfold R L at *; omega
  have hcoord : primePrefixCoord (tupleInnerPrefix τ (R x K)) =
      fun j => primePrefixCoord η.primes (Fin.castLE hnL j) := by
    funext j
    unfold primePrefixCoord
    rw [tupleInnerPrefix_eq hPH hn hτ]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro j
    simp only [tupleInnerPrefix,dite_eq_left (lt_of_lt_of_le j.isLt hn)]
    exact (basic_prefix_data_positive hPH hτ.2.2.1).2 _
  · intro j
    rw [hcoord]
    have hh := (hη.2.1 (j.val+1) (Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩)).2
    change (9/10 : ℝ)*bandScale x (j.val+1) ≤
      remainderCoord x η ((Fin.castLE hnL j).val+1) ∧
      remainderCoord x η ((Fin.castLE hnL j).val+1) ≤ (11/10 : ℝ)*bandScale x (j.val+1) at hh
    rw [remainderCoord_fin] at hh
    exact hh
  · rw [hcoord]
    exact enlargedSimplex_project hnL (basic_remainder_enlargedSimplex hL hη)

end TotientAsymptotic

end

end OAI
