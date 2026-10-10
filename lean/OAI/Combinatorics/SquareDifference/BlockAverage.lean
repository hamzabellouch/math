import OAI.Combinatorics.SquareDifference.PositiveResidue

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma cyclic_ascent_of_start_ne {β : Type*} [LinearOrder β] (f : ℕ → β)
    (hperiod : f 24=f 0) (hne : f 0≠f 1) : ∃k<24,f k<f (k+1) := by
  by_contra hn
  have hd : ∀k<24,f (k+1)≤f k := by
    intro k hk
    exact le_of_not_gt (fun h => hn ⟨k,hk,h⟩)
  have hbound : ∀k,k≤23 → f (k+1)≤f 1 := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hd (k+1) (by omega)).trans (ih (by omega))
  have hf := hbound 23 (by omega)
  rw [hperiod] at hf
  exact hne (le_antisymm hf (hd 0 (by omega)))

lemma tuple_interval_ascent (a : TupleVertex → ℕ)
    (ha : a (cycleVertex 0)≠a (cycleVertex 1)) :
    ∃k<24,a (cycleVertex k)<a (cycleVertex (k+1)) := by
  apply cyclic_ascent_of_start_ne (fun k => a (cycleVertex k)) _ ha
  exact congrArg a (cycleVertex_period 0)

lemma cycleVertex_consecutive_ne (k : ℕ) : cycleVertex k≠cycleVertex (k+1) := by
  intro he
  have hpow : tupleCycle^k=tupleCycle^(k+1) := congrFun he (⟨0, by decide⟩ : Fin tupleBlocks)
  rw [pow_succ] at hpow
  exact tupleCycle_ne_one (mul_left_cancel (show tupleCycle^k*tupleCycle=tupleCycle^k*1 by simpa using hpow.symm))

lemma equal_choice_probability {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Nonempty I] [DecidableEq I] (u v : V) (huv : u≠v) :
    (𝔼 a : V → I,if a u=a v then (1:ℝ) else 0)=(Fintype.card I:ℝ)⁻¹ := by
  rw [expect_two_evals u v huv (fun x y => if x=y then (1:ℝ) else 0)]
  have he (x : I) : (𝔼 y : I,if x=y then (1:ℝ) else 0)=(Fintype.card I:ℝ)⁻¹ := by
    simp_rw [eq_comm]
    simp [expect_eq_sum_div_card]
  simp only [he,Fintype.expect_const]

lemma choice_average_bound {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Nonempty I] [DecidableEq I] (u v : V) (huv : u≠v)
    (F : (V → I) → ℝ) (B E : ℝ) (hE : 0≤E)
    (hb : ∀a,|F a|≤B) (hg : ∀a,a u≠a v → |F a|≤E) :
    |𝔼 a,F a|≤(Fintype.card I:ℝ)⁻¹*B+E := by
  apply (abs_expect_le _ _).trans
  calc
    _ ≤ 𝔼 a : V → I,((if a u=a v then (1:ℝ) else 0)*B+E) := by
      apply expect_le_expect
      intro a _
      by_cases ha : a u=a v
      · simp only [ha,ite_true,one_mul]
        exact (hb a).trans (le_add_of_nonneg_right hE)
      · simp only [ha,ite_false,zero_mul,zero_add]
        exact hg a ha
    _ = _ := by rw [expect_add_distrib,←expect_mul,Fintype.expect_const,equal_choice_probability u v huv]

lemma multilinearIntegral_scale_expect {V X I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Nonempty I] (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (f : V → I → X → ℝ) (c : ℝ) :
    multilinearIntegral Llaw (fun v x => c*(𝔼 i,f v i x))=
      c^(Fintype.card V)*(𝔼 a : V → I,multilinearIntegral Llaw (fun v => f v (a v))) := by
  unfold multilinearIntegral
  have he (z : V → X) : (∏v,c*(𝔼 i,f v i (z v)))=
      c^(Fintype.card V)*(𝔼 a : V → I,∏v,f v (a v) (z v)) := by
    rw [prod_mul_distrib,prod_const,card_univ]
    congr 1
    exact (expect_prod_pi (fun v i => f v i (z v))).symm
  simp_rw [he]
  rw [show (fun z : V → X => c^(Fintype.card V)*(𝔼 a : V → I,∏v,f v (a v) (z v)))=
    c^(Fintype.card V) • (fun z => 𝔼 a : V → I,∏v,f v (a v) (z v)) by rfl,
    map_smul,smul_eq_mul,linearMap_expect]

end SquareDifference

end

end OAI
