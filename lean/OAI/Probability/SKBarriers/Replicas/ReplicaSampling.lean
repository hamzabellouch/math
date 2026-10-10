import Mathlib
import OAI.Probability.SKBarriers.Interpolation.RestrictedConcentration
import OAI.Probability.SKBarriers.SpinGlass.FiniteProduct
import OAI.Probability.SKBarriers.SpinGlass.FiniteIndicators

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

namespace FiniteLaw
variable {X I : Type*} [Fintype X] [Fintype I] [DecidableEq I]
theorem iid_expect_involutions (P : FiniteLaw X) (T : I → X → X)
    (hT : ∀ i, Function.Involutive (T i)) (hP : ∀ i x, P.weight (T i x)=P.weight x)
    (f : (I → X) → ℝ) :
    (P.iid I).expect (fun z => f (fun i => T i (z i)))=(P.iid I).expect f := by
  let e : (I → X) ≃ (I → X) :=
    ⟨fun z i => T i (z i),fun z i => T i (z i),fun z => funext (fun i => hT i (z i)),fun z => funext (fun i => hT i (z i))⟩
  unfold expect iid pi
  apply Fintype.sum_equiv e
  intro z
  dsimp only [e,Equiv.coe_fn_mk]
  simp only [hP]

theorem iid_two_then_one (P : FiniteLaw X) (a b : I) (hab : a≠b) (f : (Fin 3 → X) → ℝ) :
    (P.iid I).expect (fun z => P.expect (fun x => f ![z a,z b,x]))=(P.iid (Fin 3)).expect f := by
  classical
  have hi : Function.Injective (![a,b] : Fin 2 → I) := by
    intro i j H
    fin_cases i <;> fin_cases j <;> simp_all
  have H := P.iid_expect_injective (![a,b] : Fin 2 → I) hi
    (fun z => P.expect (fun x => f ![z 0,z 1,x]))
  calc
    _ = (P.iid (Fin 2)).expect (fun z => P.expect (fun x => f ![z 0,z 1,x])) := H
    _ = _ := by
      rw [iid_expect_fin_succ P 2]
      congr 1
      funext z
      congr 1
      funext x
      congr 1
      funext i
      fin_cases i <;> simp [Fin.snoc]
end FiniteLaw

def orient {n : ℕ} (ε : Bool) (x : Config n) : Config n := if ε then flip x else x

@[simp] theorem orient_orient {n : ℕ} (ε : Bool) (x : Config n) : orient ε (orient ε x)=x := by
  cases ε <;> simp [orient]
@[simp] theorem gibbs_orient {n : ℕ} (β : ℝ) (J : Disorder n) (ε : Bool) (x : Config n) :
    gibbs β J (orient ε x)=gibbs β J x := by cases ε <;> simp [orient]
@[simp] theorem overlap_orient_abs {n : ℕ} (ε : Bool) (x y : Config n) :
    |overlap (orient ε x) y|=|overlap x y| := by
  cases ε
  · simp [orient]
  · change |overlap (flip x) y| = |overlap x y|
    rw [overlap_comm,overlap_flip_right,abs_neg,overlap_comm]

theorem iid_gibbs_replica {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    ((gibbsFiniteLaw β J).iid (Fin d)).prob (fun z => z∈S)=replicaGibbsMass β J S := by
  classical
  unfold FiniteLaw.prob FiniteLaw.expect FiniteLaw.iid FiniteLaw.pi gibbsFiniteLaw replicaGibbsMass
  simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem iid_gibbs_oriented_replica {n d : ℕ} (β : ℝ) (J : Disorder n)
    (ε : Fin d → Bool) (S : Finset (ReplicaConfig n d)) :
    ((gibbsFiniteLaw β J).iid (Fin d)).prob (fun z => (fun i => orient (ε i) (z i))∈S)=replicaGibbsMass β J S := by
  have H := (gibbsFiniteLaw β J).iid_expect_involutions (fun i => orient (ε i)) (fun i => orient_orient (ε i))
    (fun i z => gibbs_orient β J (ε i) z) (fun z => if z∈S then 1 else 0)
  simp only [FiniteLaw.expect_indicator_eq_prob] at H
  exact H.trans (iid_gibbs_replica β J S)

theorem bank_triple_oriented {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (a b c : I) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (ε₀ ε₁ ε₂ : Bool) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).prob (fun z => (![orient ε₀ (z a),orient ε₁ (z b),orient ε₂ (z c)] : ReplicaConfig n 3)∈S)=
      replicaGibbsMass β J S := by
  classical
  have hi : Function.Injective (![a,b,c] : Fin 3 → I) := by
    intro i j H
    fin_cases i <;> fin_cases j <;> simp_all
  have H := (gibbsFiniteLaw β J).iid_prob_injective (![a,b,c] : Fin 3 → I) hi
    (fun z => (fun i => orient (![ε₀,ε₁,ε₂] i) (z i))∈S)
  have he (z : I → Config n) : (fun i => orient (![ε₀,ε₁,ε₂] i) ((z ∘ ![a,b,c]) i))=
      (![orient ε₀ (z a),orient ε₁ (z b),orient ε₂ (z c)] : ReplicaConfig n 3) := by
    funext i; fin_cases i <;> rfl
  simp only [he] at H
  exact H.trans (iid_gibbs_oriented_replica β J _ S)

theorem bank_pair_vertex_oriented {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (a b : I) (hab : a≠b)
    (ε₀ ε₁ ε₂ : Bool) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).expect (fun z => (gibbsFiniteLaw β J).prob (fun x =>
      (![orient ε₀ (z a),orient ε₁ (z b),orient ε₂ x] : ReplicaConfig n 3)∈S))=
      replicaGibbsMass β J S := by
  have H := (gibbsFiniteLaw β J).iid_two_then_one a b hab
    (fun z => if (fun i => orient (![ε₀,ε₁,ε₂] i) (z i))∈S then 1 else 0)
  have he (z : I → Config n) (x : Config n) :
      (fun i => orient (![ε₀,ε₁,ε₂] i) ((![z a,z b,x] : ReplicaConfig n 3) i))=
      (![orient ε₀ (z a),orient ε₁ (z b),orient ε₂ x] : ReplicaConfig n 3) := by
    funext i; fin_cases i <;> rfl
  simp only [he,FiniteLaw.expect_indicator_eq_prob] at H
  exact H.trans (iid_gibbs_oriented_replica β J _ S)

end SK.Analytic

end
end

end OAI
