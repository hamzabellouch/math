import OAI.Probability.TraceReconstruction.Restoration

namespace OAI

/-!
# Testing

Multi-gadget family restoration and common-reference many-hypothesis statistics for every positive success level.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem hellingerSq_prod_same_right (P Q : FiniteLaw α) (R : FiniteLaw β) :
    (P.prod R).hellingerSq (Q.prod R)=P.hellingerSq Q := by
  unfold hellingerSq prod
  rw [Fintype.sum_prod_type]
  have he (a : α) (b : β) :
      (Real.sqrt (P.mass a*R.mass b)-Real.sqrt (Q.mass a*R.mass b))^2=
        (Real.sqrt (P.mass a)-Real.sqrt (Q.mass a))^2*R.mass b := by
    rw [Real.sqrt_mul (P.nonneg a),Real.sqrt_mul (Q.nonneg a),←sub_mul,mul_pow,
      Real.sq_sqrt (R.nonneg b)]
  simp_rw [he,←Finset.mul_sum,R.total,mul_one]

end FiniteLaw

def HellingerTracePair.suffix {q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (hq : q∈Set.Icc 0 1) (w : List Bool) :
    HellingerTracePair q (x++w) (y++w) E V := by
  let := C.finiteOutcome
  let R := listTraceLaw q hq w w.length le_rfl
  exact {
    Outcome := C.Outcome × BoundedTrace w.length
    finiteOutcome := inferInstance
    first := C.first.prod R
    second := C.second.prod R
    decode := fun z=>C.decode z.1++z.2.val
    first_simulation := by
      simpa only [add_zero] using C.first_simulation.append hq
        (listTraceLaw_simulates q hq w w.length le_rfl).approximate
    second_simulation := by
      simpa only [add_zero] using C.second_simulation.append hq
        (listTraceLaw_simulates q hq w w.length le_rfl).approximate
    bound := by rw [FiniteLaw.hellingerSq_prod_same_right]; exact C.bound }

theorem coordinateWord_length_constant {g S : ℕ} (w : Fin g→List Bool)
    (hw : ∀j,(w j).length=S) : (coordinateWord w).length=g*S := by
  induction g with
  | zero => simp [coordinateWord]
  | succ g ih =>
    rw [coordinateWord_succ,List.length_append,hw,ih (fun j=>w j.succ) (fun j=>hw j.succ)]
    simp [Nat.add_mul,Nat.add_comm]

theorem coordinateWord_injective_equal {g S : ℕ} (atom : Bool→List Bool)
    (hw : ∀τ,(atom τ).length=S) (ha : Function.Injective atom) :
    Function.Injective (fun θ : Fin g→Bool=>coordinateWord (fun j=>atom (θ j))) := by
  induction g with
  | zero => intro θ σ _; exact Subsingleton.elim _ _
  | succ g ih =>
    intro θ σ h
    change coordinateWord (fun j=>atom (θ j))=coordinateWord (fun j=>atom (σ j)) at h
    rw [coordinateWord_succ,coordinateWord_succ] at h
    have h0 := List.append_inj_left' h (by rw [coordinateWord_length_constant _ (fun j=>hw (θ j.succ)),coordinateWord_length_constant _ (fun j=>hw (σ j.succ))])
    have h1 := List.append_inj_right' h (by rw [coordinateWord_length_constant _ (fun j=>hw (θ j.succ)),coordinateWord_length_constant _ (fun j=>hw (σ j.succ))])
    have ht := ih h1
    funext j
    exact Fin.cases (ha h0) (fun k=>congrFun ht k) j

/-- A fixed family of all binary gadget choices, at exact requested length.
 Its common-zero member is uniformly close in m-sample TV to every member.
 This suffices for every fixed positive worst-case success probability. -/
theorem ConcreteLevelPair.restored_family {r q N Δ d ω F : ℝ} {hr : r∈Set.Icc 0 1}
    {i k : ℕ} (U : ConcreteLevelPair r hr N Δ d ω F i k)
    (hr1 : r<1) (hq : q∈Set.Icc 0 1) (hrq : r≤q) (hk : 1≤k)
    (g n : ℕ) (hN : (g:ℝ)*N≤n) :
    ∃W : (Fin g→Bool)→Word n,Function.Injective W ∧ ∀θ (m : ℕ),
      ((completeTraceLaw q hq (W θ)).product m).tv
        ((completeTraceLaw q hq (W (fun _=>false))).product m) ≤
          Real.sqrt ((m:ℝ)*g*N^(-d))+2*m*g*U.error := by
  have hlen : g*U.left.length≤n := by
    exact_mod_cast (mul_le_mul_of_nonneg_left U.length_upper (Nat.cast_nonneg g)).trans hN
  let atom := fun (τ : Bool)=>if τ then U.right else U.left
  have hw (τ : Bool) : (atom τ).length=U.left.length := by cases τ; rfl; exact U.equalLength.symm
  have ha : Function.Injective atom := by
    intro τ σ hh
    cases τ <;> cases σ
    · rfl
    · exact False.elim (U.different hh)
    · exact False.elim (U.different hh.symm)
    · rfl
  let tail := List.replicate (n-g*U.left.length) false
  let w := fun θ : Fin g→Bool=>coordinateWord (fun j=>atom (θ j))++tail
  have hl (θ : Fin g→Bool) : (w θ).length=n := by
    simp only [w,tail,List.length_append,List.length_replicate,coordinateWord_length_constant _ (fun j=>hw (θ j))]
    omega
  let W := fun θ=>wordOfLength (w θ) (hl θ)
  refine ⟨W,?_,?_⟩
  · intro θ σ hh
    have hh' := congrArg List.ofFn hh
    simp only [W,ofFn_wordOfLength] at hh'
    exact coordinateWord_injective_equal atom hw ha (List.append_cancel_right hh')
  · intro θ m
    let C := ((U.oracle.hellinger hk).mix hr θ (fun _ : Fin g=>false)).suffix hr tail
    have hV : (∑j : Fin g,if θ j=false then (0:ℝ) else 1) ≤ g := by
      calc
        _ ≤ ∑_j : Fin g,(1:ℝ) := Finset.sum_le_sum (fun j _=>by split_ifs <;> norm_num)
        _ = g := by simp
    have HH := C.degraded_sample_tv ⟨hr.1,hr1⟩ hq hrq m n (hl θ).le (hl (fun _=>false)).le
    change ((listTraceLaw q hq (w θ) n _).product m).tv ((listTraceLaw q hq (w (fun _=>false)) n _).product m) ≤ _ at HH
    rw [listTraceLaw_wordOfLength q hq _ (hl θ),listTraceLaw_wordOfLength q hq _ (hl (fun _=>false))] at HH
    apply HH.trans
    have hN0 : 0≤N := (Nat.cast_nonneg U.left.length).trans U.length_upper
    have hmul : (m:ℝ)*((∑j : Fin g,if θ j=false then (0:ℝ) else 1)*N^(-d)) ≤ m*g*N^(-d) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hN0 (-d))) (Nat.cast_nonneg m)
    have hs := Real.sqrt_le_sqrt hmul
    simpa only [mul_assoc] using add_le_add hs (le_refl (2*(m:ℝ)*(g*U.error)))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem product_map_expect (P : FiniteLaw α) (f : α→β) (m : ℕ)
    (F : (Fin m→β)→ℝ) :
    ((P.map f).product m).expect F=(P.product m).expect (fun z=>F (f∘z)) := by
  induction m with
  | zero =>
    simp only [expect,product,Fintype.prod_empty,one_mul,Fintype.sum_unique]
    congr 1
    exact Subsingleton.elim _ _
  | succ m ih =>
    rw [product_succ_expect,expect_map,product_succ_expect]
    apply congrArg P.expect
    funext a
    change ((P.map f).product m).expect (fun b=>F (Fin.cons (f a) b))=_
    rw [ih]
    congr 1
    funext z
    congr 1
    funext j
    exact Fin.cases rfl (fun _=>rfl) j

end FiniteLaw

theorem reconstructionSuccess_expect {n m : ℕ} (q : ℝ) (hq : q∈Set.Icc 0 1)
    (A : (Fin m→Trace)→Word n→ℝ) (x : Word n) :
    reconstructionSuccess q A x=((completeTraceLaw q hq x).product m).expect
      (fun z=>A (fun j=>(z j).val) x) := by
  rw [completeTraceLaw_mask,FiniteLaw.product_map_expect]
  rfl

theorem IsEstimator.le_one {n m : ℕ} {A : (Fin m→Trace)→Word n→ℝ}
    (hA : IsEstimator A) (z : Fin m→Trace) (x : Word n) : A z x≤1 := by
  rw [←hA.2 z]
  exact Finset.single_le_sum (fun y _=>hA.1 z y) (Finset.mem_univ x)

/-- Many-hypothesis testing using a common reference law. The decoder remains
 unrestricted, randomized and sees only complete traces. -/
theorem family_testing_bound {n m g : ℕ} {q s ε : ℝ} (hq : q∈Set.Icc 0 1)
    (W : (Fin g→Bool)→Word n) (hW : Function.Injective W)
    (htv : ∀θ,((completeTraceLaw q hq (W θ)).product m).tv
      ((completeTraceLaw q hq (W (fun _=>false))).product m)≤ε)
    (hm : SufficientBudget n q s m) : s≤1/(2:ℝ)^g+ε := by
  obtain ⟨A,hA,hs⟩ := hm
  let P := (completeTraceLaw q hq (W (fun _=>false))).product m
  have hθ (θ : Fin g→Bool) : s≤P.expect (fun z=>A (fun j=>(z j).val) (W θ))+ε := by
    have hb := FiniteLaw.expectation_diff_le_tv
      ((completeTraceLaw q hq (W θ)).product m) P
      (fun z=>A (fun j=>(z j).val) (W θ))
      (fun z=>⟨hA.1 _ _,hA.le_one _ _⟩)
    have hh := hs (W θ)
    rw [reconstructionSuccess_expect q hq] at hh
    change ((completeTraceLaw q hq (W θ)).product m).expect (fun z=>A (fun j=>(z j).val) (W θ)) - P.expect _ ≤ _ at hb
    linarith [htv θ]
  have hsum : (∑θ : Fin g→Bool,P.expect (fun z=>A (fun j=>(z j).val) (W θ)))≤1 := by
    unfold FiniteLaw.expect
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑z,P.mass z*1 := by
        apply Finset.sum_le_sum
        intro z _
        rw [←Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (P.nonneg z)
        calc
          _ = ∑x ∈ Finset.univ.image W,A (fun j=>(z j).val) x := by
            rw [Finset.sum_image (fun a _ b _ hab=>hW hab)]
          _ ≤ ∑x : Word n,A (fun j=>(z j).val) x := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun x _ _=>hA.1 _ _)
          _ = 1 := hA.2 _
      _ = 1 := by simp [P.total]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun θ _=>hθ θ)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  have hp : 0<(2:ℝ)^g := by positivity
  have he : (2:ℝ)^g*(1/(2:ℝ)^g)=1 := by field_simp
  nlinarith only [hh,hsum,he,hp]

end TraceReconstruction

end
end
end

end OAI
