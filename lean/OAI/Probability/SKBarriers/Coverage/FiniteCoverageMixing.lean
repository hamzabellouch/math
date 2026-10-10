import Mathlib
import OAI.Probability.SKBarriers.Replicas.ReplicaSampling
import OAI.Probability.SKBarriers.SpinGlass.FiniteSampling

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic
namespace FiniteLaw

 theorem cover_mixed_mass {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteLaw X) (Q : FiniteLaw Y) (R : X → Y → Prop) (E : X → Prop)
    {a δ : ℝ} (ha : 0<a) (hcov : P.prob (fun x => Q.prob (R x)<a)≤δ) :
    P.prob E≤δ+Q.expect (fun y => P.prob (fun x => E x ∧ R x y))/a := by
  have H := P.expect_mono (f:=fun x => a*(if E x then 1 else 0))
    (g:=fun x => a*(if Q.prob (R x)<a then 1 else 0)+Q.prob (fun y => E x ∧ R x y)) (fun x => by
      by_cases hx : E x
      · simp only [hx,true_and,ite_true,mul_one]
        by_cases hc : Q.prob (R x)<a
        · simp only [ite_eq_left hc,mul_one]
          linarith only [Q.prob_nonneg (R x)]
        · simp only [ite_eq_right hc,mul_zero,zero_add]
          exact le_of_not_gt hc
      · simp only [hx,false_and,ite_false,mul_zero,prob_false,add_zero]
        split_ifs <;> simp only [mul_one,mul_zero] <;> linarith only [ha])
  rw [expect_const_mul,expect_add,expect_const_mul] at H
  simp only [expect_indicator_eq_prob] at H
  have he : P.expect (fun x => Q.prob (fun y => E x ∧ R x y))=
      Q.expect (fun y => P.prob (fun x => E x ∧ R x y)) := P.expect_expect_comm Q _
  rw [he] at H
  have HC := mul_le_mul_of_nonneg_left hcov ha.le
  apply (mul_le_mul_iff_right₀ ha).mp
  rw [mul_add,mul_div_cancel₀ _ ha.ne']
  nlinarith only [H,HC]

 theorem expect_involution {X : Type*} [Fintype X] (P : FiniteLaw X)
    (T : X → X) (hT : Function.Involutive T) (hP : ∀x,P.weight (T x)=P.weight x) (f : X → ℝ) :
    P.expect (fun x => f (T x))=P.expect f := by
  let e : X ≃ X := ⟨T,T,hT,hT⟩
  apply Fintype.sum_equiv e
  intro x
  change P.weight x*f (T x)=P.weight (T x)*f (T x)
  rw [hP]

 theorem iid_pair_expect {X : Type*} [Fintype X] (P : FiniteLaw X) (f : X → X → ℝ) :
    (P.iid (Fin 2)).expect (fun s => f (s 0) (s 1))=P.expect (fun x => P.expect (f x)) := by
  rw [iid_expect_fin_succ P 1]
  change (P.iid (Fin 1)).expect (fun s => P.expect (fun y => f (s 0) y))=P.expect (fun x => P.expect (f x))
  exact iid_expect_single P (0:Fin 1) (fun x => P.expect (f x))

end FiniteLaw

 theorem gibbs_prob_eq_sum {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (gibbsFiniteLaw β J).prob E=∑x,if E x then gibbs β J x else 0 := by
  simp only [FiniteLaw.prob,FiniteLaw.expect,gibbsFiniteLaw,mul_ite,mul_one,mul_zero]

 theorem gibbs_expect_flip {n : ℕ} (β : ℝ) (J : Disorder n) (f : Config n → ℝ) :
    (gibbsFiniteLaw β J).expect (fun v => f (flip v))=(gibbsFiniteLaw β J).expect f :=
  (gibbsFiniteLaw β J).expect_involution flip flip_flip (gibbs_flip β J) f

 theorem mixed_abs_neighbor_le_signed {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop)
    {q a₁ : ℝ} (haq : a₁<q) (v : Config n) :
    (gibbsFiniteLaw β J).prob (fun x => E x ∧ q≤|overlap x v|)≤
      (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ E x)+
        (gibbsFiniteLaw β J).prob (fun x => a₁<overlap (flip v) x ∧ E x) := by
  refine ((gibbsFiniteLaw β J).prob_mono (fun x hx => ?_)).trans ((gibbsFiniteLaw β J).prob_or _ _)
  rw [overlap_comm] at hx
  rcases le_abs.mp hx.2 with h|h
  · exact Or.inl ⟨haq.trans_le h,hx.1⟩
  · apply Or.inr
    refine ⟨?_,hx.1⟩
    rw [overlap_comm,overlap_flip_right,overlap_comm]
    linarith only [haq,h]

 theorem covered_mixed_mass_le_signed_average {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop)
    {q a₁ a δ : ℝ} (haq : a₁<q) (ha : 0<a)
    (hcov : (gibbsFiniteLaw β J).prob (fun x => (gibbsFiniteLaw β J).prob (fun y => q≤|overlap x y|)<a)≤δ) :
    (gibbsFiniteLaw β J).prob E≤δ+(2/a)*(gibbsFiniteLaw β J).expect (fun v =>
      (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ E x)) := by
  have H := (gibbsFiniteLaw β J).cover_mixed_mass (gibbsFiniteLaw β J) (fun x y => q≤|overlap x y|) E ha hcov
  have HB := (gibbsFiniteLaw β J).expect_mono (fun v => mixed_abs_neighbor_le_signed β J E haq v)
  rw [FiniteLaw.expect_add] at HB
  have HF := gibbs_expect_flip β J (fun v => (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ E x))
  rw [HF] at HB
  refine H.trans ?_
  apply add_le_add_right
  have HD := div_le_div_of_nonneg_right HB ha.le
  refine HD.trans_eq ?_
  ring

def pairStripSet (n : ℕ) (a₀ a₁ : ℝ) : Finset (ReplicaConfig n 2) :=
  Finset.univ.filter (fun s => a₀≤overlap (s 0) (s 1) ∧ overlap (s 0) (s 1)≤a₁)

 theorem pairStrip_expect {n : ℕ} (β : ℝ) (J : Disorder n) (a₀ a₁ : ℝ) :
    (gibbsFiniteLaw β J).expect (fun v => (gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁))=
      replicaGibbsMass β J (pairStripSet n a₀ a₁) := by
  rw [← iid_gibbs_replica β J (pairStripSet n a₀ a₁)]
  simp only [pairStripSet,Finset.mem_filter,Finset.mem_univ,true_and,FiniteLaw.prob]
  convert ((gibbsFiniteLaw β J).iid_pair_expect (fun v x => if a₀≤overlap v x ∧ overlap v x≤a₁ then 1 else 0)).symm using 1
  all_goals congr 1
  · funext v
    congr 1
    funext x
    split_ifs <;> rfl

end SK.Analytic

end
end

end OAI
