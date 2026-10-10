import OAI.Combinatorics.ContingencyTables.Counting.CompanionMinMass
import OAI.Combinatorics.ContingencyTables.Counting.CompanionConcentration
import OAI.Combinatorics.ContingencyTables.Transport.TraceBounds

namespace OAI

/-! # Trace restart bounds for the literal companion weights

The actual factorial lifts supply the trace inverse gap, and exact
binomial cancellation supplies its minimum mass. The restart stage
therefore has a two-warm endpoint from every initial subprobability law.
-/

namespace ContingencyTables.CompanionTrace

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing TwoLiftStates
open CompanionConcentration BinaryContraction DegreeCompletion TraceBounds ObservableBounds

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma restart_exponential (M : ℕ) :
    Real.exp (-2*((M:ℝ)+5))/(1/2:ℝ)^M ≤ 1 := by
  have h2 : (2:ℝ) ≤ Real.exp 2 := by
    linarith [Real.add_one_le_exp (2:ℝ)]
  have he : Real.exp (-2:ℝ) ≤ 1/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) h2
  have hp := pow_le_pow_left₀ (Real.exp_nonneg (-2)) he M
  have h10 : Real.exp (-10:ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hid : Real.exp (-2*((M:ℝ)+5))=Real.exp (-2:ℝ)^M*Real.exp (-10:ℝ) := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  rw [hid,div_le_one (by positivity : (0:ℝ) < (1/2:ℝ)^M)]
  exact (mul_le_of_le_one_right (pow_nonneg (Real.exp_nonneg _) _) h10).trans hp

def integerConstant (A : Instance I J) : ℕ :=
  let p := Fintype.card (Labels A)
  10*p^4*(9*(p*(1+8*p*A.W^4))+2*(8+32*p*A.W^6))

lemma integerConstant_cast (A : Instance I J) :
    (integerConstant A:ℝ)=observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
  unfold integerConstant observableConstant
  push_cast
  ring

def time (A : Instance I J) (H K : ℕ) : ℕ :=
  2*integerConstant A*(H+Fintype.card (Labels A)+K+5)

noncomputable def trace (A : Instance I J) (j : ℕ) (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0 < w p r) : FiniteChain (PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :=
  metropolisTrace pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover w
    (completeDegree (weight A j) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length)
    hw (completeDegree_positive _ _ (actual_degree A j).1)

lemma trace_pi (A : Instance I J) (j : ℕ) (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0 < w p r) (S : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    (trace A j hp w hw).π S=CompanionWarmStart.law A j S.val.val := by
  exact completed_trace_pi pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover w
    (weight A j) hw (actual_degree A j).1 S

private lemma actual_dual_degree (A : Instance I J) (j : ℕ) :
    DegreePositive (g A ((j:ℝ)/scale A)) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length ∧
      AdditionProperty (g A ((j:ℝ)/scale A)) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length := by
  have hg := second_properties A ((j:ℝ)/scale A)
    (div_nonneg (Nat.cast_nonneg j) (scale_positive A).le)
  simpa only [PairedLabels.length] using hg

private lemma actual_plain_agreement (A : Instance I J) (j : ℕ)
    (S : Set (Labels A×Bool)) (hS : PlainState pairs S) :
    weight A j S=g A ((j:ℝ)/scale A) S := by
  exact (plain_lifts_agree (labelCell A) (h A ((j:ℝ)/scale A)) S hS).symm

private lemma actual_lift_comparison (A : Instance I J) (j : ℕ)
    (S : Set (Labels A×Bool)) (hS : ChainState pairs S) :
    weight A j S≤(A.W:ℝ)^2*g A ((j:ℝ)/scale A) S := by
  apply firstLift_le_square_secondLift (labelCell A) (h A ((j:ℝ)/scale A)) S hS A.W
    (by have hW := A.hW; omega)
  · intro s
    rw [label_width]
    exact A.hsmall _ _ s.property
  · exact (h_positive A _ _).le

private lemma omission_instance {X : Type*} [Fintype X]
    (d e : DecidableEq X) (f : Set X → ℝ) (k : ℕ)
    (h : @OmissionProperty X _ d f k) : @OmissionProperty X _ e f k := by
  cases Subsingleton.elim d e
  exact h

private lemma addition_instance {X : Type*} [Fintype X]
    (d e : DecidableEq X) (f : Set X → ℝ) (k : ℕ)
    (h : @AdditionProperty X _ d f k) : @AdditionProperty X _ e f k := by
  cases Subsingleton.elim d e
  exact h

private lemma trace_poincare_raw (A : Instance I J) (j : ℕ) (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : GoodMultipliers pairs (weight A j) w)
    (H : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) → ℝ) :
    (trace A j hp w hw.positive).variance H ≤
      (2*(Fintype.card (Labels A):ℝ)^2*((Fintype.card (Labels A):ℝ)*
        (1+8*(Fintype.card (Labels A):ℝ)*((A.W:ℝ)^2)^2)))*
        (trace A j hp w hw.positive).energy H := by
  let d : DecidableEq (Labels A×Bool) := inferInstance
  have hsigf := omission_instance (inferInstance : DecidableEq (Labels A×Bool)) d
    (weight A j) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length (actual_degree A j).2
  have hsigg := addition_instance (inferInstance : DecidableEq (Labels A×Bool)) d
    (g A ((j:ℝ)/scale A)) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length
    (actual_dual_degree A j).2
  have hh := @omission_trace_poincare (Labels A×Bool) inferInstance d
    pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover w (weight A j) (g A ((j:ℝ)/scale A)) hw.positive
    (actual_degree A j).1 (actual_dual_degree A j).1
    hsigf hsigg
    ((A.W:ℝ)^2) (sq_nonneg _) hw.lower
    (actual_plain_agreement A j) (actual_lift_comparison A j) H
  change (trace A j hp w hw.positive).variance H ≤
    (2*((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)^2)*
      (((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)*
        (1+8*((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)*((A.W:ℝ)^2)^2))*
      (trace A j hp w hw.positive).energy H at hh
  have hcoef : (2*((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)^2)*
      (((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)*
        (1+8*((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)*((A.W:ℝ)^2)^2))=
      2*(Fintype.card (Labels A):ℝ)^2*((Fintype.card (Labels A):ℝ)*
        (1+8*(Fintype.card (Labels A):ℝ)*((A.W:ℝ)^2)^2)) := by
    rw [PairedLabels.length]
  exact hh.trans_eq (congrArg (fun k : ℝ => k*(trace A j hp w hw.positive).energy H) hcoef)

theorem trace_poincare (A : Instance I J) (j : ℕ) (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : GoodMultipliers pairs (weight A j) w)
    (H : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) → ℝ) :
    (trace A j hp w hw.positive).variance H ≤
      observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)*
        (trace A j hp w hw.positive).energy H := by
  have hpR : (1:ℝ) ≤ Fintype.card (Labels A) := by exact_mod_cast hp
  have hcoef := trace_constant_le_observable (Fintype.card (Labels A)) ((A.W:ℝ)^2)
    hpR (square_width_one_le A)
  exact (trace_poincare_raw A j hp w hw H).trans
    (mul_le_mul_of_nonneg_right hcoef ((trace A j hp w hw.positive).energy_nonneg H))

noncomputable def minimumMass (A : Instance I J) (H K : ℕ) : ℝ :=
  (1/2:ℝ)^(H+Fintype.card (Labels A)+K)

lemma minimumMass_positive (A : Instance I J) (H K : ℕ) : 0 < minimumMass A H K := by
  unfold minimumMass
  positivity

/-- The manuscript's literal integer restart schedule gives pointwise
relative error at most one with the proved minimum mass. -/
theorem schedule_error (A : Instance I J) (H K : ℕ)
    (hp : 0 < Fintype.card (Labels A)) :
    Real.exp (-(time A H K:ℝ)/observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))/
      minimumMass A H K ≤ 1 := by
  have hpR : (0:ℝ) < Fintype.card (Labels A) := by exact_mod_cast hp
  have hp1 : (1:ℝ) ≤ Fintype.card (Labels A) := by exact_mod_cast hp
  have hbound := observableConstant_lower (Fintype.card (Labels A)) ((A.W:ℝ)^2)
    hp1 (square_width_one_le A)
  have hconst : 0 < observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) :=
    lt_of_lt_of_le (by positivity) hbound
  have hexp : -(time A H K:ℝ)/observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)=
      -2*((H+Fintype.card (Labels A)+K:ℕ)+5:ℝ) := by
    unfold time
    push_cast
    rw [integerConstant_cast]
    field_simp [hconst.ne']
  rw [hexp]
  exact restart_exponential (H+Fintype.card (Labels A)+K)

lemma trace_minimum (A : Instance I J) (H K j : ℕ) (hj : j ≤ H)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^K)
    (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0 < w p r) (S : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    minimumMass A H K ≤ (trace A j hp w hw).π S := by
  rw [trace_pi]
  apply le_trans _ (CompanionMinMass.law_lower A K j hB S.val.val S.property)
  exact pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) (by omega)

/-- The pointwise error estimate has no new signature or minimum-mass
assumption: both are supplied by the actual count/lift application. -/
theorem trace_point_mixing (A : Instance I J) (H K j : ℕ) (hj : j ≤ H)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^K)
    (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : GoodMultipliers pairs (weight A j) w) (t : ℕ)
    (x y : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    |((trace A j hp w hw.positive).kernel.power t).P x y/
        CompanionWarmStart.law A j y.val.val-1| ≤
      Real.exp (-(t:ℝ)/observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))/minimumMass A H K := by
  let T := trace A j hp w hw.positive
  have hpR : (1:ℝ) ≤ Fintype.card (Labels A) := by exact_mod_cast hp
  have hK : 1 ≤ observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
    have hh := observableConstant_lower (Fintype.card (Labels A)) ((A.W:ℝ)^2)
      hpR (square_width_one_le A)
    have hp5 : (1:ℝ) ≤ (Fintype.card (Labels A):ℝ)^5 := one_le_pow₀ hpR
    nlinarith
  have hh := T.kernel_point_mixing _ _ hK (minimumMass_positive A H K)
    (trace_minimum A H K j hj hB hp w hw.positive) (trace_poincare A j hp w hw) t x y
  rwa [trace_pi] at hh

/-- A stage with pointwise relative error at most one ends two-warm,
even when its incoming law is merely a subprobability law. -/
theorem stage_warm (A : Instance I J) (H K j : ℕ) (hj : j ≤ H)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^K)
    (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : GoodMultipliers pairs (weight A j) w) (t : ℕ)
    (ht : Real.exp (-(t:ℝ)/observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))/minimumMass A H K ≤ 1)
    (nu : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) → ℝ)
    (hnu : ∀ S,0 ≤ nu S) (hmass : ∑ S,nu S ≤ 1)
    (y : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    ((trace A j hp w hw.positive).kernel.power t).push nu y ≤ 2*CompanionWarmStart.law A j y.val.val := by
  have hy : 0 < CompanionWarmStart.law A j y.val.val :=
    div_pos (weight_positive A j _) (CompanionWarmStart.total_positive A j)
  have hrow (x : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
      ((trace A j hp w hw.positive).kernel.power t).P x y ≤
        2*CompanionWarmStart.law A j y.val.val := by
    have hh := (le_abs_self _).trans ((trace_point_mixing A H K j hj hB hp w hw t x y).trans ht)
    apply (div_le_iff₀ hy).mp
    linarith
  calc
    _ ≤ ∑ x,nu x*(2*CompanionWarmStart.law A j y.val.val) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hrow x) (hnu x))
    _ = (∑ x,nu x)*(2*CompanionWarmStart.law A j y.val.val) := by rw [Finset.sum_mul]
    _ ≤ _ := by nlinarith

end ContingencyTables.CompanionTrace

end OAI
