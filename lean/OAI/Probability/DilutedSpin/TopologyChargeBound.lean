import OAI.Probability.DilutedSpin.ScheduledRelativeCharge

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- Exact leaf budget, counting vertices with multiplicity and not merely
branching depth values. Unary grid levels consume no budget. -/
lemma branch_budget {n : ℕ} (S : PrescribedTree n) :
    branchingCount S (fun _ => True)+branchExcess S+1=leaves S := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    have hs : (∑ i, branchingCount (C i) (fun _ => True))+
        (∑ i, branchExcess (C i))+(k:ℕ)=∑ i, leaves (C i) := by
      calc
        _ = ∑ i, (branchingCount (C i) (fun _ => True)+branchExcess (C i)+1) := by
          simp [Finset.sum_add_distrib]
        _ = _ := Finset.sum_congr rfl (fun i _ => ih i)
    simp only [branchingCount,branchExcess,leaves,true_and]
    have hp : 0 < (k:ℕ) := k.property
    split <;> omega

lemma branchingDepths_card_le {n : ℕ} (S : PrescribedTree n) :
    (branchingDepths S).card≤branchingCount S (fun _ => True) := by
  classical
  rw [branchingCount_eq_vertexSum]
  simp only [and_true]
  calc
    _ ≤ (Finset.univ.filter (fun v : S.Internal => 1<vertexArity S v)).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_eq_sum_ones,Finset.sum_filter]

lemma shiftedPrefixDepths_card_le {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    (shiftedPrefixDepths S d).card≤leaves S := by
  calc
    _ ≤ (shiftedTwinDepths S).card := Finset.card_image_le
    _ ≤ (branchingDepths S).card := Finset.card_image_le
    _ ≤ branchingCount S (fun _ => True) := branchingDepths_card_le S
    _ ≤ leaves S := by have h := branch_budget S; omega

lemma chargeBound_le_pow {C D : ℝ} (hC : 0≤C) (hD : 0≤D) (k b : ℕ) :
    chargeBound C D k b≤(C+D)^k := by
  induction k generalizing b with
  | zero => simp only [chargeBound,pow_zero]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero =>
      simp only [chargeBound,pow_succ]
      calc
        _ ≤ C*(C+D)^k := mul_le_mul_of_nonneg_left (ih 0) hC
        _ ≤ _ := by nlinarith [pow_nonneg (add_nonneg hC hD) k]
    | succ b =>
      simp only [chargeBound,pow_succ]
      calc
        _ ≤ C*(C+D)^k+D*(C+D)^k := add_le_add
          (mul_le_mul_of_nonneg_left (ih _) hC) (mul_le_mul_of_nonneg_left (ih _) hD)
        _ = _ := by ring

/-- A topology-only constant for the genuine relative signed-history cost.
The grid size is absent. Its hypotheses are just leaf/depth counts, not a
covariance estimate or any desired limiting conclusion. -/
theorem shiftedCharge_relative_uniform {L : ℕ} (hL : 0<L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (k R : ℕ) (hQ : Q.card≤R)
    (hS : leaves S+k≤R) (hT : leaves T≤R)
    (a b : T.Leaf) (hab : a≠b) (η : ℝ) (hη : 0<η)
    (hr : BranchRegular T (grid L 0 L) η)
    (hb : branchingCount T (fun _ => True)=branchingCount T (· ∈ Q)+1) :
    shiftedCharge Q T S k /
      |partialKappa T (grid L 0 L) Finset.univ/partialKappa T (grid L 0 L) {b,a}| ≤
      (((2+(R:ℝ))*(R:ℝ))^k)/(min η 1)^R := by
  classical
  have hA := chargeBound_nonneg (C := 2*(leaves S+k:ℕ))
    (D := (Q.card:ℝ)*(leaves S+k:ℕ)) (by positivity) (by positivity) k
    (branchingCount T (· ∈ Q))
  have hp := chargeBound_le_pow (C := 2*(leaves S+k:ℕ))
    (D := (Q.card:ℝ)*(leaves S+k:ℕ)) (by positivity) (by positivity) k
    (branchingCount T (· ∈ Q))
  have hv : (2*(leaves S+k:ℕ)+(Q.card:ℝ)*(leaves S+k:ℕ))≤(2+(R:ℝ))*(R:ℝ) := by
    have hSr : ((leaves S+k:ℕ):ℝ)≤R := by exact_mod_cast hS
    have hQr : (Q.card:ℝ)≤R := by exact_mod_cast hQ
    nlinarith [mul_nonneg (sub_nonneg.mpr hSr) (by positivity : 0≤(R:ℝ)),
      mul_nonneg (sub_nonneg.mpr hQr) (show 0≤((leaves S+k:ℕ):ℝ) by positivity)]
  have hex : branchExcess T≤R := by have hh := branch_budget T; omega
  have hm : 0 < min η 1 := lt_min hη zero_lt_one
  have he : (min η 1)^R≤η^(branchExcess T) :=
    (pow_le_pow_of_le_one hm.le (min_le_right _ _) hex).trans
      (pow_le_pow_left₀ hm.le (min_le_left _ _) _)
  exact (shiftedCharge_relative_bound hL Q T S k a b hab η hη hr hb).trans
    (div_le_div₀ (by positivity) (hp.trans (pow_le_pow_left₀ (by positivity) hv _))
      (pow_pos hm _) he)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
