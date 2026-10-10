import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.PiExponent.Approximation.WeightSeparationProducts

namespace OAI

namespace PiExponentApprox

noncomputable section

def geometricDegreeWeight (w0 : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then w0 else x i

def geometricJetWeight (v0 theta : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then v0 else x i / theta

def weightSeparationFactor (m : ℕ) (C w0 v0 theta : ℝ) : ℝ :=
  C * (max 1 (max v0 (1 / theta) / min w0 1)) ^ (m + 1)

theorem weightSeparationFactor_pos
    (m : ℕ) (C w0 v0 theta : ℝ) (hC : 0 < C) :
    0 < weightSeparationFactor m C w0 v0 theta := by
  unfold weightSeparationFactor
  have hbase : 0 < max 1 (max v0 (1 / theta) / min w0 1) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos hC (pow_pos hbase _)

theorem geometric_weight_products_of_normalized
    (m : ℕ) (C w0 v0 theta : ℝ) (x : ℕ → ℝ)
    (hC : 0 < C) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (A B : Finset ℕ) (hcard : A.card = B.card) (hbound : B.card ≤ m + 1)
    (hsep : weightSeparationFactor m C w0 v0 theta * (∏ i ∈ B, x i) <
      ∏ i ∈ A, x i) :
    C * (∏ i ∈ B, geometricJetWeight v0 theta x i) <
      ∏ i ∈ A, geometricDegreeWeight w0 x i := by
  let L : ℝ := min w0 1
  let R : ℝ := max v0 (1 / theta)
  let T : ℝ := max 1 (R / L)
  have hL : 0 < L := lt_min hw0 zero_lt_one
  have hR : 0 < R := lt_of_lt_of_le hv0 (le_max_left _ _)
  have hT : 1 ≤ T := le_max_left _ _
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le zero_lt_one (hx i)
  have hdeg (i : ℕ) : L * x i ≤ geometricDegreeWeight w0 x i := by
    by_cases hi : i = 0
    · subst i
      simp only [geometricDegreeWeight, hx0, mul_one]
      exact min_le_left _ _
    · simp only [geometricDegreeWeight, ite_eq_right hi]
      exact mul_le_of_le_one_left (le_of_lt (hxpos i)) (min_le_right _ _)
  have hjet (i : ℕ) : geometricJetWeight v0 theta x i ≤ R * x i := by
    by_cases hi : i = 0
    · subst i
      simp only [geometricJetWeight, hx0, mul_one]
      exact le_max_left _ _
    · simp only [geometricJetWeight, ite_eq_right hi]
      calc
        x i / theta = (1 / theta) * x i := by ring
        _ ≤ R * x i := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (le_of_lt (hxpos i))
  have hdegprod : L ^ A.card * (∏ i ∈ A, x i) ≤
      ∏ i ∈ A, geometricDegreeWeight w0 x i := by
    calc
      _ = ∏ i ∈ A, (L * x i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => mul_nonneg (le_of_lt hL)
        (le_of_lt (hxpos i))) (fun i _ => hdeg i)
  have hjetnonneg (i : ℕ) : 0 ≤ geometricJetWeight v0 theta x i := by
    unfold geometricJetWeight
    split
    · exact le_of_lt hv0
    · exact div_nonneg (le_of_lt (hxpos i)) (le_of_lt htheta)
  have hjetprod : (∏ i ∈ B, geometricJetWeight v0 theta x i) ≤
      R ^ B.card * (∏ i ∈ B, x i) := by
    calc
      _ ≤ ∏ i ∈ B, (R * x i) := Finset.prod_le_prod₀
        (fun i _ => hjetnonneg i) (fun i _ => hjet i)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hRle : R ≤ T * L := (div_le_iff₀ hL).mp (le_max_right _ _)
  have hpowers : R ^ B.card ≤ T ^ (m + 1) * L ^ B.card := by
    calc
      R ^ B.card ≤ (T * L) ^ B.card := pow_le_pow_left₀ (le_of_lt hR) hRle _
      _ = T ^ B.card * L ^ B.card := mul_pow _ _ _
      _ ≤ T ^ (m + 1) * L ^ B.card := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hT hbound) (pow_nonneg (le_of_lt hL) _)
  have hprodB : 0 ≤ ∏ i ∈ B, x i := Finset.prod_nonneg fun i _ => le_of_lt (hxpos i)
  calc
    C * (∏ i ∈ B, geometricJetWeight v0 theta x i) ≤
        C * (R ^ B.card * (∏ i ∈ B, x i)) :=
      mul_le_mul_of_nonneg_left hjetprod (le_of_lt hC)
    _ ≤ C * ((T ^ (m + 1) * L ^ B.card) * (∏ i ∈ B, x i)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpowers hprodB) (le_of_lt hC)
    _ = L ^ A.card * (weightSeparationFactor m C w0 v0 theta *
          (∏ i ∈ B, x i)) := by
      rw [hcard]
      change C * ((T ^ (m + 1) * L ^ B.card) * (∏ i ∈ B, x i)) =
        L ^ B.card * ((C * T ^ (m + 1)) * (∏ i ∈ B, x i))
      ring
    _ < L ^ A.card * (∏ i ∈ A, x i) :=
      mul_lt_mul_of_pos_left hsep (pow_pos hL _)
    _ ≤ _ := hdegprod

def SeparatedWeightGrowth (m : ℕ) (D : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ i, 0 < i → i ≤ m → D * (∏ j ∈ Finset.range i, x j) < x i

theorem geometric_weight_products_separated
    (m : ℕ) (C w0 v0 theta : ℝ) (x : ℕ → ℝ)
    (hC : 0 < C) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (hgrowth : SeparatedWeightGrowth m (weightSeparationFactor m C w0 v0 theta) x)
    (A B : Finset ℕ) (hcard : A.card = B.card)
    (hA : A ⊆ Finset.range (m + 1)) (hB : B ⊆ Finset.range (m + 1))
    (i : ℕ) (hi : 0 < i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    C * (∏ j ∈ B, geometricJetWeight v0 theta x j) <
      ∏ j ∈ A, geometricDegreeWeight w0 x j := by
  have hibound : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp (hA hiA))
  have hcardbound : B.card ≤ m + 1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hB
  apply geometric_weight_products_of_normalized m C w0 v0 theta x
    hC hw0 hv0 htheta hx0 hx A B hcard hcardbound
  exact PiExponent.normalized_products_separated x
    (weightSeparationFactor m C w0 v0 theta) hx
    (weightSeparationFactor_pos m C w0 v0 theta hC)
    A B i hiA hiB hbelow (hgrowth i hi hibound)

end
end PiExponentApprox

end OAI
