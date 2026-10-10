import OAI.Algebra.OddKaplansky.SourceGluing

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section
namespace OddKaplansky.BooleanPolynomial
noncomputable section
open scoped Classical BigOperators
open MvPolynomial
variable {σ : Type portUniverse1} {K : Type portUniverse2} [sectionInstance4 : Fintype σ] [sectionInstance5 : DecidableEq σ] [CommRing K]

def value (S : Finset σ) (i : σ) : K := if i ∈ S then 1 else 0

def coefficient (f : MvPolynomial σ K) (T : Finset σ) : K :=
  ∑ d ∈ f.support, if d.support = T then f.coeff d else 0

lemma support_card_le
    {σ : Type contextUniverse1}
    {K : Type contextUniverse2}
    [Fintype.{contextUniverse1} σ]
    [DecidableEq.{contextUniverse1 + 1} σ]
    [CommRing.{contextUniverse2} K] {f : MvPolynomial σ K} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    d.support.card ≤ f.totalDegree := by
  apply le_trans _ (le_totalDegree hd)
  change d.support.card ≤ ∑ i ∈ d.support, d i
  calc
    d.support.card = ∑ _i ∈ d.support, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

lemma bool_power_product
    {σ : Type contextUniverse1}
    {K : Type contextUniverse2}
    [Fintype.{contextUniverse1} σ]
    [DecidableEq.{contextUniverse1 + 1} σ]
    [CommRing.{contextUniverse2} K] (S : Finset σ) (d : σ →₀ ℕ) :
    d.prod (fun i e => value (K := K) S i ^ e) = if d.support ⊆ S then 1 else 0 := by
  change (∏ i ∈ d.support, value S i ^ d i) = _
  by_cases hs : d.support ⊆ S
  · rw [ite_eq_left hs]
    exact Finset.prod_eq_one (fun i hi => by simp [value, hs hi])
  · rw [ite_eq_right hs]
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hs
    apply Finset.prod_eq_zero hi
    simp [value, hni, Finsupp.mem_support_iff.mp hi]

lemma evaluate (f : MvPolynomial σ K) (S : Finset σ) (n : ℕ) [Fintype {T : Finset σ // T.card ≤ n}] (hf : f.totalDegree ≤ n) :
    eval (value S) f = ∑ T : {T : Finset σ // T.card ≤ n},
      (if T.val ⊆ S then (1 : K) else 0) * coefficient f T.val := by
  rw [eval_eq]
  change (∑ d ∈ f.support, f.coeff d * d.prod (fun i e => value S i ^ e)) = _
  simp_rw [bool_power_product, coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdc : d.support.card ≤ n := (support_card_le hd).trans hf
  let T : {T : Finset σ // T.card ≤ n} := ⟨d.support, hdc⟩
  rw [Finset.sum_eq_single T]
  · simp [T, mul_comm]
  · intro U _ hUT
    have hne : d.support ≠ U.val := by
      intro h
      apply hUT
      exact Subtype.ext h.symm
    simp [hne]
  · simp

end
end OddKaplansky.BooleanPolynomial

namespace OddKaplansky.GraphPolynomial
noncomputable section
open scoped Classical BigOperators
open MvPolynomial
variable {σ : Type portUniverse3} {K : Type portUniverse4} [sectionInstance6 : Fintype σ] [sectionInstance7 : DecidableEq σ] [Field K]

def factor (S : Finset σ) (r k : ℕ) : MvPolynomial σ K :=
  C ((r - k : ℕ) : K)⁻¹ * ((∑ i ∈ S, X i) + C (-(k : K)))

def polynomial (S : Finset σ) (r lo hi : ℕ) : MvPolynomial σ K :=
  ∏ k ∈ Finset.Ico lo hi, factor S r k

lemma degree_factor
    {σ : Type contextUniverse1}
    {K : Type contextUniverse2}
    [Fintype.{contextUniverse1} σ]
    [DecidableEq.{contextUniverse1 + 1} σ]
    [Field.{contextUniverse2} K] (S : Finset σ) (r k : ℕ) : (factor (K := K) S r k).totalDegree ≤ 1 := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact totalDegree_finsetSum_le (fun i _ => (totalDegree_X i).le)
  · rw [totalDegree_C]
    omega

lemma degree_polynomial (S : Finset σ) (r lo hi : ℕ) :
    (polynomial (K := K) S r lo hi).totalDegree ≤ hi - lo := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.Ico lo hi, (1 : ℕ) := Finset.sum_le_sum (fun k _ => degree_factor S r k)
    _ = _ := by simp

lemma eval_variables
    {σ : Type contextUniverse1}
    {K : Type contextUniverse2}
    [Fintype.{contextUniverse1} σ]
    [DecidableEq.{contextUniverse1 + 1} σ]
    [Field.{contextUniverse2} K] (S T : Finset σ) :
    eval (BooleanPolynomial.value (K := K) T) (∑ i ∈ S, X i) = ((S ∩ T).card : K) := by
  simp only [eval_sum, eval_X, BooleanPolynomial.value]
  rw [Finset.sum_boole]
  congr 1

lemma eval_polynomial (S T : Finset σ) (r lo hi : ℕ) :
    eval (BooleanPolynomial.value (K := K) T) (polynomial S r lo hi) =
      ∏ k ∈ Finset.Ico lo hi, (((S ∩ T).card : K) - (k : K)) / ((r-k : ℕ) : K) := by
  simp only [polynomial, map_prod, factor, eval_mul, eval_add, eval_C, eval_variables,
    sub_eq_add_neg, div_eq_mul_inv, mul_comm]

lemma diagonal (S : Finset σ) (r lo hi : ℕ) (hS : S.card = r) (hhi : hi ≤ r)
    (hden : ∀ k ∈ Finset.Ico lo hi, ((r-k : ℕ) : K) ≠ 0) :
    eval (BooleanPolynomial.value (K := K) S) (polynomial S r lo hi) = 1 := by
  rw [eval_polynomial]
  apply Finset.prod_eq_one
  intro k hk
  have hk' : k ≤ r := Nat.le_of_lt ((Finset.mem_Ico.mp hk).2.trans_le hhi)
  simp only [Finset.inter_self, hS, ← Nat.cast_sub hk']
  exact div_self (hden k hk)

lemma vanishes (S T : Finset σ) (r lo hi : ℕ)
    (ha : lo ≤ (S ∩ T).card) (hb : (S ∩ T).card < hi) :
    eval (BooleanPolynomial.value (K := K) T) (polynomial S r lo hi) = 0 := by
  rw [eval_polynomial]
  apply Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨ha,hb⟩)
  simp

end
end OddKaplansky.GraphPolynomial

end

end OAI
