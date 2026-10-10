import Mathlib
import OAI.Computability.MinUncut.Search.FiniteAverageBounds
import OAI.Computability.MinUncut.Estimates.ComparisonSoundness

namespace OAI

section
namespace MinUncut.Inner
open scoped BigOperators
open GaussianHermite RowNoise

def rationalSigma (J : ℕ) : ℚ := 1/(2560*(J:ℚ))
def rationalEta (J : ℕ) : ℚ := rationalSigma J^2/(2560*(J:ℚ))
def rationalR (J : ℕ) : ℕ := ⌈(rationalEta J)⁻¹^2⌉₊
def rationalT (J : ℕ) : ℕ := ⌈32*(J:ℚ)/(rationalEta J*rationalSigma J^4)⌉₊

lemma ceil_rat_real (q : ℚ) : ⌈(q:ℝ)⌉₊=⌈q⌉₊ := by
  apply Nat.le_antisymm
  · exact Nat.ceil_le.mpr (by exact_mod_cast Nat.le_ceil q)
  · exact Nat.ceil_le.mpr (by exact_mod_cast Nat.le_ceil (q:ℝ))

@[simp] lemma rationalSigma_cast (J : ℕ) : (rationalSigma J:ℝ)=sourceSigma J := by
  simp [rationalSigma,sourceSigma]
@[simp] lemma rationalEta_cast (J : ℕ) : (rationalEta J:ℝ)=sourceEta J := by
  simp [rationalEta,sourceEta]
@[simp] lemma rationalR_eq (J : ℕ) : rationalR J=sourceR J := by
  simp only [rationalR,sourceR,← rationalEta_cast J,← Rat.cast_inv,← Rat.cast_pow,ceil_rat_real]
@[simp] lemma rationalT_eq (J : ℕ) : rationalT J=sourceT J := by
  rw [rationalT,sourceT,← ceil_rat_real]
  congr 1
  simp

lemma rho_even (σ : ℝ) (t : ℕ) : (smoothingRho σ)^(2*t)=((1+σ^2)⁻¹)^t := by
  rw [pow_mul]
  congr 1
  unfold smoothingRho
  rw [inv_pow,Real.sq_sqrt (by positivity)]

lemma cutoff_tail {r : ℝ} (hr : 0 ≤ r) {s : ℕ}
    (hstep : ((s:ℝ)+3)*r ≤ (s:ℝ)+2) (hbase : ((s:ℝ)+2)*r^(s+2) ≤ 1/16) :
    ∀ t : ℕ, s+2 ≤ t → (t:ℝ)*r^t ≤ 1/16 := by
  have hr1 : r ≤ 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) s]
  intro t ht
  induction t,ht using Nat.le_induction with
  | base => simpa only [Nat.cast_add,Nat.cast_ofNat] using hbase
  | succ t ht ih =>
    have ht' : (s:ℝ)+2 ≤ t := by exact_mod_cast ht
    have hd : ((t:ℝ)+1)*r ≤ t := by nlinarith
    calc
      ((t+1:ℕ):ℝ)*r^(t+1) = (((t:ℝ)+1)*r)*r^t := by push_cast; rw [pow_succ]; ring
      _ ≤ (t:ℝ)*r^t := mul_le_mul_of_nonneg_right hd (pow_nonneg hr _)
      _ ≤ _ := ih

lemma exists_finite_cutoff {σ : ℝ} (hσ : 0 < σ) :
    ∃ s : ℕ, ((s:ℝ)+3)*(1+σ^2)⁻¹ ≤ (s:ℝ)+2 ∧
      ((s:ℝ)+2)*((1+σ^2)⁻¹)^(s+2) ≤ 1/16 := by
  obtain ⟨s,hs⟩ := exists_cutoff (smoothingRho_lt_one hσ.ne') (by norm_num : (0:ℝ) < 1/16)
  obtain ⟨a,ha⟩ := exists_nat_gt ((σ^2)⁻¹)
  refine ⟨max s a,?_,?_⟩
  · have hb : (a:ℝ)*σ^2 > 1 := by
      have := (div_lt_iff₀ (show 0 < σ^2 by positivity)).mp (show 1/σ^2 < a by simpa using ha)
      linarith
    have hc : (a:ℝ) ≤ max s a := by exact_mod_cast le_max_right s a
    apply (mul_inv_le_iff₀ (show 0 < 1+σ^2 by positivity)).mpr
    nlinarith [sq_nonneg σ]
  · have hh := hs (max s a+2) (by omega)
    rw [rho_even] at hh
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

lemma pairClass_card_le (m : ℕ) : Fintype.card (Option (PairClass m)) ≤ m^2+1 := by
  have h := Fintype.card_le_of_injective (fun p : PairClass m => p.val) Subtype.val_injective
  simpa only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin,pow_two] using Nat.add_le_add_right h 1

lemma row_card (m n : ℕ) : Fintype.card (Row m n)=m*n^(m-1) := by
  classical
  simp only [Row,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin]
  have he (i : Fin m) : Fintype.card {j : Fin m // j ≠ i}=m-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
end MinUncut.Inner

end
section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

lemma edgeMean_abs_difference (equations : S → Equation Name) {k : ℕ}
    (hk : k≤Fintype.card I) (F G : EdgeStatistic Name I) {ε : ℝ}
    (h : ∀ U hidden pos, |F U hidden pos-G U hidden pos|≤ε) :
    |edgeMean equations k F-edgeMean equations k G|≤ε := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  apply expect_abs_difference
  intro H
  apply expect_abs_difference
  intro a
  apply expect_abs_difference
  intro pos
  exact h _ _ _

def ProofFamily.finiteErrors {J : ℕ} (P : InnerParameters J) (O : OuterParameters J P)
    (g : GridData) (f : ProofFamily Name I) (equations : S → Equation Name) : Test → ℝ
  | .first => edgeMean equations O.k (fun U h pos => finiteFirst (m := P.m) (n := P.n) g
    (f.second (secondQuestion U h pos)) (rationalSigma J) (rationalEta J))
  | .second => edgeMean equations O.k (fun U h pos => finiteSecond (m := P.m) (n := P.n) g
    (f.second (secondQuestion U h pos)) ((sourceEta J)^2/P.m) (rationalSigma J) (rationalEta J))
  | .third => edgeMean equations O.k (fun U h pos => finiteThird (m := P.m) (n := P.n) g
    (f.second (secondQuestion U h pos)) (rationalSigma J) (rationalEta J))
  | .fourth => edgeMean equations O.k (fun U h pos => finiteFourth (m := P.m) (n := P.n) g
    (projection U h pos) (f.first U) (f.second (secondQuestion U h pos)) (rationalSigma J) (rationalEta J))

def ProofFamily.finiteCost {J : ℕ} (P : InnerParameters J) (O : OuterParameters J P)
    (g : GridData) (f : ProofFamily Name I) (equations : S → Equation Name) : ℝ :=
  ∑ j, f.finiteErrors P O g equations j / budgets P O j

def budgetWeight {J : ℝ} (P : InnerParameters J) (O : OuterParameters J P) : ℝ :=
  ∑ j, (budgets P O j)⁻¹

lemma rational_source_bounds {J : ℕ} (hJ : 1≤J) :
    0≤rationalSigma J ∧ rationalSigma J≤1 ∧ 0≤rationalEta J ∧ rationalEta J≤1 := by
  have hJ' : (1:ℝ)≤J := by exact_mod_cast hJ
  have hs := sourceSigma_pos hJ'
  have hs1 := sourceSigma_le_one hJ'
  have he := sourceEta_pos hJ'
  have he1 := (sourceEta_le_sigma hJ').trans hs1
  rw [← rationalSigma_cast] at hs hs1
  rw [← rationalEta_cast] at he he1
  exact ⟨by exact_mod_cast hs.le,by exact_mod_cast hs1,by exact_mod_cast he.le,by exact_mod_cast he1⟩

attribute [local irreducible] edgeMean
lemma ProofFamily.finiteErrors_difference {J : ℕ} (hJ : 1≤J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hk : O.k≤Fintype.card I) {ε : ℚ} (hε : 0<ε) (j : Test) :
    |f.testErrors P O equations j-
      f.finiteErrors P O (tableGrid P.m P.n ε hε) equations j|≤ε := by
  have hn : 0<P.n := by have := P.hn; omega
  have hm : 0<P.m := by have := P.hm; omega
  have hJ' : (1:ℝ)≤J := by exact_mod_cast hJ
  obtain ⟨hs,hs1,he,he1⟩ := rational_source_bounds hJ
  have ha := source_row_rate hJ' hm
  cases j <;> rw [ProofFamily.testErrors,ProofFamily.finiteErrors] <;>
    apply edgeMean_abs_difference equations hk <;> intro U hidden pos
  · simpa only [rationalSigma_cast,rationalEta_cast] using
      finiteFirst_difference (f.second (secondQuestion U hidden pos)) hn hs hs1 he he1 hε
  · simpa only [rationalSigma_cast,rationalEta_cast] using
      finiteSecond_difference (f.second (secondQuestion U hidden pos)) hn hs hs1 he he1 hε ha.1 ha.2.1
  · simpa only [rationalSigma_cast,rationalEta_cast] using
      finiteThird_difference (f.second (secondQuestion U hidden pos)) hn hs hs1 he he1 hε
  · simpa only [rationalSigma_cast,rationalEta_cast,ProofFamily.fourthTotal] using
      finiteFourth_difference (projection U hidden pos) (f.first U)
        (f.second (secondQuestion U hidden pos)) hn hs hs1 he he1 hε

lemma ProofFamily.finiteCost_difference {J : ℕ} (hJ : 1≤J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hk : O.k≤Fintype.card I) {ε : ℚ} (hε : 0<ε) :
    |f.cost P O equations-f.finiteCost P O (tableGrid P.m P.n ε hε) equations|≤
      (ε:ℝ)*budgetWeight P O := by
  have hJ' : (1:ℝ)≤J := by exact_mod_cast hJ
  unfold ProofFamily.cost ProofFamily.finiteCost
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |f.testErrors P O equations j / budgets P O j-
          f.finiteErrors P O (tableGrid P.m P.n ε hε) equations j / budgets P O j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (ε:ℝ) / budgets P O j := Finset.sum_le_sum (fun j _ => by
      rw [← sub_div,abs_div,abs_of_pos (budgets_pos hJ' P O j)]
      exact div_le_div_of_nonneg_right (f.finiteErrors_difference hJ P O equations hk hε j)
        (budgets_pos hJ' P O j).le)
    _ = _ := by simp only [budgetWeight,Finset.mul_sum,div_eq_mul_inv]
end MinUncut.Outer

end
end

end OAI
