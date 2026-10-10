import OAI.NumberTheory.DirichletL.Moments.PartitionNorm
import OAI.NumberTheory.DirichletL.Moments.Forcing

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondLedger
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentPartition CenteredMomentProductCRT ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem nonzero_unequal_min_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (hcd : c ≠ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) : 6 ∣ min c d := by
  by_contra h6
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hc
      (show 1 ≤ d-c by omega) (by simpa only [min_eq_left hlt.le] using h6) (-k)
    have he : c+(d-c)=d := Nat.add_sub_of_le hlt.le
    have hn := norm_ne_zero_iff.mpr hne
    rw [actualCorrelation_norm_swap] at hn
    have hz' : actualCorrelation (p^d) (p^c) (supported_power p hp d) (supported_power p hp c)
        (-(p^min c d*k)) = 0 := by
      simpa only [← pow_add,he,min_eq_left hlt.le,mul_neg] using hz
    exact hn (by rw [hz',norm_zero])
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hd
      (show 1 ≤ c-d by omega) (by simpa only [min_eq_right hgt.le] using h6) k
    have he : d+(c-d)=c := Nat.add_sub_of_le hgt.le
    exact hne (by simpa only [← pow_add,he,min_eq_right hgt.le] using hz)

def localSaving (c d : ℕ) (nonunit : Prop) : ℝ :=
  (c+d : ℝ) - 5*(min c d : ℝ)/6 - 1 +
    (if c=d ∧ ¬6∣c ∧ ¬nonunit then 1 else 0) +
    (if c=d ∧ ¬6∣c ∧ nonunit then 1/6 else 0) +
    (if c=d ∧ c=1 ∧ nonunit then 1/3 else 0)

theorem localSaving_lower (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (huneq : c ≠ d → 6 ∣ min c d) (nonunit : Prop) :
    ((c:ℝ)+d)/3 ≤ localSaving c d nonunit := by
  by_cases hcd : c=d
  · subst d
    by_cases h6 : 6∣c
    · have hc6 : 6 ≤ c := Nat.le_of_dvd (by omega) h6
      have hn1 : c ≠ 1 := by omega
      simp only [localSaving,min_self,h6,not_true_eq_false,false_and,and_false,
        ite_false,hn1,add_zero]
      have hcr : (6:ℝ) ≤ c := by exact_mod_cast hc6
      linarith
    · by_cases hu : nonunit
      · by_cases hc1 : c=1
        · subst c
          norm_num [localSaving,hu]
        · have hc2 : 2 ≤ c := by omega
          simp only [localSaving,min_self,h6,not_false_eq_true,hu,not_true_eq_false,
            and_self,and_false,false_and,ite_false,ite_true,hc1,add_zero]
          have hcr : (2:ℝ) ≤ c := by exact_mod_cast hc2
          linarith
      · simp only [localSaving,min_self,h6,not_false_eq_true,hu,and_false,
          and_true,ite_false,ite_true,add_zero]
        have hcr : (1:ℝ) ≤ c := by exact_mod_cast hc
        linarith
  · have hmin : 6 ≤ min c d := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (le_min hc hd)) (huneq hcd)
    have hmr : (6:ℝ) ≤ min c d := by exact_mod_cast hmin
    have hmc : ((min c d : ℕ) : ℝ) ≤ c := by exact_mod_cast min_le_left c d
    have hmd : ((min c d : ℕ) : ℝ) ≤ d := by exact_mod_cast min_le_right c d
    simp only [Nat.cast_min] at hmr hmc hmd
    simp only [localSaving,hcd,false_and,ite_false,add_zero]
    linarith

theorem actual_localSaving_lower (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) :
    ((c:ℝ)+d)/3 ≤ localSaving c d (p ∣ k) :=
  localSaving_lower c d hc hd (fun hcd => nonzero_unequal_min_six p hp hg hchar c d hc hd hcd k hne) _

section Global
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem local_nonzero_of_global (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ) (w : O)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) (i : ι) :
    actualCorrelation (p i^c i) (p i^d i) (supported_power (p i) (hp i) (c i))
      (supported_power (p i) (hp i) (d i))
      (p i^min (c i) (d i)*dividedFrequency p c d w i) ≠ 0 := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^d i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i*p i^d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add,← pow_add]
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hn := norm_ne_zero_iff.mpr hne
  rw [actualCorrelation_product_norm (fun i => p i^c i) (fun i => p i^d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab] at hn
  have hi := (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
  rw [commonFrequency_factor p c d w i] at hi
  exact norm_ne_zero_iff.mp hi

omit [DecidableEq ι] in
theorem log_norm_power_product (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c : ι → ℕ) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) =
      ∑ i, (c i : ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]
  rw [Real.logb_prod _ _ (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)))]
  simp only [Real.logb_pow]

def secondSaving (p : ι → O) (c d : ι → ℕ) (w : O) (Z : ℝ) : ℝ :=
  ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) *
    localSaving (c i) (d i) (p i ∣ dividedFrequency p c d w i)

def actualUnitSet (p : ι → O) (c d : ι → ℕ) (w : O) : Finset ι :=
  Finset.univ.filter (fun i => c i=d i ∧ ¬6∣c i ∧ ¬p i∣dividedFrequency p c d w i)

def actualNonunitSet (p : ι → O) (c d : ι → ℕ) (w : O) : Finset ι :=
  Finset.univ.filter (fun i => c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i)

omit [Fintype ι] [DecidableEq ι] in
theorem log_norm_radical (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (S : Finset ι) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) =
      ∑ i ∈ S, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,Nat.cast_prod]
  exact Real.logb_prod _ _ (fun i _ => Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))

theorem secondSaving_eq_norm_ledger (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ) (w : O) (Z : ℝ) :
    secondSaving p c d w Z =
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) +
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ) -
      5*Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.commonIdeal p c d) : ℝ)/6 -
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) +
      Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.unitIdeal p (actualUnitSet p c d w)) : ℝ) +
      Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.unitIdeal p (actualNonunitSet p c d w)) : ℝ)/6 +
      Real.logb Z (Ideal.absNorm (CenteredMomentForcing.forcingIdeal
        (fun i => Ideal.span {p i}) c d (actualNonunitSet p c d w)) : ℝ)/3 := by
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d]
  simp only [CenteredMomentPartitionNorm.commonIdeal,CenteredMomentPartitionNorm.unitIdeal,
    CenteredMomentForcing.forcingIdeal]
  rw [log_norm_power_product p hp,log_norm_radical p hp,log_norm_radical p hp,
    log_norm_radical p hp,log_norm_radical p hp]
  simp only [actualUnitSet,actualNonunitSet,CenteredMomentForcing.forcingSet,
    Finset.filter_filter,Finset.sum_filter,]
  unfold secondSaving
  have hf (i : ι) :
      (if (c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i) ∧ c i=1 ∧ d i=1
       then Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 0) =
      (if c i=d i ∧ c i=1 ∧ p i∣dividedFrequency p c d w i
       then Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 0) := by
    have he : ((c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i) ∧ c i=1 ∧ d i=1) ↔
        (c i=d i ∧ c i=1 ∧ p i∣dividedFrequency p c d w i) := by
      constructor
      · rintro ⟨⟨hcd,h6,hn⟩,hc,hd⟩
        exact ⟨hcd,hc,hn⟩
      · rintro ⟨hcd,hc,hn⟩
        exact ⟨⟨hcd,by omega,hn⟩,hc,by omega⟩
    simp only [he]
  simp_rw [hf]
  rw [show (∑ i, (c i:ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)) +
      (∑ i, (d i:ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∑ i, ((c i:ℝ)+(d i:ℝ))*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) by
      simp only [add_mul,Finset.sum_add_distrib]]
  simp only [Finset.mul_sum,Finset.sum_div]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [localSaving,Nat.cast_min]
  split_ifs <;> ring

theorem actual_secondSaving_lower (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i})) (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (w : O) (Z : ℝ) (hZ : 1 < Z)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) :
    (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) +
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/3 ≤ secondSaving p c d w Z := by
  calc
    _ = ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)*(((c i:ℝ)+d i)/3) := by
      rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
        ← Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
        (actual_localSaving_lower (p i) (hp i) (hg i) (hchar i) (c i) (d i) (hc i) (hd i)
          (dividedFrequency p c d w i) (local_nonzero_of_global p hp hcop c d w hne i))
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

end Global

end SevenEighths.CenteredMomentSecondLedger

end

end OAI
