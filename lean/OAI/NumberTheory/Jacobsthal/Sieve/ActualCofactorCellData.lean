import Mathlib
import OAI.NumberTheory.Jacobsthal.Estimates.SmallModelSourceScales

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

noncomputable def selections {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) : Finset (ι → Finset ℕ) :=
  Fintype.piFinset (fun i => (P i).powersetCard (m i))

theorem mem_selections {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (f : ι → Finset ℕ) :
    f ∈ selections P m ↔ ∀ i, f i ⊆ P i ∧ (f i).card = m i := by
  simp only [selections, Fintype.mem_piFinset, Finset.mem_powersetCard]

def selectionProduct {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) : ℕ :=
  ∏ i, ∏ p ∈ f i, p

noncomputable def selectionPrimes {ι : Type*} [Fintype ι]
    (f : ι → Finset ℕ) : Finset ℕ := Finset.univ.biUnion f

theorem selection_disjoint {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) :
    Pairwise (fun i j => Disjoint (f i) (f j)) := by
  intro i j hij
  exact (hd hij).mono (hf i) (hf j)

theorem selectionProduct_eq_union {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) :
    selectionProduct f = ∏ p ∈ selectionPrimes f, p := by
  symm
  exact Finset.prod_biUnion (fun i _ j _ hij => selection_disjoint P hd f hf hij)

theorem recover_bin {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) (i : ι) :
    selectionPrimes f ∩ P i = f i := by
  ext p
  constructor
  · intro hp
    obtain ⟨hu, hpi⟩ := Finset.mem_inter.mp hp
    obtain ⟨j, _hj, hpj⟩ := Finset.mem_biUnion.mp hu
    by_cases hji : j = i
    · simpa only [hji] using hpj
    · exact False.elim ((Finset.disjoint_left.mp (hd hji)) (hf j hpj) hpi)
  · intro hp
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩, hf i hp⟩

theorem selectionProduct_primeFactors {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) :
    (selectionProduct f).primeFactors = selectionPrimes f := by
  rw [selectionProduct_eq_union P hd f hf]
  apply Nat.primeFactors_prod
  intro p hp
  obtain ⟨i, _hi, hpi⟩ := Finset.mem_biUnion.mp hp
  exact hP i p (hf i hpi)

theorem selectionProduct_pos {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) : 0 < selectionProduct f :=
  Finset.prod_pos (fun i _ => Finset.prod_pos (fun p hp => (hP i p (hf i hp)).pos))

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem selectionProduct_injOn {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Set.InjOn selectionProduct (selections P m : Set (ι → Finset ℕ)) := by
  intro f hf g hg he
  have hfs := (mem_selections P m f).mp hf
  have hgs := (mem_selections P m g).mp hg
  have hu : selectionPrimes f = selectionPrimes g := by
    rw [← selectionProduct_primeFactors P hP hd f (fun i => (hfs i).1),
      ← selectionProduct_primeFactors P hP hd g (fun i => (hgs i).1), he]
  funext i
  rw [← recover_bin P hd f (fun j => (hfs j).1) i,
    ← recover_bin P hd g (fun j => (hgs j).1) i, hu]

noncomputable def cofactorChoices {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) : Finset ℕ :=
  (selections P m).image selectionProduct

theorem selections_card {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) :
    (selections P m).card = ∏ i, (P i).card.choose (m i) := by
  simp only [selections, Fintype.card_piFinset, Finset.card_powersetCard]

theorem cofactorChoices_card {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    (cofactorChoices P m).card = ∏ i, (P i).card.choose (m i) := by
  rw [cofactorChoices, Finset.card_image_of_injOn (selectionProduct_injOn P m hP hd)]
  exact selections_card P m

theorem cofactorChoices_nonempty {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hm : ∀ i, m i ≤ (P i).card) : (cofactorChoices P m).Nonempty := by
  apply Finset.card_pos.mp
  rw [cofactorChoices_card P m hP hd]
  exact Finset.prod_pos (fun i _ => Nat.choose_pos (hm i))

theorem cofactor_positive {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p) (q : ℕ)
    (hq : q ∈ cofactorChoices P m) : 0 < q := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  exact selectionProduct_pos P hP f (fun i => ((mem_selections P m f).mp hf i).1)

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices

theorem half_power_le_choose (n m : ℕ) (hm : 2*m ≤ n) :
    ((n : ℝ)/2)^m/(m.factorial : ℝ) ≤ (n.choose m : ℝ) := by
  have hsub : m ≤ n+1 := by omega
  have hhalf : (n : ℝ)/2 ≤ ((n+1-m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
    have hh : 2*(m : ℝ) ≤ n := by exact_mod_cast hm
    linarith
  calc
    _ ≤ (((n+1-m : ℕ) : ℝ)^m)/(m.factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf m) (Nat.cast_nonneg _)
    _ ≤ (n.choose m : ℝ) := by
      simpa only [Nat.cast_pow] using (Nat.pow_le_choose (α := ℝ) m n)

theorem factorial_le_uniform_power (m K : ℕ) (hm : m ≤ K) :
    (m.factorial : ℝ) ≤ (K : ℝ)^m := by
  exact_mod_cast (Nat.factorial_le_pow m).trans (Nat.pow_le_pow_left hm m)

theorem scaled_power_le_choose (n m K : ℕ) (hK : 0 < K) (hm : m ≤ K)
    (hn : 2*m ≤ n) (R H : ℝ) (hR : 0 ≤ R) (hH : 0 < H)
    (hcount : R/H ≤ n) :
    (R/(2*H*(K : ℝ)))^m ≤ (n.choose m : ℝ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hp : (R/H/2)^m ≤ ((n : ℝ)/2)^m :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hcount (by norm_num)) m
  calc
    _ = (R/H/2)^m/(K : ℝ)^m := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ ((n : ℝ)/2)^m/(K : ℝ)^m :=
      div_le_div_of_nonneg_right hp (pow_nonneg hKR.le _)
    _ ≤ ((n : ℝ)/2)^m/(m.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hfact (factorial_le_uniform_power m K hm)
    _ ≤ (n.choose m : ℝ) := half_power_le_choose n m hn

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem selectionProduct_squarefree {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) : Squarefree (selectionProduct f) := by
  rw [selectionProduct_eq_union P hd f hf]
  have hp (p : ℕ) (h : p ∈ selectionPrimes f) : p.Prime := by
    obtain ⟨i, _hi, hpi⟩ := Finset.mem_biUnion.mp h
    exact hP i p (hf i hpi)
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hpp q hqq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hpp) (hp q hqq)).mpr hpq)
  · intro p hpp
    exact (hp p hpp).squarefree

theorem cofactor_squarefree {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (q : ℕ) (hq : q ∈ cofactorChoices P m) : Squarefree q := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  exact selectionProduct_squarefree P hP hd f (fun i => ((mem_selections P m f).mp hf i).1)

theorem prime_factor_bin_recovery {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : f ∈ selections P m) (i : ι) :
    (selectionProduct f).primeFactors ∩ P i = f i := by
  have hs := (mem_selections P m f).mp hf
  rw [selectionProduct_primeFactors P hP hd f (fun j => (hs j).1)]
  exact recover_bin P hd f (fun j => (hs j).1) i

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem cofactor_card_half_lower {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hm : ∀ i, 2*m i ≤ (P i).card) :
    (∏ i, (((P i).card : ℝ)/2)^(m i)/((m i).factorial : ℝ)) ≤
      ((cofactorChoices P m).card : ℝ) := by
  rw [cofactorChoices_card P m hP hd, Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun i _ => by positivity)
    (fun i _ => half_power_le_choose (P i).card (m i) (hm i))

theorem cofactor_card_scaled_lower {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hm : ∀ i, 2*m i ≤ (P i).card)
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (H : ℝ) (hH : 0 < H)
    (hcount : ∀ i, R i/H ≤ (P i).card) :
    (∏ i, (R i)^(m i))/(2*H*((∑ i, m i)+1 : ℕ))^(∑ i, m i) ≤
      ((cofactorChoices P m).card : ℝ) := by
  let K : ℕ := (∑ i, m i)+1
  have hK : 0 < K := Nat.succ_pos _
  have hmi (i : ι) : m i ≤ K := by
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)).trans
      (Nat.le_succ _)
  calc
    _ = ∏ i, (R i/(2*H*(K : ℝ)))^(m i) := by
      simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      rfl
    _ ≤ ∏ i, ((P i).card.choose (m i) : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (div_nonneg (hR i) (by positivity)) _)
        (fun i _ => scaled_power_le_choose (P i).card (m i) K hK (hmi i)
          (hm i) (R i) H (hR i) hH (hcount i))
    _ = ((cofactorChoices P m).card : ℝ) := by
      rw [cofactorChoices_card P m hP hd, Nat.cast_prod]

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices

theorem denominator_loss_budget (A C T : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hT : 1 ≤ T) (k : ℕ) (hk : (k : ℝ) ≤ C*T) :
    (2*(A*Real.exp T)*((k+1 : ℕ) : ℝ))^k ≤
      Real.exp (C*(2*A+C+1)*T^2) := by
  have hT0 : 0 ≤ T := by linarith
  have hD : 0 ≤ 2*A+C+1 := by positivity
  have hconst : 2*A ≤ Real.exp (2*A*T) := by
    have he := Real.add_one_le_exp (2*A)
    have hm := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2*A))
    norm_num only [mul_one] at hm
    linarith
  have hkexp : ((k+1 : ℕ) : ℝ) ≤ Real.exp (C*T) := by
    have he := Real.add_one_le_exp (C*T)
    push_cast
    linarith
  have hbase : 2*(A*Real.exp T)*((k+1 : ℕ) : ℝ) ≤
      Real.exp ((2*A+C+1)*T) := by
    calc
      _ = (2*A)*Real.exp T*((k+1 : ℕ) : ℝ) := by ring
      _ ≤ Real.exp (2*A*T)*Real.exp T*Real.exp (C*T) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le) hkexp
          (Nat.cast_nonneg _) (by positivity)
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  calc
    _ ≤ (Real.exp ((2*A+C+1)*T))^k := pow_le_pow_left₀ (by positivity) hbase k
    _ = Real.exp ((k : ℝ)*((2*A+C+1)*T)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (C*(2*A+C+1)*T^2) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hk (mul_nonneg hD hT0)
      nlinarith only [h]

theorem cofactor_card_exponential_lower {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hm : ∀ i, 2*m i ≤ (P i).card)
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (A C T : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hcount : ∀ i, R i/(A*Real.exp T) ≤ (P i).card)
    (hk : ((∑ i, m i) : ℝ) ≤ C*T) :
    (∏ i, (R i)^(m i))*Real.exp (-C*(2*A+C+1)*T^2) ≤
      ((cofactorChoices P m).card : ℝ) := by
  have hden := denominator_loss_budget A C T hA hC hT (∑ i, m i)
    (by simpa only [Nat.cast_sum] using hk)
  have hfinite := cofactor_card_scaled_lower P m hP hd hm R hR (A*Real.exp T) (by positivity) hcount
  calc
    _ = (∏ i, (R i)^(m i))/Real.exp (C*(2*A+C+1)*T^2) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ ≤ (∏ i, (R i)^(m i))/(2*(A*Real.exp T)*((∑ i, m i)+1 : ℕ))^(∑ i, m i) :=
      div_le_div_of_nonneg_left (Finset.prod_nonneg (fun i _ => pow_nonneg (hR i) _))
        (by positivity) hden
    _ ≤ _ := hfinite

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin

theorem source_log_budget : ∀ᶠ z : ℝ in atTop,
    0 < Real.log z ∧ 1 ≤ Real.log (Real.log z) ∧
    0 < sourceW z ∧ 0 < sourceB z ∧
    Real.log (sourceB z) ≤ Real.log (Real.log z) := by
  filter_upwards [source_B_bounds,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with z hs ht
  have hw : 0 < sourceW z := (Real.exp_pos 1).trans_le hs.1
  have hb : 0 < sourceB z := by linarith [hs.2.1]
  exact ⟨hb.trans_le hs.2.2, ht, hw, hb, Real.log_le_log hb hs.2.2⟩

theorem sqrt_sourceW_dominates (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ z : ℝ in atTop, D*Real.log (Real.log z) ≤ Real.sqrt (sourceW z) := by
  have heps : 0 < 1/(D+1) := by positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1/2)).bound heps
  filter_upwards [Real.tendsto_log_atTop.eventually hsmall, source_log_budget] with z hz hs
  have hT : 0 < Real.log (Real.log z) := by linarith [hs.2.1]
  have hbound : (Real.log (Real.log z))^2 ≤ Real.sqrt (Real.log z)/(D+1) := by
    have hh : (Real.log (Real.log z))^2 ≤ (1/(D+1))*(Real.log z)^((1 : ℝ)/2) := by
      simpa only [Real.norm_eq_abs, Real.rpow_two,
        abs_of_nonneg (sq_nonneg (Real.log (Real.log z))),
        abs_of_nonneg (Real.rpow_nonneg hs.1.le ((1 : ℝ)/2))] using hz
    rw [← Real.sqrt_eq_rpow] at hh
    simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using hh
  have hpay : D*(Real.log (Real.log z))^2 ≤ Real.sqrt (Real.log z) := by
    have hh := (le_div_iff₀ (by positivity : 0 < D+1)).mp hbound
    nlinarith [sq_nonneg (Real.log (Real.log z))]
  have he : Real.sqrt (sourceW z) = Real.sqrt (Real.log z)/Real.log (Real.log z) := by
    rw [sourceW, Real.sqrt_div hs.1.le, Real.sqrt_sq_eq_abs, abs_of_pos hT]
  rw [he]
  apply (le_div_iff₀ hT).mpr
  nlinarith only [hpay]

theorem source_multiplicity_room (eta C : ℝ) (heta : 0 < eta) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop,
      2*C*Real.log (sourceB z) ≤ eta*Real.sqrt (sourceW z)/8 := by
  filter_upwards [sqrt_sourceW_dominates (16*C/eta) (by positivity), source_log_budget]
    with z hh hs
  have hdiv : (16*C*Real.log (Real.log z))/eta ≤ Real.sqrt (sourceW z) := by
    simpa only [div_mul_eq_mul_div] using hh
  have hmul := (div_le_iff₀ heta).mp hdiv
  have hlog := mul_le_mul_of_nonneg_left hs.2.2.2.2 (show 0 ≤ 2*C by positivity)
  linarith

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin

theorem source_prime_bin_data (eta C : ℝ) (heta : 0 < eta) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, ∀ R xi : ℝ, sourceW z ≤ R → eta ≤ xi → xi ≤ 1 →
      (1+xi)*R ≤ z →
      2*C*Real.log (sourceB z) ≤ ((primeBin R xi).card : ℝ) ∧
      ((1+xi)*R)/((8/eta)*Real.log z) ≤ ((primeBin R xi).card : ℝ) := by
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp (uniform_prime_bin_count heta)
  filter_upwards [sourceW_tendsto_atTop.eventually_ge_atTop R0,
    source_multiplicity_room eta C heta hC, source_log_budget] with z hz hroom hs
  have hL : 0 < Real.log z := hs.1
  intro R xi hR hxi hxi1 hRz
  have hc := hR0 R (hz.trans hR)
  have hRp : 0 < R := by linarith [hc.1]
  have hxp : 0 < xi := heta.trans_le hxi
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hc.1])
  have hU : R ≤ (1+xi)*R := by nlinarith
  have hlogle : Real.log R ≤ Real.log z := Real.log_le_log hRp (hU.trans hRz)
  have htwo : (1+xi)*R ≤ 2*R := by nlinarith
  have hlower := (hc.2 xi hxi hxi1).1
  constructor
  · calc
      _ ≤ eta*Real.sqrt (sourceW z)/8 := hroom
      _ ≤ eta*Real.sqrt R/8 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hR) heta.le)
          (by norm_num)
      _ ≤ xi*R/(4*Real.log R) := bin_scale_sqrt_lower hc.1 heta hxi
      _ ≤ _ := hlower
  · calc
      _ = eta*((1+xi)*R)/(8*Real.log z) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
      _ ≤ eta*(2*R)/(8*Real.log z) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htwo heta.le) (by positivity)
      _ = eta*R/(4*Real.log z) := by ring
      _ ≤ eta*R/(4*Real.log R) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hlogle (by norm_num))
      _ ≤ xi*R/(4*Real.log R) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxi hRp.le) (by positivity)
      _ ≤ _ := hlower

theorem source_cofactor_count_lower (eta C : ℝ) (heta : 0 < eta) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] (R xi : ι → ℝ) (m : ι → ℕ),
      (∀ i, sourceW z ≤ R i) → (∀ i, eta ≤ xi i) → (∀ i, xi i ≤ 1) →
      (∀ i, (1+xi i)*R i ≤ z) →
      Pairwise (fun i j => Disjoint (primeBin (R i) (xi i)) (primeBin (R j) (xi j))) →
      ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      (∏ i, ((1+xi i)*R i)^(m i))*
        Real.exp (-C*(16/eta+C+1)*(Real.log (Real.log z))^2) ≤
        ((cofactorChoices (fun i => primeBin (R i) (xi i)) m).card : ℝ) := by
  filter_upwards [source_prime_bin_data eta C heta hC, source_log_budget] with z hb hs
  intro ι inst R xi m hR hxi hxi1 hU hd hk
  have hprime (i : ι) (p : ℕ) (hp : p ∈ primeBin (R i) (xi i)) : Nat.Prime p :=
    ((mem_primeBin ((hs.2.2.1).trans_le (hR i)).le (heta.le.trans (hxi i)) p).mp hp).1
  have hhalf (i : ι) : 2*m i ≤ (primeBin (R i) (xi i)).card := by
    have hmi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
    have hmiR : (m i : ℝ) ≤ ((∑ j, m j : ℕ) : ℝ) := by exact_mod_cast hmi
    have hh := (hb (R i) (xi i) (hR i) (hxi i) (hxi1 i) (hU i)).1
    have hmR : 2*(m i : ℝ) ≤ (primeBin (R i) (xi i)).card := by linarith
    exact_mod_cast hmR
  have hcount (i : ι) : ((1+xi i)*R i)/((8/eta)*Real.exp (Real.log (Real.log z))) ≤
      ((primeBin (R i) (xi i)).card : ℝ) := by
    rw [Real.exp_log hs.1]
    exact (hb (R i) (xi i) (hR i) (hxi i) (hxi1 i) (hU i)).2
  have hsize : ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (Real.log z) :=
    hk.trans (mul_le_mul_of_nonneg_left hs.2.2.2.2 hC)
  have hnonneg (i : ι) : 0 ≤ (1+xi i)*R i :=
    mul_nonneg (by linarith [hxi i]) ((hs.2.2.1).trans_le (hR i)).le
  have hh := cofactor_card_exponential_lower (fun i => primeBin (R i) (xi i)) m
    hprime hd hhalf (fun i => (1+xi i)*R i) hnonneg (8/eta) C (Real.log (Real.log z))
    (by positivity) hC hs.2.1 hcount (by simpa only [Nat.cast_sum] using hsize)
  have he : (2 : ℝ)*(8/eta) = 16/eta := by ring
  rw [he] at hh
  exact hh

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
open NumberTheoryLean.LogarithmicBinPartition

theorem source_span_geometry : ∀ᶠ z : ℝ in atTop,
    0 < sourceW z ∧ sourceW z < z ∧
    ∀ xi : ℝ, 0 < xi → xi ≤ 1 → Real.log (1+xi) ≤ Real.log (z/sourceW z) := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [source_log_budget, hsmall, eventually_gt_atTop (1 : ℝ)] with z hs hz hz1
  have hzp : 0 < z := by linarith
  have hlogz : 0 < Real.log z := hs.1
  have hlog : Real.log z ≤ (1/2 : ℝ)*z := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogz, abs_of_pos hzp, id_eq] using hz
  have hden : 1 ≤ (Real.log (Real.log z))^2 := by nlinarith [hs.2.1]
  have hWle : sourceW z ≤ Real.log z := div_le_self hlogz.le hden
  have hw : 0 < sourceW z := hs.2.2.1
  have hwz : sourceW z < z := by linarith
  refine ⟨hw, hwz, ?_⟩
  intro xi hxi hxi1
  apply Real.log_le_log (by linarith : 0 < 1+xi)
  apply (le_div_iff₀ hw).mpr
  nlinarith [mul_le_mul_of_nonneg_right hxi1 hw.le]

noncomputable def actualBins (z xi : ℝ) : Fin (binCount (sourceW z) z xi) → Finset ℕ :=
  fun i => primeBin (lower (sourceW z) z xi i) (width (sourceW z) z xi i)

noncomputable def cofactorScale (z xi : ℝ) (m : Fin (binCount (sourceW z) z xi) → ℕ) : ℝ :=
  ∏ i, (upper (sourceW z) z xi i)^(m i)

theorem cofactorScale_nonneg {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) : 0 ≤ cofactorScale z xi m := by
  apply Finset.prod_nonneg
  intro i _
  have hb := bin_source_bounds hw hwz hxi i
  exact pow_nonneg ((hw.trans_le hb.1).trans hb.2.1).le _

theorem actual_source_many_cofactors (C xi : ℝ) (hC : 0 ≤ C) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop, ∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      cofactorScale z xi m*Real.exp (-C*(64/xi+C+1)*(Real.log (Real.log z))^2) ≤
        ((cofactorChoices (actualBins z xi) m).card : ℝ) := by
  filter_upwards [source_cofactor_count_lower (xi/4) C (by positivity) hC, source_span_geometry]
    with z hc hs
  intro m hm
  have hwide := effectiveWidth_ge_quarter hs.1 hs.2.1 hxi hxi1 (hs.2.2 xi hxi hxi1)
  have hwidth := effectiveWidth_le hs.1 hs.2.1 hxi
  have hh := hc (Fin (binCount (sourceW z) z xi)) (lower (sourceW z) z xi)
    (width (sourceW z) z xi) m
    (fun i => (bin_source_bounds hs.1 hs.2.1 hxi i).1)
    (fun _ => hwide) (fun _ => hwidth.trans hxi1)
    (fun i => (bin_source_bounds hs.1 hs.2.1 hxi i).2.2)
    (fun i j hij => bins_pairwise_disjoint hs.1 hs.2.1 hxi i j hij) hm
  have he : (16 : ℝ)/(xi/4) = 64/xi := by
    rw [div_div_eq_mul_div]
    norm_num
  rw [he] at hh
  exact hh

theorem actual_source_many_cofactors_power (C xi eps : ℝ) (hC : 0 ≤ C)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, ∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      cofactorScale z xi m/(sourceZ z)^eps ≤
        ((cofactorChoices (actualBins z xi) m).card : ℝ) := by
  have hD : 0 ≤ C*(64/xi+C+1) := by positivity
  filter_upwards [actual_source_many_cofactors C xi hC hxi hxi1,
    exp_loglog_sq_le_sourceZ (C*(64/xi+C+1)) eps hD heps, source_span_geometry]
    with z hc hg hs
  intro m hm
  calc
    _ ≤ cofactorScale z xi m/Real.exp ((C*(64/xi+C+1))*(Real.log (Real.log z))^2) :=
      div_le_div_of_nonneg_left (cofactorScale_nonneg hs.1 hs.2.1 hxi m) (Real.exp_pos _) hg
    _ = cofactorScale z xi m*Real.exp (-C*(64/xi+C+1)*(Real.log (Real.log z))^2) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ ≤ _ := hc m hm

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq
open ErdosInverseBoxHeight ErdosInversePrimeBin
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints

theorem selectionProduct_upper {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (f : ι → Finset ℕ) (hf : f ∈ selections P m)
    (U : ι → ℝ) (hU : ∀ i, ∀ p ∈ P i, (p : ℝ) ≤ U i) :
    (selectionProduct f : ℝ) ≤ ∏ i, (U i)^(m i) := by
  rw [selectionProduct, Nat.cast_prod]
  apply Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
  intro i _
  have hs := (mem_selections P m f).mp hf i
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _p ∈ f i, U i := Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p)
      (fun p hp => hU i p (hs.1 hp))
    _ = (U i)^(m i) := by rw [Finset.prod_const, hs.2]

theorem selectionProduct_lower {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (f : ι → Finset ℕ) (hf : f ∈ selections P m)
    (U : ι → ℝ) (hU : ∀ i, 0 ≤ U i) (F : ℝ) (hF : 0 < F)
    (hlower : ∀ i, ∀ p ∈ P i, U i/F ≤ (p : ℝ)) :
    (∏ i, (U i)^(m i))/F^(∑ i, m i) ≤ (selectionProduct f : ℝ) := by
  calc
    _ = ∏ i, (U i/F)^(m i) := by
      simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    _ ≤ (selectionProduct f : ℝ) := by
      rw [selectionProduct, Nat.cast_prod]
      apply Finset.prod_le_prod₀ (fun i _ => pow_nonneg (div_nonneg (hU i) hF.le) _)
      intro i _
      have hs := (mem_selections P m f).mp hf i
      rw [Nat.cast_prod, ← hs.2, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => div_nonneg (hU i) hF.le)
        (fun p hp => hlower i p (hs.1 hp))

theorem actual_cofactor_range {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    cofactorScale z xi m/(1+xi)^(∑ i, m i) ≤ (q : ℝ) ∧ (q : ℝ) ≤ cofactorScale z xi m := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  have hU (i : Fin (binCount (sourceW z) z xi)) : 0 ≤ upper (sourceW z) z xi i := by
    have hb := bin_source_bounds hw hwz hxi i
    exact ((hw.trans_le hb.1).trans hb.2.1).le
  have hlower (i : Fin (binCount (sourceW z) z xi)) (p : ℕ) (hp : p ∈ actualBins z xi i) :
      upper (sourceW z) z xi i/(1+xi) ≤ (p : ℝ) := by
    have hb := (mem_primeBin (endpoint_pos hw i.1).le (effectiveWidth_pos hw hwz hxi).le p).mp hp
    have hwidth := effectiveWidth_le hw hwz hxi
    have hl : upper (sourceW z) z xi i/(1+xi) ≤ lower (sourceW z) z xi i := by
      apply (div_le_iff₀ (by linarith : 0 < 1+xi)).mpr
      change (1+effectiveWidth (sourceW z) z xi)*lower (sourceW z) z xi i ≤ _
      have hl0 : 0 ≤ lower (sourceW z) z xi i := (endpoint_pos hw i.1).le
      have h := mul_le_mul_of_nonneg_right hwidth hl0
      nlinarith
    exact hl.trans hb.2.1.le
  have hupper (i : Fin (binCount (sourceW z) z xi)) (p : ℕ) (hp : p ∈ actualBins z xi i) :
      (p : ℝ) ≤ upper (sourceW z) z xi i :=
    ((mem_primeBin (endpoint_pos hw i.1).le (effectiveWidth_pos hw hwz hxi).le p).mp hp).2.2
  exact ⟨selectionProduct_lower (actualBins z xi) m f hf (upper (sourceW z) z xi) hU (1+xi)
      (by linarith) hlower,
    selectionProduct_upper (actualBins z xi) m f hf (upper (sourceW z) z xi) hupper⟩

theorem actual_cofactor_positive {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) : 0 < q :=
  cofactor_positive (actualBins z xi) m
    (fun i _ hp => (bin_prime_in_source hw hwz hxi i hp).1) q hq

theorem actual_cofactor_ratio {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q r : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) (hr : r ∈ cofactorChoices (actualBins z xi) m) :
    (q : ℝ)/(r : ℝ) ≤ (1+xi)^(∑ i, m i) := by
  have hqp := actual_cofactor_range hw hwz hxi m q hq
  have hrp := actual_cofactor_range hw hwz hxi m r hr
  have hF : 0 < (1+xi)^(∑ i, m i) := by positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast actual_cofactor_positive hw hwz hxi m r hr
  apply (div_le_iff₀ hr0).mpr
  have h := (div_le_iff₀ hF).mp hrp.1
  simpa only [mul_comm] using hqp.2.trans h

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler
open NumberTheoryLean.LogarithmicBinScale

theorem actual_reciprocal_variation {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q r : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) (hr : r ∈ cofactorChoices (actualBins z xi) m) :
    (q : ℝ)⁻¹ ≤ (1+xi)^(∑ i, m i)*(r : ℝ)⁻¹ := by
  have h := actual_cofactor_ratio hw hwz hxi m r q hr hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast actual_cofactor_positive hw hwz hxi m q hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast actual_cofactor_positive hw hwz hxi m r hr
  have hm := (div_le_iff₀ hq0).mp h
  have hi : (1 : ℝ)/(q : ℝ) ≤ (1+xi)^(∑ i, m i)/(r : ℝ) := by
    apply (div_le_div_iff₀ hq0 hr0).mpr
    simpa only [one_mul] using hm
  simpa only [one_div, div_eq_mul_inv, one_mul] using hi

theorem source_bin_factor_subpower (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, ∀ (xi : ℝ) (k : ℕ), 0 < xi → xi ≤ 1 →
      (k : ℝ) ≤ C*Real.log (sourceB z) → (1+xi)^k ≤ (sourceZ z)^eps := by
  filter_upwards [source_log_budget, exp_loglog_sq_le_sourceZ C eps hC heps] with z hs hg
  intro xi k hxi hxi1 hk
  have hbase : 0 < 1+xi := by linarith
  have hlog : Real.log (1+xi) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hbase
    linarith
  have hlen : (k : ℝ) ≤ C*Real.log (Real.log z) :=
    hk.trans (mul_le_mul_of_nonneg_left hs.2.2.2.2 hC)
  have hT : Real.log (Real.log z) ≤ (Real.log (Real.log z))^2 := by nlinarith [hs.2.1]
  calc
    _ = Real.exp ((k : ℝ)*Real.log (1+xi)) := by
      rw [Real.exp_nat_mul, Real.exp_log hbase]
    _ ≤ Real.exp (C*(Real.log (Real.log z))^2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (k : ℝ)*1 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
        _ ≤ C*Real.log (Real.log z) := by simpa only [mul_one] using hlen
        _ ≤ _ := mul_le_mul_of_nonneg_left hT hC
    _ ≤ _ := hg

theorem source_cofactor_weight_variation (C xi eps : ℝ) (hC : 0 ≤ C)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, ∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) → ∀ q r : ℕ,
      q ∈ cofactorChoices (actualBins z xi) m → r ∈ cofactorChoices (actualBins z xi) m →
      (q : ℝ)/(r : ℝ) ≤ (sourceZ z)^eps ∧
        (q : ℝ)⁻¹ ≤ (sourceZ z)^eps*(r : ℝ)⁻¹ := by
  filter_upwards [source_span_geometry, source_bin_factor_subpower C eps hC heps] with z hs hb
  intro m hm q r hq hr
  have hf := hb xi (∑ i, m i) hxi hxi1 hm
  exact ⟨(actual_cofactor_ratio hs.1 hs.2.1 hxi m q r hq hr).trans hf,
    (actual_reciprocal_variation hs.1 hs.2.1 hxi m q r hq hr).trans
      (mul_le_mul_of_nonneg_right hf (inv_nonneg.mpr (Nat.cast_nonneg r)))⟩

end ErdosCofactorChoices

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseCells
open ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints NumberTheoryLean.LogarithmicBinPartition

theorem actual_cofactorScale_pos {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) : 0 < cofactorScale z xi m := by
  apply Finset.prod_pos
  intro i _
  have hb := bin_source_bounds hw hwz hxi i
  exact pow_pos ((hw.trans_le hb.1).trans hb.2.1) _

theorem actual_cofactor_squarefree {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) : Squarefree q :=
  cofactor_squarefree (actualBins z xi) m (fun i _ hp => (bin_prime_in_source hw hwz hxi i hp).1)
    (fun i j hij => bins_pairwise_disjoint hw hwz hxi i j hij) q hq

theorem actual_cofactor_effective_range {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    cofactorScale z xi m/(1+effectiveWidth (sourceW z) z xi)^(∑ i,m i) ≤ (q : ℝ) ∧
      (q : ℝ) ≤ cofactorScale z xi m := by
  have hupper := (actual_cofactor_range hw hwz hxi m q hq).2
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have htheta := effectiveWidth_pos hw hwz hxi
  have hF : 0 < 1+effectiveWidth (sourceW z) z xi := by linarith
  have hU : ∀ i : Fin (binCount (sourceW z) z xi),0 ≤ upper (sourceW z) z xi i := by
    intro i
    have hb := bin_source_bounds hw hwz hxi i
    exact ((hw.trans_le hb.1).trans hb.2.1).le
  have hlower : ∀ i : Fin (binCount (sourceW z) z xi),∀ p ∈ actualBins z xi i,
      upper (sourceW z) z xi i/(1+effectiveWidth (sourceW z) z xi) ≤ (p : ℝ) := by
    intro i p hp
    have hh := (mem_primeBin (endpoint_pos hw i.1).le htheta.le p).mp hp
    have he : upper (sourceW z) z xi i/(1+effectiveWidth (sourceW z) z xi) = lower (sourceW z) z xi i := by
      change ((1+effectiveWidth (sourceW z) z xi)*lower (sourceW z) z xi i)/(1+effectiveWidth (sourceW z) z xi) = _
      field_simp
    rw [he]
    exact hh.2.1.le
  exact ⟨selectionProduct_lower (actualBins z xi) m f hf (upper (sourceW z) z xi) hU
    (1+effectiveWidth (sourceW z) z xi) hF hlower,hupper⟩

theorem source_cofactor_cell_data (C xi eps : ℝ) (hC : 0 ≤ C) (hxi : 0 < xi)
    (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i,m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      0 < cofactorScale z xi m ∧ 0 < (cofactorChoices (actualBins z xi) m).card ∧
      cofactorScale z xi m/(sourceZ z)^eps ≤ ((cofactorChoices (actualBins z xi) m).card : ℝ) ∧
      ∀ q ∈ cofactorChoices (actualBins z xi) m,0 < q ∧ Squarefree q := by
  filter_upwards [source_span_geometry,actual_source_many_cofactors_power C xi eps hC hxi hxi1 heps] with z hs hc
  intro m hm
  have hS := actual_cofactorScale_pos hs.1 hs.2.1 hxi m
  have hcount := hc m hm
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hn : (0 : ℝ) < (cofactorChoices (actualBins z xi) m).card :=
    (div_pos hS (Real.rpow_pos_of_pos hZ eps)).trans_le hcount
  refine ⟨hS,by exact_mod_cast hn,hcount,?_⟩
  intro q hq
  exact ⟨actual_cofactor_positive hs.1 hs.2.1 hxi m q hq,
    actual_cofactor_squarefree hs.1 hs.2.1 hxi m q hq⟩

end ErdosInverseCells

end

end Erdos970

end OAI
