import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerDivisors
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerSupport
import OAI.NumberTheory.CubicMoment.Estimates.BalancedErrorMoment

namespace OAI

/-! Logarithmic multiplicities and moments of products of finitely many prime powers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_one : idealExponentOf 1 = 0 := by
  simp [idealExponentOf, Associates.factors', UniqueFactorizationMonoid.factors_one]

lemma idealExponentOf_primePower_card {p : Eisenstein} (hp : Prime p) (j : ℕ) :
    (idealExponentOf (p^j)).support.card ≤ 1 := by
  have hsub : (idealExponentOf (p^j)).support ⊆ (idealExponentOf p).support := by
    induction j with
    | zero => simp [idealExponentOf_one]
    | succ j ih =>
      rw [pow_succ, idealExponentOf_mul (pow_ne_zero _ hp.ne_zero) hp.ne_zero]
      exact Finsupp.support_add.trans (Finset.union_subset ih (Finset.Subset.refl _))
  apply (Finset.card_le_card hsub).trans_eq
  rw [idealExponentOf_support_card hp.irreducible.squarefree,
    UniqueFactorizationMonoid.card_factors_of_irreducible hp.irreducible]

private lemma primary_prime_pow {p : Eisenstein} (hp : primary p) (j : ℕ) : primary (p^j) := by
  induction j with
  | zero => simp [primary]
  | succ j ih => simpa only [pow_succ] using primary_mul ih hp

lemma idealExponentOf_prod_card {κ : Type*} (S : Finset κ) (f : κ → Eisenstein)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    (idealExponentOf (∏ i ∈ S, f i)).support.card ≤
      ∑ i ∈ S, (idealExponentOf (f i)).support.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [idealExponentOf_one]
  | @insert i S hi ih =>
    have hS : ∀ j ∈ S, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (idealExponentOf_mul_support_card (hf i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr hS)).trans (Nat.add_le_add_left (ih hS) _)

lemma orderedPrimePowerSupport_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ a ∈ S i, ∃ p : Eisenstein, ∃ j : ℕ,
      primaryPrime p ∧ 0 < j ∧ a = p^j)
    {b : Eisenstein} (hb : b ∈ orderedConvolutionSupport S) :
    primary b ∧ (idealExponentOf b).support.card ≤ Fintype.card ι := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  have hp (i : ι) : primary (f i) ∧ (idealExponentOf (f i)).support.card ≤ 1 := by
    obtain ⟨p,j,hp,_,he⟩ := hS i (f i) (Fintype.mem_piFinset.mp hf i)
    rw [he]
    exact ⟨primary_prime_pow hp.1 j,idealExponentOf_primePower_card hp.2 j⟩
  refine ⟨primary_finset_prod _ _ (fun i _ => (hp i).1),?_⟩
  calc
    _ ≤ ∑ i : ι, (idealExponentOf (f i)).support.card :=
      idealExponentOf_prod_card _ f (fun i _ => primary_ne_zero (hp i).1)
    _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum (fun i _ => (hp i).2)
    _ = _ := by simp

/-- A fixed logarithmic power is bounded by every positive norm power,
with an explicit constant uniform down to norm one. -/
lemma natLog_power_bound (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((Nat.log 2 n + 1 : ℕ) : ℝ)^m ≤ C*(n:ℝ)^ε := by
  by_cases hm : m = 0
  · subst m
    refine ⟨1,zero_lt_one,?_⟩
    intro n hn
    simpa using Real.one_le_rpow (by exact_mod_cast hn) hε.le
  let δ : ℝ := ε/m
  have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hδ : 0 < δ := div_pos hε hm0
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := 1/(δ*Real.log 2)+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A^m,pow_pos hA _,?_⟩
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := zero_lt_one.trans_le hn1
  have hlog : (Nat.log 2 n:ℝ) ≤ Real.log n/Real.log 2 := by
    change (Nat.log 2 n:ℝ) ≤ Real.logb (2:ℝ) (n:ℝ)
    rw [← Real.natFloor_logb_natCast 2 n]
    exact Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hn1)
  have hx : 1 ≤ (n:ℝ)^δ := Real.one_le_rpow hn1 hδ.le
  have hbase : ((Nat.log 2 n+1:ℕ):ℝ) ≤ A*(n:ℝ)^δ := by
    push_cast
    calc
      _ ≤ Real.log n/Real.log 2+1 := by linarith
      _ ≤ ((n:ℝ)^δ/δ)/Real.log 2+(n:ℝ)^δ :=
        add_le_add (div_le_div_of_nonneg_right (Real.log_le_rpow_div hn0.le hδ) hL.le) hx
      _ = _ := by dsimp [A]; ring
  have he : ((n:ℝ)^δ)^m = (n:ℝ)^ε := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ ε (ne_of_gt hm0)
  calc
    _ ≤ (A*(n:ℝ)^δ)^m := pow_le_pow_left₀ (by positivity) hbase m
    _ = _ := by rw [mul_pow,he]

lemma boundedPrimeSupport_pair_fiber_power (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Finset Eisenstein) (Y : ℝ), 1 ≤ Y →
      (∀ b ∈ B, primary b ∧ norm b ≤ Y ∧ (idealExponentOf b).support.card ≤ k) →
      ∀ n ∈ productSupport B,
      (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ C*Y^ε := by
  obtain ⟨C,hC,hbound⟩ := natLog_power_bound (2*k) (show 0 < ε/2 by positivity)
  refine ⟨C,hC,?_⟩
  intro B Y hY hB n hn
  have hraw := boundedPrimeSupport_pair_fiber B (fun b hb => (hB b hb).1) k
    (fun b hb => (hB b hb).2.2) hn
  obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  have hn0 : n ≠ 0 := by
    rw [← he]
    exact mul_ne_zero (primary_ne_zero (hB a ha).1) (primary_ne_zero (hB b hb).1)
  have hnN : (normNat n:ℝ) ≤ Y^2 := by
    rw [normNat_cast,← he,norm_mul_eq,pow_two]
    exact mul_le_mul (hB a ha).2.1 (hB b hb).2.1 (norm_nonneg _) (by linarith)
  have hnat : 1 ≤ normNat n := Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hn0)
  calc
    _ ≤ ((Nat.log 2 (normNat n)+1:ℕ):ℝ)^(2*k) := by exact_mod_cast hraw
    _ ≤ C*(normNat n:ℝ)^(ε/2) := hbound _ hnat
    _ ≤ C*(Y^2)^(ε/2) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnN (by positivity)) hC.le
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ Y)]
      congr 2
      ring

/-- Actual fourth moments for supports with a bounded number of prime
bases. The arbitrary higher powers cost only an arbitrarily small norm power. -/
theorem boundedPrimeSupport_fourth_moment (hHuxley : HuxleyAdditiveLargeSieve)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Y : ℝ), 1 ≤ Q → 1 ≤ Y →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, primary b ∧ norm b ≤ Y ∧ (idealExponentOf b).support.card ≤ k) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4) ≤
        C*Q^ε*(Q^2+Y^2)*Y^ε*(∑ b ∈ B, ‖v b‖^2)^2 := by
  obtain ⟨C,hC,hfourth⟩ := ordinary_mixed_fourth_moment hHuxley hε
  obtain ⟨K,hK,hfiber⟩ := boundedPrimeSupport_pair_fiber_power k hε
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro Q Y hQ hY P B hP hB v
  have h := hfourth Q Y hQ hY P B hP
    (fun b hb => ⟨primary_ne_zero (hB b hb).1,(hB b hb).2.1⟩)
    (K*Y^ε) (hfiber B Y hY hB) v
  exact h.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
