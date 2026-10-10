import OAI.NumberTheory.CubicMoment.Estimates.IdealVonMangoldt
import OAI.NumberTheory.CubicMoment.Estimates.SparseFourthMoment
import Mathlib.Data.Finsupp.Interval

namespace OAI

/-! Divisor and pair-product multiplicities with a bounded number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_inj_primary {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : idealExponentOf a = idealExponentOf b) : a = b := by
  have hA := idealExponentOf_associated (primary_ne_zero ha)
  have hB := idealExponentOf_associated (primary_ne_zero hb)
  rw [h] at hA
  exact primary_associated_eq ha hb (hA.symm.trans hB)

lemma idealExponentOf_le_of_dvd {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ∣ b) : idealExponentOf a ≤ idealExponentOf b := by
  obtain ⟨c,rfl⟩ := hab
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hb).2
  rw [idealExponentOf_mul ha hc]
  exact le_add_of_nonneg_right zero_le

lemma primary_divisor_card_exponents (T : Finset Eisenstein)
    (hT : ∀ a ∈ T, primary a) {b : Eisenstein} (hb : b ≠ 0) :
    (T.filter (fun a => a ∣ b)).card ≤
      ∏ p ∈ (idealExponentOf b).support, (idealExponentOf b p + 1) := by
  let D := T.filter (fun a => a ∣ b)
  have hinj : Set.InjOn idealExponentOf (D : Set Eisenstein) := by
    intro a ha c hc he
    exact idealExponentOf_inj_primary (hT a (Finset.mem_filter.mp ha).1)
      (hT c (Finset.mem_filter.mp hc).1) he
  have hsub : D.image idealExponentOf ⊆ Finset.Iic (idealExponentOf b) := by
    intro ν hν
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hν
    exact Finset.mem_Iic.mpr (idealExponentOf_le_of_dvd
      (primary_ne_zero (hT a (Finset.mem_filter.mp ha).1)) hb (Finset.mem_filter.mp ha).2)
  calc
    D.card = (D.image idealExponentOf).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Iic (idealExponentOf b)).card := Finset.card_le_card hsub
    _ = _ := by rw [Finsupp.card_Iic]; simp

lemma idealPrimeRepresentative_normNat_ge_two (p : EisensteinIdealPrime) :
    2 ≤ normNat (idealPrimeRepresentative p) := by
  have hp := idealPrimeRepresentative_irreducible p
  have hz := normNat_ne_zero hp.ne_zero
  have ho : normNat (idealPrimeRepresentative p) ≠ 1 := by
    intro h
    apply hp.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast, h]
    norm_num
  omega

lemma idealExponentOf_le_log_norm {b : Eisenstein} (hb : b ≠ 0)
    (p : EisensteinIdealPrime) : idealExponentOf b p ≤ Nat.log 2 (normNat b) := by
  have hle : Finsupp.single p (idealExponentOf b p) ≤ idealExponentOf b :=
    Finsupp.single_le_iff.mpr le_rfl
  have hreal : (normNat (idealPrimeRepresentative p) : ℝ) ^ idealExponentOf b p ≤
      (normNat b : ℝ) := by
    calc
      _ = idealExponentNorm (Finsupp.single p (idealExponentOf b p)) :=
        (idealExponentNorm_single _ _).symm
      _ ≤ idealExponentNorm (idealExponentOf b) := idealExponentNorm_mono hle
      _ = norm b := idealExponentOf_norm hb
      _ = _ := (normNat_cast b).symm
  have hpow : normNat (idealPrimeRepresentative p) ^ idealExponentOf b p ≤ normNat b := by
    exact_mod_cast hreal
  exact Nat.le_log_of_pow_le (by decide)
    ((Nat.pow_le_pow_left (idealPrimeRepresentative_normNat_ge_two p) _).trans hpow)

/-- Only the number of distinct prime bases enters this bound; their
exponents may be arbitrarily large. -/
theorem primary_divisor_card_log (T : Finset Eisenstein)
    (hT : ∀ a ∈ T, primary a) {b : Eisenstein} (hb : b ≠ 0) {k : ℕ}
    (hk : (idealExponentOf b).support.card ≤ k) :
    (T.filter (fun a => a ∣ b)).card ≤ (Nat.log 2 (normNat b) + 1)^k := by
  apply (primary_divisor_card_exponents T hT hb).trans
  calc
    _ ≤ ∏ _p ∈ (idealExponentOf b).support, (Nat.log 2 (normNat b) + 1) :=
      Finset.prod_le_prod (fun p _ => Nat.add_le_add_right (idealExponentOf_le_log_norm hb p) 1)
    _ = (Nat.log 2 (normNat b) + 1)^(idealExponentOf b).support.card := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hk

/-- For primary factors, fixing the first divisor determines the second. -/
lemma primary_pair_fiber_le_divisors (B : Finset Eisenstein)
    (hB : ∀ a ∈ B, primary a) (n : Eisenstein) :
    ((B.product B).filter (fun z => z.1*z.2 = n)).card ≤
      (B.filter (fun a => a ∣ n)).card := by
  let T := (B.product B).filter (fun z => z.1*z.2 = n)
  have hinj : Set.InjOn Prod.fst (T : Set (Eisenstein × Eisenstein)) := by
    intro a ha b hb he
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext he
    have hn : a.1 ≠ 0 := primary_ne_zero (hB a.1 (Finset.mem_product.mp ha'.1).1)
    apply mul_left_cancel₀ hn
    calc
      a.1*a.2 = n := ha'.2
      _ = b.1*b.2 := hb'.2.symm
      _ = a.1*b.2 := by rw [he]
  have hsub : T.image Prod.fst ⊆ B.filter (fun a => a ∣ n) := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hz).1,?_⟩
    exact ⟨z.2,hzn.symm⟩
  exact (Finset.card_image_iff.mpr hinj).symm.le.trans (Finset.card_le_card hsub)

lemma idealExponentOf_mul_support_card {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0) :
    (idealExponentOf (a*b)).support.card ≤
      (idealExponentOf a).support.card + (idealExponentOf b).support.card := by
  rw [idealExponentOf_mul ha hb]
  exact (Finset.card_le_card Finsupp.support_add).trans (Finset.card_union_le _ _)

/-- Pair-product fibers of elements with at most `k` prime bases cost
only a `2k`-th power of a logarithm, even for high prime powers. -/
theorem boundedPrimeSupport_pair_fiber (B : Finset Eisenstein)
    (hB : ∀ a ∈ B, primary a) (k : ℕ)
    (hk : ∀ a ∈ B, (idealExponentOf a).support.card ≤ k)
    {n : Eisenstein} (hn : n ∈ productSupport B) :
    ((B.product B).filter (fun z => z.1*z.2 = n)).card ≤
      (Nat.log 2 (normNat n) + 1)^(2*k) := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  have ha0 := primary_ne_zero (hB a ha)
  have hb0 := primary_ne_zero (hB b hb)
  apply (primary_pair_fiber_le_divisors B hB _).trans
  apply primary_divisor_card_log B hB (mul_ne_zero ha0 hb0)
  exact (idealExponentOf_mul_support_card ha0 hb0).trans (by
    have h1 := hk a ha
    have h2 := hk b hb
    omega)

end CubicFirstMoment

end

end OAI
