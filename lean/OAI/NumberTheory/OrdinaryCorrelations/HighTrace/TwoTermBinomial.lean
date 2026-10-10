import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.MemSupport

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SourceCylinder
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ p, Fintype (Ω p)]
local instance twoTermBinomialDecidableEqIndex : DecidableEq ι := Classical.decEq _
local instance twoTermBinomialDecidableEqIntersection (E : Finset (Cylinder Ω)) :
    DecidableEq (Intersection E) := Classical.decEq _
local instance twoTermBinomialDecidableLEIntersection (E : Finset (Cylinder Ω)) :
    DecidableLE (Intersection E) := Classical.decRel _
local instance twoTermBinomialDecidableLTIntersection (E : Finset (Cylinder Ω)) :
    DecidableLT (Intersection E) := Classical.decRel _
local instance twoTermBinomialLocallyFiniteOrderIntersection (E : Finset (Cylinder Ω)) :
    LocallyFiniteOrder (Intersection E) :=
  Fintype.toLocallyFiniteOrder

lemma two_term_binomial (a k : ℕ) :
    a ^ (k + 1) + (k + 1) * a ^ k ≤ (a + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.mul_le_mul_right (a + 1) ih
    simp only [pow_succ] at h ⊢
    calc
      a ^ k * a * a + (k+1+1) * (a^k*a)
          ≤ a ^ k * a * a + (k+1+1) * (a^k*a) + (k+1)*a^k := Nat.le_add_right _ _
      _ = (a^k*a + (k+1)*a^k)*(a+1) := by ring
      _ ≤ (a+1)^k*(a+1)*(a+1) := h

lemma double_power_le (n : ℕ) : 2 * n ^ (n+1) ≤ (n+1) ^ (n+1) := by
  have h := two_term_binomial n n
  have h' : 2 * n ^ (n+1) ≤ n ^ (n+1) + (n+1) * n ^ n := by
    rw [pow_succ]
    calc
      2*(n^n*n) ≤ 2*(n^n*n)+n^n := Nat.le_add_right _ _
      _ = n^n*n+(n+1)*n^n := by ring
  exact h'.trans h

lemma factorial_power_bound (m : ℕ) (hm : 2 ≤ m) :
    2 ^ m * m.factorial ≤ m ^ (m+1) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : 2 ≤ n
    · calc
        2 ^ (n+1) * (n+1).factorial = (n+1) * (2 * (2^n * n.factorial)) := by
          rw [pow_succ, Nat.factorial_succ]; ring
        _ ≤ (n+1) * (2 * n ^ (n+1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (ih hn))
        _ ≤ (n+1) * (n+1) ^ (n+1) := Nat.mul_le_mul_left _ (double_power_le n)
        _ = (n+1) ^ (n+1+1) := by rw [pow_succ]; ring
    · have : n = 1 := by omega
      subst n
      decide

lemma geometric_two_bound (m : ℕ) : (∑ k ∈ Finset.range m, 2^k) ≤ 2^m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma choose_factorial_le {m k : ℕ} (hk : k ≤ m) :
    m.choose k * k.factorial ≤ m.factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  calc
    m.choose k * k.factorial ≤ (m.choose k * k.factorial) * (m-k).factorial := by
      exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
    _ = m.factorial := h

omit [Fintype ι] in
lemma proper_subset_factorial_sum (U : Finset ι) :
    (∑ S ∈ U.powerset with S.card < U.card, 2 ^ S.card * S.card.factorial) ≤
      2 ^ U.card * U.card.factorial := by
  classical
  rw [Finset.sum_filter]
  rw [Finset.sum_powerset]
  have hlevel (k : ℕ) :
      (∑ S ∈ U.powersetCard k,
        if S.card < U.card then 2 ^ S.card * S.card.factorial else 0) =
      U.card.choose k * (if k < U.card then 2 ^ k * k.factorial else 0) := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_powersetCard k U (fun k => if k < U.card then 2 ^ k * k.factorial else 0))
  simp_rw [hlevel]
  rw [Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, mul_zero, add_zero]
  calc
    (∑ k ∈ Finset.range U.card,
      U.card.choose k * (if k < U.card then 2 ^ k * k.factorial else 0))
        ≤ ∑ k ∈ Finset.range U.card, 2 ^ k * U.card.factorial := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      simp only [hk', ↓reduceIte]
      calc
        U.card.choose k * (2 ^ k * k.factorial) = 2 ^ k * (U.card.choose k * k.factorial) := by ring
        _ ≤ 2 ^ k * U.card.factorial := Nat.mul_le_mul_left _ (choose_factorial_le hk'.le)
    _ = (∑ k ∈ Finset.range U.card, 2 ^ k) * U.card.factorial := by rw [Finset.sum_mul]
    _ ≤ 2 ^ U.card * U.card.factorial := Nat.mul_le_mul_right _ (geometric_two_bound _)

omit [∀ p, Fintype (Ω p)] in
lemma intersection_support_inj (E : Finset (Cylinder Ω)) (I : Intersection E) :
    Set.InjOn (fun J : Intersection E => J.val.support) {J | J ≤ I} := by
  intro J hJ K hK heq
  exact Subtype.ext (Cylinder.eq_of_support_eq hJ hK heq)

lemma coefficient_crude (E : Finset (Cylinder Ω)) (I : Intersection E) :
    (coefficient E I).natAbs ≤ 2 ^ I.val.support.card * I.val.support.card.factorial := by
  classical
  have aux : ∀ m, ∀ I : Intersection E, I.val.support.card = m →
      (coefficient E I).natAbs ≤ 2 ^ m * m.factorial := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro I hcard
      by_cases hI : I = ⊥
      · subst I
        simp [coefficient, IncidenceAlgebra.mu_self, show (⊥ : Intersection E).val = ⊥ from rfl] at hcard ⊢
        subst m
        simp
      · have hmu : coefficient E I = -∑ J ∈ Finset.Ico ⊥ I, coefficient E J := by
          exact IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (Ne.symm hI)
        rw [hmu, Int.natAbs_neg]
        calc
          (∑ J ∈ Finset.Ico ⊥ I, coefficient E J).natAbs
              ≤ ∑ J ∈ Finset.Ico ⊥ I, (coefficient E J).natAbs := Int.natAbs_sum_le _ _
          _ ≤ ∑ J ∈ Finset.Ico ⊥ I, 2 ^ J.val.support.card * J.val.support.card.factorial := by
            apply Finset.sum_le_sum
            intro J hJ
            have hjlt : J.val.support.card < m := by
              rw [← hcard]
              exact Finset.card_lt_card (Cylinder.support_ssubset (Finset.mem_Ico.mp hJ).2)
            exact ih _ hjlt J rfl
          _ = ∑ S ∈ (Finset.Ico ⊥ I).image (fun J : Intersection E => J.val.support),
              2 ^ S.card * S.card.factorial := by
            symm
            apply Finset.sum_image
            intro J hJ K hK hJK
            exact intersection_support_inj E I (Finset.mem_Ico.mp hJ).2.le
              (Finset.mem_Ico.mp hK).2.le hJK
          _ ≤ ∑ S ∈ I.val.support.powerset with S.card < I.val.support.card,
              2 ^ S.card * S.card.factorial := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro S hS
              obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hS
              have hlt := (Finset.mem_Ico.mp hJ).2
              exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Cylinder.support_mono hlt.le),
                Finset.card_lt_card (Cylinder.support_ssubset hlt)⟩
            · intros; omega
          _ ≤ 2 ^ I.val.support.card * I.val.support.card.factorial := proper_subset_factorial_sum _
          _ = 2 ^ m * m.factorial := by rw [hcard]
  exact aux _ I rfl

end OrdinaryCorrelations.SourceCylinder

end

end OAI
