import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HarmonicResidueDomination

theorem class_card_le (Q L:ℕ) (S:Finset ℕ) (a:ZMod Q)
    (hS:∀n∈S,n≤2*L ∧ (n:ZMod Q)=a) : S.card≤2*L/Q+1 := by
  classical
  calc
    S.card ≤ (Finset.range (2*L/Q+1)).card := by
      apply Finset.card_le_card_of_injOn (fun n=>n/Q)
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right (hS n hn).1))
      · intro n hn m hm he
        change n/Q=m/Q at he
        have hr : n%Q=m%Q := (ZMod.natCast_eq_natCast_iff' n m Q).mp
          ((hS n hn).2.trans (hS m hm).2.symm)
        have h1 := Nat.mod_add_div n Q
        have h2 := Nat.mod_add_div m Q
        rw [hr,he] at h1
        omega
    _ = _ := Finset.card_range _

theorem harmonic_class_le (Q L:ℕ) (hQ:0<Q) (hL:Q≤L)
    (S:Finset ℕ) (a:ZMod Q) (hS:∀n∈S,L≤n ∧ n≤2*L ∧ (n:ZMod Q)=a) :
    (∑n∈S,(n:ℝ)⁻¹)≤3/(Q:ℝ) := by
  have hL0 : 0<L := hQ.trans_le hL
  have hLR : (0:ℝ)<L := by exact_mod_cast hL0
  have hQR : (0:ℝ)<Q := by exact_mod_cast hQ
  have hc := class_card_le Q L S a (fun n hn=>(hS n hn).2)
  have hcR : (S.card:ℝ)≤(2*L/Q:ℕ)+1 := by exact_mod_cast hc
  have hdR : ((2*L/Q:ℕ):ℝ)*(Q:ℝ)≤2*(L:ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (2*L) Q
  have hQL : (Q:ℝ)≤L := by exact_mod_cast hL
  calc
    _ ≤ (S.card:ℝ)*(L:ℝ)⁻¹ := by
      calc
        _ ≤ ∑_n∈S,(L:ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro n hn
          exact inv_anti₀ hLR (by exact_mod_cast (hS n hn).1)
        _ = _ := by simp
    _ ≤ 3/(Q:ℝ) := by
      apply (le_div_iff₀ hQR).mpr
      rw [mul_assoc,inv_mul_eq_div,← mul_div_assoc]
      apply (div_le_iff₀ hLR).mpr
      nlinarith [mul_le_mul_of_nonneg_right hcR hQR.le]

theorem harmonic_cover_le {J:Type*} [Fintype J]
    (Q:ℕ) (hQ:0<Q) (L:J→ℕ) (hL:∀j,Q≤L j) (S:Finset ℕ) (a:ZMod Q)
    (hcover:∀n∈S,∃j,L j≤n ∧ n≤2*L j) :
    (∑n∈S.filter (fun n:ℕ=>(n:ZMod Q)=a),(n:ℝ)⁻¹)≤3*Fintype.card J/(Q:ℝ) := by
  classical
  let T : J→Finset ℕ := fun j=>S.filter (fun n=>L j≤n ∧ n≤2*L j ∧ (n:ZMod Q)=a)
  have hmajor : (∑n∈S.filter (fun n:ℕ=>(n:ZMod Q)=a),(n:ℝ)⁻¹) ≤
      ∑n∈S,∑j:J,if n∈T j then (n:ℝ)⁻¹ else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro n hn
    by_cases ha : (n:ZMod Q)=a
    · rw [ite_eq_left ha]
      obtain ⟨j,hj⟩ := hcover n hn
      have ht : n∈T j := Finset.mem_filter.mpr ⟨hn,hj.1,hj.2,ha⟩
      have hh := Finset.single_le_sum
        (s:=Finset.univ) (f:=fun j:J=>if n∈T j then (n:ℝ)⁻¹ else 0)
        (fun j _=>by split_ifs <;> positivity) (Finset.mem_univ j)
      simpa only [ite_eq_left ht] using hh
    · rw [ite_eq_right ha]
      exact Finset.sum_nonneg (fun j _=>by split_ifs <;> positivity)
  calc
    _ ≤ ∑n∈S,∑j:J,if n∈T j then (n:ℝ)⁻¹ else 0 := hmajor
    _ = ∑j:J,∑n∈T j,(n:ℝ)⁻¹ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      congr 1
      exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
    _ ≤ ∑_j:J,3/(Q:ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact harmonic_class_le Q (L j) hQ (hL j) (T j) a
        (fun n hn=>(Finset.mem_filter.mp hn).2)
    _ = _ := by simp; ring

end Ostmann.Characters.HarmonicResidueDomination

end

end OAI
