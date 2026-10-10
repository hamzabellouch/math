import OAI.NumberTheory.DirichletL.Moments.HeckeExpansion
import OAI.NumberTheory.DirichletL.Moments.MobiusRegroup

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorAllocation
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def nonemptySelections (s : Finset ι) : Finset (Finset ι) := s.powerset.erase ∅

omit [DecidableEq ι] in
theorem prime_complement (P : Ideal O) (hP : Prime P) (s : Finset ι) (v : ι → Ideal O) :
    (∏ i ∈ s, (1-(if P ∣ v i then (1:ℂ) else 0))) =
      if P ∣ ∏ i ∈ s,v i then 0 else 1 := by
  by_cases h : P ∣ ∏ i ∈ s,v i
  · rw [ite_eq_left h]
    obtain ⟨i,hi,hd⟩ := (hP.dvd_finsetProd_iff v).mp h
    exact Finset.prod_eq_zero hi (by simp only [ite_eq_left hd,sub_self])
  · rw [ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    have hd : ¬P∣v i := fun hh => h ((hP.dvd_finsetProd_iff v).mpr ⟨i,hi,hh⟩)
    simp only [ite_eq_right hd,sub_zero]

theorem prime_factor_allocation (P : Ideal O) (hP : Prime P)
    (s : Finset ι) (v : ι → Ideal O) :
    (if P ∣ ∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
        ∏ i ∈ J, if P ∣ v i then (1:ℂ) else 0 := by
  let f := fun J : Finset ι => (-1:ℂ)^J.card*∏ i ∈ J,if P∣v i then (1:ℂ) else 0
  have he : (∑ J ∈ nonemptySelections s,f J)+1 =
      if P ∣ ∏ i ∈ s,v i then (0:ℂ) else 1 := by
    have hr := Finset.sum_erase_add s.powerset f (Finset.mem_powerset.mpr (Finset.empty_subset s))
    have hh := Finset.prod_sub (fun _i : ι => (1:ℂ))
      (fun i => if P∣v i then (1:ℂ) else 0) s
    simp only [Finset.prod_const_one,mul_one] at hh
    rw [prime_complement P hP s v] at hh
    simpa only [nonemptySelections,f,Finset.card_empty,pow_zero,Finset.prod_empty,one_mul] using hr.trans hh.symm
  have hn : (∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
      ∏ i ∈ J,if P∣v i then (1:ℂ) else 0) = -(∑ J ∈ nonemptySelections s,f J) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f]
    rw [pow_succ]
    ring
  rw [hn]
  by_cases h : P∣∏ i ∈ s,v i <;> simp only [h,ite_true,ite_false] at he ⊢ <;>
    linear_combination he

theorem squarefree_dvd_iff (D I : Ideal O) (hD : Squarefree D) :
    D∣I ↔ ∀ P ∈ primeSupport D,P∣I := by
  constructor
  · intro hd P hP
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)).trans hd
  · intro h
    rw [← squarefree_support_product_self hD]
    apply Finset.prod_dvd_of_coprime ?_ h
    intro P hP Q hQ hne
    let : P.IsMaximal := (Ideal.isPrime_of_prime (support_prime hP)).isMaximal (support_prime hP).ne_zero
    let : Q.IsMaximal := (Ideal.isPrime_of_prime (support_prime hQ)).isMaximal (support_prime hQ).ne_zero
    exact Ideal.isCoprime_of_isMaximal hne

abbrev Allocation (D : Ideal O) (s : Finset ι) :=
  (P : primeSupport D) → nonemptySelections s

def allocationTerm (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)*
    ∏ i ∈ (a P).val, if (P:Ideal O)∣v i then (1:ℂ) else 0

theorem squarefree_mask_allocation (D : Ideal O) (hD : Squarefree D)
    (s : Finset ι) (v : ι → Ideal O) :
    (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ a : Allocation D s, allocationTerm D s v a := by
  have hprod : (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∏ P : primeSupport D, if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0 := by
    by_cases hd : D∣∏ i ∈ s,v i
    · rw [ite_eq_left hd]
      symm
      apply Finset.prod_eq_one
      intro P hP
      rw [ite_eq_left ((squarefree_dvd_iff _ _ hD).mp hd P P.property)]
    · rw [ite_eq_right hd]
      obtain ⟨P,hP,hnd⟩ := not_forall.mp (fun h => hd ((squarefree_dvd_iff _ _ hD).mpr h))
        |> fun h => by simpa only [not_forall,not_imp] using h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨P,hP⟩ : primeSupport D)) (by simp only [ite_eq_right hnd])
  rw [hprod]
  have hl (P : primeSupport D) :
      (if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J : nonemptySelections s, (-1:ℂ)^(J.val.card+1)*
        ∏ i ∈ J.val, if (P:Ideal O)∣v i then (1:ℂ) else 0 := by
    rw [prime_factor_allocation P (support_prime P.property) s v]
    exact (Finset.sum_coe_sort (nonemptySelections s) (fun J =>
      (-1:ℂ)^(J.card+1)*∏ i ∈ J,if (P:Ideal O)∣v i then (1:ℂ) else 0)).symm
  simp_rw [hl]
  exact Fintype.prod_sum _

theorem allocationTerm_norm_le_one (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ‖allocationTerm D s v a‖ ≤ 1 := by
  unfold allocationTerm
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro P hP
  rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i hi
  split_ifs <;> norm_num

theorem allocation_card_bound (D : Ideal O) (s : Finset ι) :
    Fintype.card (Allocation D s) ≤ (2^(primeSupport D).card)^s.card := by
  have hc : (nonemptySelections s).card ≤ 2^s.card := by
    simpa only [nonemptySelections,Finset.card_powerset] using
      (Finset.card_erase_le (s := s.powerset) (a := (∅:Finset ι)))
  change Fintype.card (primeSupport D → nonemptySelections s) ≤ _
  simp only [Fintype.card_fun,Fintype.card_coe]
  calc
    _ ≤ (2^s.card)^(primeSupport D).card := Nat.pow_le_pow_left hc _
    _ = _ := by simp only [← pow_mul,Nat.mul_comm]

theorem allocation_mass_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      ∀ v : ι → Ideal O, (∑ a : Allocation D s, ‖allocationTerm D s v a‖) ≤
        C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C^N,pow_pos hC _,?_⟩
  intro D hD s hs v
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ∑ _a : Allocation D s,(1:ℝ) := Finset.sum_le_sum (fun a _ => allocationTerm_norm_le_one D s v a)
    _ = (Fintype.card (Allocation D s):ℝ) := by simp
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

end SevenEighths.CenteredMomentDivisorAllocation

end

end OAI
