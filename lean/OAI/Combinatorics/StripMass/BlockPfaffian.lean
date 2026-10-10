import Mathlib
import OAI.Combinatorics.StripMass.LaurentBox

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

def blockFirst {m : ℕ} (i : Fin m) : Fin (2*m) := ⟨2*i.val, by omega⟩
def blockSecond {m : ℕ} (i : Fin m) : Fin (2*m) := ⟨2*i.val+1, by omega⟩

theorem blockFirst_injective {m : ℕ} : Function.Injective (@blockFirst m) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [blockFirst] at this
  omega

theorem blockSecond_injective {m : ℕ} : Function.Injective (@blockSecond m) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [blockSecond] at this
  omega

@[simp] theorem blockFirst_ne_second {m : ℕ} (i j : Fin m) : blockFirst i ≠ blockSecond j := by
  intro h
  have := congrArg Fin.val h
  dsimp [blockFirst,blockSecond] at this
  omega

@[simp] theorem blockSecond_ne_first {m : ℕ} (i j : Fin m) : blockSecond i ≠ blockFirst j :=
  (blockFirst_ne_second j i).symm

@[simp] theorem blockFirst_zero (m : ℕ) : blockFirst (0 : Fin (m+1)) = 0 := rfl
@[simp] theorem blockSecond_zero (m : ℕ) : blockSecond (0 : Fin (m+1)) = 1 := rfl

def blockSummand {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*m)) (Fin (2*m)) K) (σ : Equiv.Perm (Fin (2*m))) : K :=
  (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ (blockFirst i)) (σ (blockSecond i))

def blockSwap {m : ℕ} (k : Fin (m+1)) : Equiv.Perm (Fin (2*(m+1))) :=
  Equiv.swap (blockFirst 0) (blockFirst k) * Equiv.swap (blockSecond 0) (blockSecond k)

theorem blockSwap_first {m : ℕ} (k i : Fin (m+1)) :
    blockSwap k (blockFirst i) = blockFirst (Equiv.swap 0 k i) := by
  simp only [blockSwap, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.swap_apply_of_ne_of_ne (blockFirst_ne_second i 0) (blockFirst_ne_second i k)]
  exact (blockFirst_injective.map_swap 0 k i).symm

theorem blockSwap_second {m : ℕ} (k i : Fin (m+1)) :
    blockSwap k (blockSecond i) = blockSecond (Equiv.swap 0 k i) := by
  change Equiv.swap (blockFirst 0) (blockFirst k)
    (Equiv.swap (blockSecond 0) (blockSecond k) (blockSecond i)) = _
  rw [← blockSecond_injective.map_swap 0 k i]
  exact Equiv.swap_apply_of_ne_of_ne (blockSecond_ne_first _ 0) (blockSecond_ne_first _ k)

@[simp] theorem blockSwap_sign {m : ℕ} (k : Fin (m+1)) : Equiv.Perm.sign (blockSwap k) = 1 := by
  by_cases hk : k = 0
  · simp [blockSwap,hk]
  · rw [blockSwap, map_mul,
      Equiv.Perm.sign_swap (blockFirst_injective.ne (Ne.symm hk)),
      Equiv.Perm.sign_swap (blockSecond_injective.ne (Ne.symm hk))]
    simp

theorem blockSummand_swap {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (σ : Equiv.Perm (Fin (2*(m+1)))) (k : Fin (m+1)) :
    blockSummand M (σ*blockSwap k) = blockSummand M σ := by
  simp only [blockSummand, map_mul, blockSwap_sign, mul_one, Equiv.Perm.coe_mul,
    Function.comp_apply, blockSwap_first, blockSwap_second]
  congr 1
  exact Equiv.prod_comp (Equiv.swap 0 k) (fun i => M (σ (blockFirst i)) (σ (blockSecond i)))

def blockFlip (m : ℕ) : Equiv.Perm (Fin (2*(m+1))) := Equiv.swap 0 1

@[simp] theorem blockFlip_first_zero (m : ℕ) : blockFlip m (blockFirst 0) = blockSecond 0 := by
  simp [blockFlip]

@[simp] theorem blockFlip_second_zero (m : ℕ) : blockFlip m (blockSecond 0) = blockFirst 0 := by
  simp [blockFlip]

@[simp] theorem blockFlip_first_succ {m : ℕ} (i : Fin m) :
    blockFlip m (blockFirst i.succ) = blockFirst i.succ := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;>
    have hv := congrArg Fin.val h <;> simp only [blockFirst, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one] at hv <;> omega

@[simp] theorem blockFlip_second_succ {m : ℕ} (i : Fin m) :
    blockFlip m (blockSecond i.succ) = blockSecond i.succ := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;>
    have hv := congrArg Fin.val h <;> simp only [blockSecond, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one] at hv <;> omega

@[simp] theorem blockFlip_sign (m : ℕ) : Equiv.Perm.sign (blockFlip m) = -1 := by
  exact Equiv.Perm.sign_swap (by intro h; have := congrArg Fin.val h; simp at this)

theorem blockSummand_flip {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (σ : Equiv.Perm (Fin (2*(m+1)))) :
    blockSummand M (σ*blockFlip m) = blockSummand M σ := by
  simp only [blockSummand, map_mul, blockFlip_sign, Units.val_mul, Int.cast_mul,
    Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Equiv.Perm.coe_mul,
    Function.comp_apply]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [blockFlip_first_zero, blockFlip_second_zero,
    blockFlip_first_succ, blockFlip_second_succ, hM (σ (blockFirst 0)) (σ (blockSecond 0))]
  ring

 
def blockSection {m : ℕ} (p : Fin (2*(m+1))) : Equiv.Perm (Fin (2*(m+1))) :=
  let k : Fin (m+1) := ⟨p.val/2, by omega⟩
  if p.val%2 = 0 then blockSwap k else blockSwap k * blockFlip m

@[simp] theorem blockSection_zero {m : ℕ} (p : Fin (2*(m+1))) : blockSection p 0 = p := by
  unfold blockSection
  split_ifs with hp
  · rw [← blockFirst_zero m, blockSwap_first, Equiv.swap_apply_left]
    apply Fin.ext
    dsimp [blockFirst]
    omega
  · change blockSwap _ (blockFlip m 0) = p
    rw [← blockFirst_zero m, blockFlip_first_zero, blockSwap_second, Equiv.swap_apply_left]
    apply Fin.ext
    dsimp [blockSecond]
    omega

theorem blockSummand_section {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (σ : Equiv.Perm (Fin (2*(m+1))))
    (p : Fin (2*(m+1))) : blockSummand M (σ*blockSection p) = blockSummand M σ := by
  unfold blockSection
  split_ifs
  · exact blockSummand_swap M σ _
  · rw [← mul_assoc, blockSummand_flip M hM, blockSummand_swap]


 

 


abbrev FixedZero (n : ℕ) := {σ : Equiv.Perm (Fin (n+1)) // σ 0 = 0}

instance (n : ℕ) : Fintype (FixedZero n) := by classical exact Subtype.fintype _

def fixedZeroEquiv (n : ℕ) : FixedZero n ≃ Equiv.Perm (Fin n) where
  toFun σ := (Equiv.Perm.decomposeFin σ.val).2
  invFun σ := ⟨Equiv.Perm.decomposeFin.symm (0,σ), by simp⟩
  left_inv σ := by
    apply Subtype.ext
    have hp : (Equiv.Perm.decomposeFin σ.val).1 = 0 := by
      have h := congrArg (fun e : Equiv.Perm (Fin (n+1)) => e 0)
        (Equiv.Perm.decomposeFin.symm_apply_apply σ.val)
      change Equiv.Perm.decomposeFin.symm ((Equiv.Perm.decomposeFin σ.val).1,
        (Equiv.Perm.decomposeFin σ.val).2) 0 = σ.val 0 at h
      rw [Equiv.Perm.decomposeFin_symm_apply_zero, σ.property] at h
      exact h
    change Equiv.Perm.decomposeFin.symm (0,(Equiv.Perm.decomposeFin σ.val).2) = σ.val
    conv_rhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ.val]
    congr 1
    exact Prod.ext hp.symm rfl
  right_inv σ := by simp

 

def blockPermutationEquiv (m : ℕ) : Equiv.Perm (Fin (2*(m+1))) ≃
    Fin (2*(m+1)) × FixedZero (2*m+1) where
  toFun σ := (σ⁻¹ 0, ⟨σ * blockSection (σ⁻¹ 0), by
    change σ (blockSection (m := m) (σ⁻¹ 0) 0) = 0
    rw [blockSection_zero (m := m)]
    exact σ.apply_symm_apply 0⟩)
  invFun p := p.2.val * (blockSection p.1)⁻¹
  left_inv σ := by simp
  right_inv p := by
    rcases p with ⟨p,ρ⟩
    have hi : ρ.val⁻¹ 0 = 0 := by
      apply ρ.val.injective
      change ρ.val (ρ.val.symm 0) = ρ.val 0
      rw [ρ.val.apply_symm_apply]
      exact ρ.property.symm
    have hp : (ρ.val * (blockSection p)⁻¹)⁻¹ 0 = p := by
      simp only [mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, hi]
      exact blockSection_zero (m := m) p
    apply Prod.ext hp
    apply Subtype.ext
    change (ρ.val * (blockSection p)⁻¹) *
      blockSection ((ρ.val * (blockSection p)⁻¹)⁻¹ 0) = ρ.val
    rw [hp, mul_assoc, inv_mul_cancel, mul_one]

theorem blockSummand_section_inv {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (σ : Equiv.Perm (Fin (2*(m+1))))
    (p : Fin (2*(m+1))) : blockSummand M (σ*(blockSection p)⁻¹) = blockSummand M σ := by
  have h := blockSummand_section M hM (σ*(blockSection p)⁻¹) p
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm

theorem blockSummand_sum_fixedZero {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) :
    ∑ σ, blockSummand M σ = (2*(m+1) : K) *
      ∑ τ : Equiv.Perm (Fin (2*m+1)),
        blockSummand M (Equiv.Perm.decomposeFin.symm (0,τ)) := by
  classical
  rw [← Equiv.sum_comp (blockPermutationEquiv m).symm]
  simp only [Fintype.sum_prod_type, blockPermutationEquiv, Equiv.coe_fn_symm_mk,
    blockSummand_section_inv M hM]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  · norm_cast
  · exact (Equiv.sum_comp (fixedZeroEquiv (2*m+1)).symm
      (fun σ => blockSummand M σ.val)).symm

@[simp] theorem blockFirst_succ {m : ℕ} (i : Fin m) :
    blockFirst i.succ = (blockFirst i).succ.succ := by
  apply Fin.ext
  simp [blockFirst]
  omega

@[simp] theorem blockSecond_succ {m : ℕ} (i : Fin m) :
    blockSecond i.succ = (blockSecond i).succ.succ := by
  apply Fin.ext
  simp [blockSecond]
  omega

 

theorem blockSummand_fixTwo {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (σ : Equiv.Perm (Fin (2*m))) :
    blockSummand M (Equiv.Perm.decomposeFin.symm
      (0,Equiv.Perm.decomposeFin.symm (0,σ))) =
      M 0 1 * blockSummand (fun i j => M i.succ.succ j.succ.succ) σ := by
  change Fin (2*m+2) → Fin (2*m+2) → K at M
  unfold blockSummand
  rw [Fin.prod_univ_succ]
  simp only [blockFirst_zero, blockSecond_zero, blockFirst_succ, blockSecond_succ]
  change ((Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm
      (0, Equiv.Perm.decomposeFin.symm (0, σ))) : ℤ) : K) *
    (M (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ)) 0)
      (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ)) 1) *
      ∏ index : Fin m,
        M (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ))
          (blockFirst index).succ.succ)
          (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ))
            (blockSecond index).succ.succ)) = _
  simp only [Equiv.Perm.decomposeFin.symm_sign, ite_true, one_mul,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, Equiv.swap_self, Equiv.refl_apply,
    Fin.succ_zero_eq_one,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  ring

theorem blockSummand_isolated_zero {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hzero : ∀ j, j ≠ 1 → M 0 j = 0)
    (p : Fin (2*m+1)) (hp : p ≠ 0) (σ : Equiv.Perm (Fin (2*m))) :
    blockSummand M (Equiv.Perm.decomposeFin.symm
      (0,Equiv.Perm.decomposeFin.symm (p,σ))) = 0 := by
  change Fin (2*m+2) → Fin (2*m+2) → K at M
  unfold blockSummand
  rw [Fin.prod_univ_succ]
  simp only [blockFirst_zero, blockSecond_zero]
  change ((Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm
      (0, Equiv.Perm.decomposeFin.symm (p, σ))) : ℤ) : K) *
    (M (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (p, σ)) 0)
      (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (p, σ)) 1) * _) = 0
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, Equiv.swap_self, Equiv.refl_apply]
  rw [hzero p.succ (by
    change p.succ ≠ (0 : Fin (2*m+1)).succ
    exact (Fin.succ_injective (2*m+1)).ne hp),
    zero_mul, mul_zero]

theorem blockSummand_sum_isolated {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (hzero : ∀ j, j ≠ 1 → M 0 j = 0) :
    ∑ σ, blockSummand M σ = (2*(m+1) : K) * M 0 1 *
      ∑ σ, blockSummand (fun i j => M i.succ.succ j.succ.succ) σ := by
  classical
  rw [blockSummand_sum_fixedZero M hM]
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := 2*m)).symm]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single 0]
  · have sum_eq : (∑ σ : Equiv.Perm (Fin (2*m)),
        blockSummand M (Equiv.Perm.decomposeFin.symm
          (0, Equiv.Perm.decomposeFin.symm (0, σ)))) =
        M 0 1 * ∑ σ, blockSummand (fun i j => M i.succ.succ j.succ.succ) σ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      exact blockSummand_fixTwo M σ
    exact (congrArg (fun value : K => (2*(m+1) : K) * value) sum_eq).trans
      (mul_assoc _ _ _).symm
  · intro p _ hp
    exact Finset.sum_eq_zero (fun σ _ => blockSummand_isolated_zero M hzero p hp σ)
  · simp


 

 


 
theorem pfaffian_eq_block {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*m)) (Fin (2*m)) K) :
    pfaffian M = (2^m * (Nat.factorial m : K))⁻¹ * ∑ σ, blockSummand M σ := by
  have hm : 2*m/2 = m := by omega
  unfold pfaffian blockSummand
  congr 1
  · rw [hm]
  · apply Finset.sum_congr rfl
    intro σ _
    congr 1
    let e : Fin (2*m/2) ≃ Fin m := finCongr hm
    apply Fintype.prod_equiv e
    intro i
    congr 2

 

theorem pfaffian_isolated {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (hzero : ∀ j, j ≠ 1 → M 0 j = 0) :
    pfaffian M = M 0 1 * pfaffian (fun i j : Fin (2*m) => M i.succ.succ j.succ.succ) := by
  rw [pfaffian_eq_block M, blockSummand_sum_isolated M hM hzero,
    pfaffian_eq_block (m := m) (fun i j : Fin (2*m) => M i.succ.succ j.succ.succ)]
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hm : (m+1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hf : (Nat.factorial m : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

 

theorem blockSummand_fixZero {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (τ : Equiv.Perm (Fin (2*m+1))) :
    blockSummand M (Equiv.Perm.decomposeFin.symm (0,τ)) =
      (Equiv.Perm.sign τ : ℤ) * M 0 (τ 0).succ *
      ∏ i : Fin m, M (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ := by
  change Fin (2*m+2) → Fin (2*m+2) → K at M
  unfold blockSummand
  rw [Fin.prod_univ_succ]
  simp only [blockFirst_zero, blockSecond_zero, blockFirst_succ, blockSecond_succ]
  change ((Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm (0, τ)) : ℤ) : K) *
    (M (Equiv.Perm.decomposeFin.symm (0, τ) 0)
      (Equiv.Perm.decomposeFin.symm (0, τ) 1) *
      ∏ index : Fin m,
        M (Equiv.Perm.decomposeFin.symm (0, τ) (blockFirst index).succ.succ)
          (Equiv.Perm.decomposeFin.symm (0, τ) (blockSecond index).succ.succ)) = _
  simp only [Equiv.Perm.decomposeFin.symm_sign, ite_true, one_mul,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, Equiv.swap_self, Equiv.refl_apply,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  ring

 

theorem pfaffian_firstRow_add {K : Type*} [Field K] {m : ℕ}
    (M A B : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j)
    (hA : ∀ i j, A j i = -A i j)
    (hB : ∀ i j, B j i = -B i j)
    (hrow : ∀ j, M 0 j = A 0 j + B 0 j)
    (hrestA : ∀ i j : Fin (2*m+1), M i.succ j.succ = A i.succ j.succ)
    (hrestB : ∀ i j : Fin (2*m+1), M i.succ j.succ = B i.succ j.succ) :
    pfaffian M = pfaffian A + pfaffian B := by
  rw [pfaffian_eq_block, pfaffian_eq_block, pfaffian_eq_block,
    blockSummand_sum_fixedZero M hM, blockSummand_sum_fixedZero A hA,
    blockSummand_sum_fixedZero B hB]
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro τ _
  simp only [blockSummand_fixZero, hrow]
  have hprodA : (∏ i : Fin m, M (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ) =
      ∏ i : Fin m, A (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ :=
    Finset.prod_congr rfl (fun _ _ => hrestA _ _)
  have hprodB : (∏ i : Fin m, M (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ) =
      ∏ i : Fin m, B (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ :=
    Finset.prod_congr rfl (fun _ _ => hrestB _ _)
  rw [← hprodA, ← hprodB]
  ring


 

 


 

theorem clearedPfaffianTerm_of_missing_pair {R : Type*} [CommRing R] {m : ℕ}
    (N D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R)
    (hD : D 0 1 = 0) (σ : Equiv.Perm (Fin (2*(m+1))))
    (hσ : firstPair m ∉ selectedPairs σ) : clearedPfaffianTerm N D σ = 0 := by
  unfold clearedPfaffianTerm
  have hz : (∏ e ∈ (selectedPairs σ)ᶜ, D e.val.1 e.val.2) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_compl.mpr hσ)
    exact hD
  rw [hz, mul_zero]

 
theorem isolateFirstNumerator_prod_of_missing_pair {R : Type*} [CommRing R] {m : ℕ}
    (N : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R)
    (σ : Equiv.Perm (Fin (2*(m+1)))) (hσ : firstPair m ∉ selectedPairs σ) :
    (∏ i : Fin (2*(m+1)/2),
      isolateFirstNumerator N (σ (pairFirst _ i)) (σ (pairSecond _ i))) = 0 := by
  obtain ⟨i,hi⟩ := pairIndex_cover (n := 2*(m+1)) (by omega) σ 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hpair : permutationPair σ i ≠ firstPair m := by
    intro he
    apply hσ
    exact he ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  unfold isolateFirstNumerator
  rw [ite_eq_left]
  rcases hi with hi | hi
  · left
    refine ⟨hi,?_⟩
    intro hj
    apply hpair
    unfold permutationPair
    simp only [hi,hj]
    exact (firstPair_eq_upperPair m).symm
  · right
    refine ⟨hi,?_⟩
    intro hj
    apply hpair
    unfold permutationPair upperPair
    have h : ¬ (1 : Fin (2*(m+1))) < 0 := by exact not_lt_of_ge (firstPair m).property.le
    simp only [hi,hj,h,dite_false,firstPair]

 

theorem clearedPfaffian_collision {R : Type*} [CommRing R] {m : ℕ}
    (t : R) (N D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) (hD : D 0 1 = 0) :
    clearedPfaffian t N D =
      clearedPfaffian t (isolateFirstNumerator N) (repairFirstDenominator D) := by
  classical
  unfold clearedPfaffian
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  by_cases hσ : firstPair m ∈ selectedPairs σ
  · unfold clearedPfaffianTerm
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      exact (isolateFirstNumerator_selected N σ hσ i).symm
    · apply Finset.prod_congr rfl
      intro e he
      exact (repairFirstDenominator_compl D σ hσ e he).symm
  · rw [clearedPfaffianTerm_of_missing_pair N D hD σ hσ]
    simp only [clearedPfaffianTerm,
      isolateFirstNumerator_prod_of_missing_pair N σ hσ, zero_mul]

theorem repairFirstDenominator_symm {R : Type*} [One R] {m : ℕ}
    (D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) (hD : ∀ i j, D i j = D j i) :
    ∀ i j, repairFirstDenominator D i j = repairFirstDenominator D j i := by
  intro i j
  unfold repairFirstDenominator
  have h : ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ↔
      ((j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0)) := by tauto
  simp only [h, hD i j]

theorem isolateFirstNumerator_skew {R : Type*} [AddGroup R] {m : ℕ}
    (N : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) (hN : ∀ i j, N j i = -N i j) :
    ∀ i j, isolateFirstNumerator N j i = -isolateFirstNumerator N i j := by
  intro i j
  unfold isolateFirstNumerator
  have h : ((j = 0 ∧ i ≠ 1) ∨ (i = 0 ∧ j ≠ 1)) ↔
      ((i = 0 ∧ j ≠ 1) ∨ (j = 0 ∧ i ≠ 1)) := by tauto
  simp only [h]
  split_ifs
  · exact neg_zero.symm
  · exact hN i j

 

theorem clearedPfaffian_collision_formula {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (N D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hN : ∀ i j, N j i = -N i j) (hD : ∀ i j, D i j = D j i)
    (hzero : D 0 1 = 0)
    (hne : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) → D i j ≠ 0) :
    clearedPfaffian (2^((2*(m+1))/2) * (Nat.factorial ((2*(m+1))/2) : K))⁻¹ N D =
      (∏ e : UpperPair (2*(m+1)), repairFirstDenominator D e.val.1 e.val.2) *
        (N 0 1 * pfaffian (fun i j : Fin (2*m) =>
          N i.succ.succ j.succ.succ / D i.succ.succ j.succ.succ)) := by
  classical
  rw [clearedPfaffian_collision _ N D hzero]
  rw [← clear_pfaffian (isolateFirstNumerator N) (repairFirstDenominator D)
    (repairFirstDenominator_symm D hD) (by
      intro i j hij
      unfold repairFirstDenominator
      split_ifs with h
      · exact one_ne_zero
      · exact hne i j hij h)]
  congr 1
  let M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K := fun i j =>
    isolateFirstNumerator N i j / repairFirstDenominator D i j
  have hM : ∀ i j, M j i = -M i j := by
    intro i j
    dsimp [M]
    rw [isolateFirstNumerator_skew N hN i j,
      repairFirstDenominator_symm D hD j i, neg_div]
  change pfaffian M = _
  rw [pfaffian_isolated M hM (by intro j hj; simp [M,isolateFirstNumerator,hj])]
  have h01 : M 0 1 = N 0 1 := by
    simp [M,isolateFirstNumerator,repairFirstDenominator]
  rw [h01]
  congr 2


 

 


 
def firstPairDecompose (n : ℕ) : UpperPair (n+1) ≃ Fin n ⊕ UpperPair n where
  toFun e := if hi : e.val.1 = 0 then
      Sum.inl (e.val.2.pred (ne_of_gt (hi ▸ e.property)))
    else
      let hj : e.val.2 ≠ 0 := by
        intro hj; have := e.property; simp [hj] at this
      Sum.inr ⟨(e.val.1.pred hi,e.val.2.pred hj),
        (Fin.pred_lt_pred_iff (ha := hi) (hb := hj)).mpr e.property⟩
  invFun e := match e with
    | Sum.inl j => ⟨(0,j.succ),Fin.succ_pos _⟩
    | Sum.inr e => ⟨(e.val.1.succ,e.val.2.succ), Fin.succ_lt_succ_iff.mpr e.property⟩
  left_inv e := by
    dsimp
    split_ifs with hi
    · apply Subtype.ext
      apply Prod.ext hi.symm
      simp only [Fin.succ_pred]
    · apply Subtype.ext
      apply Prod.ext <;> simp only [Fin.succ_pred]
  right_inv e := by
    cases e with
    | inl j => simp
    | inr e => simp

 
theorem prod_upperPair_succ {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin (n+1) → Fin (n+1) → R) :
    (∏ e : UpperPair (n+1), D e.val.1 e.val.2) =
      (∏ j : Fin n, D 0 j.succ) *
        ∏ e : UpperPair n, D e.val.1.succ e.val.2.succ := by
  calc
    _ = ∏ e : Fin n ⊕ UpperPair n,
        D ((firstPairDecompose n).symm e).val.1 ((firstPairDecompose n).symm e).val.2 :=
      (Fintype.prod_equiv (firstPairDecompose n).symm _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

theorem prod_upperPair_two {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin (n+2) → Fin (n+2) → R) :
    (∏ e : UpperPair (n+2), D e.val.1 e.val.2) =
      D 0 1 * (∏ j : Fin n, D 0 j.succ.succ * D 1 j.succ.succ) *
        ∏ e : UpperPair n, D e.val.1.succ.succ e.val.2.succ.succ := by
  rw [prod_upperPair_succ D, Fin.prod_univ_succ,
    prod_upperPair_succ (fun i j : Fin (n+1) => D i.succ j.succ),
    Finset.prod_mul_distrib]
  simp only [Fin.succ_zero_eq_one]
  ac_rfl


 

 


theorem pfaffian_cast {K : Type*} [Field K] {n m : ℕ} (h : n = m)
    (M : Matrix (Fin n) (Fin n) K) :
    pfaffian (fun i j : Fin m => M (i.cast h.symm) (j.cast h.symm)) = pfaffian M := by
  subst m
  rfl

theorem clearedPfaffian_cast {R : Type*} [CommRing R] {n m : ℕ} (h : n = m)
    (t : R) (N D : Matrix (Fin n) (Fin n) R) :
    clearedPfaffian t (fun i j : Fin m => N (i.cast h.symm) (j.cast h.symm))
      (fun i j : Fin m => D (i.cast h.symm) (j.cast h.symm)) = clearedPfaffian t N D := by
  subst m
  rfl

 

theorem clearedPfaffian_delete_even {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : n % 2 = 0) (N D : Matrix (Fin (n+2)) (Fin (n+2)) K)
    (hN : ∀ i j, N j i = -N i j) (hD : ∀ i j, D i j = D j i)
    (hzero : D 0 1 = 0)
    (hne : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) → D i j ≠ 0) :
    clearedPfaffian (2^((n+2)/2) * (Nat.factorial ((n+2)/2) : K))⁻¹ N D =
      N 0 1 * (∏ j : Fin n, D 0 j.succ.succ * D 1 j.succ.succ) *
        ((∏ e : UpperPair n, D e.val.1.succ.succ e.val.2.succ.succ) *
          pfaffian (fun i j : Fin n => N i.succ.succ j.succ.succ / D i.succ.succ j.succ.succ)) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = 2*m := ⟨n/2,by omega⟩
  apply Eq.trans (clearedPfaffian_collision_formula N D hN hD hzero hne)
  apply Eq.trans (congrArg (fun z => z *
    (N 0 1 * pfaffian (fun i j : Fin (2*m) =>
      N i.succ.succ j.succ.succ / D i.succ.succ j.succ.succ)))
        (prod_upperPair_two (n := 2*m) (repairFirstDenominator D)))
  have hs : ∀ i : Fin (2*m), i.succ.succ ≠ (1 : Fin (2*m+2)) := by
    intro i h
    have := congrArg Fin.val h
    simp at this
  simp only [repairFirstDenominator, Fin.succ_ne_zero, hs,
    and_false, or_false, ite_false,
    and_self, true_or, ite_true, one_mul]
  ac_rfl

end
end CriticalStrip.Diagram

end OAI
