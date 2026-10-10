import Mathlib
import OAI.Probability.BinarySweep.Processes.Basic

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

theorem supportTimeBound_bounds (d : ℕ) :
    (2 : ℝ) * (d + 1) - 6 ≤ supportTimeBound d ∧
    supportTimeBound d ≤ (2 : ℝ) * (d + 1) := by
  let N : ℕ := 2 ^ (d + 1)
  have hN : (2 : ℝ) ≤ N := by
    dsimp [N]
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    have : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    linarith
  have hNp : (0 : ℝ) < N := by linarith
  have hNne : N ≠ 0 := by exact_mod_cast hNp.ne'
  have hfac : (0 : ℝ) < N.factorial := by positivity
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at this ⊢
    exact this
  have hlogN : Real.log (N : ℝ) = ((d : ℝ) + 1) * Real.log 2 := by
    simp [N, Real.log_pow]
  have hlogNN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hst := Stirling.le_log_factorial_stirling hNne
  have hfaclow : (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    linarith
  have hfacup : Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
    have h := Real.log_le_log hfac (show (N.factorial : ℝ) ≤ (N : ℝ) ^ N by
      exact_mod_cast Nat.factorial_le_pow N)
    rwa [Real.log_pow] at h
  have hconstlow : -(1 : ℝ) ≤ Real.log (3 / 4 : ℝ) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (3 / 4 : ℝ)) (by norm_num)
    norm_num at this
    linarith
  have hconstup : Real.log (3 / 4 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hL : Real.log (3 * (N.factorial : ℝ) / 4) =
      Real.log (N.factorial : ℝ) + Real.log (3 / 4 : ℝ) := by
    rw [show 3 * (N.factorial : ℝ) / 4 = (N.factorial : ℝ) * (3 / 4) by ring]
    exact Real.log_mul hfac.ne' (by norm_num)
  have hlow : (N : ℝ) * (((d : ℝ) + 1) * Real.log 2) - N - 1 ≤
      Real.log (3 * (N.factorial : ℝ) / 4) := by
    rw [hL]
    rw [hlogN] at hfaclow
    linarith
  have hup : Real.log (3 * (N.factorial : ℝ) / 4) ≤
      (N : ℝ) * (((d : ℝ) + 1) * Real.log 2) := by
    rw [hL]
    rw [hlogN] at hfacup
    linarith
  have hrewrite : supportTimeBound d =
      2 * Real.log (3 * (N.factorial : ℝ) / 4) / ((N : ℝ) * Real.log 2) := by
    simp only [supportTimeBound, Real.logb]
    have hcast : (N : ℝ) = (2 : ℝ) ^ (d + 1) := by simp [N]
    rw [← hcast]
    ring
  rw [hrewrite]
  constructor
  · apply (le_div_iff₀ (mul_pos hNp hlog)).mpr
    have hprod : (N : ℝ) / 2 ≤ (N : ℝ) * Real.log 2 := by
      nlinarith [mul_nonneg hNp.le (sub_nonneg.mpr hhalf)]
    nlinarith
  · apply (div_le_iff₀ (mul_pos hNp hlog)).mpr
    nlinarith

theorem support_ceiling_asymptotic (d : ℕ) :
    |(⌈supportTimeBound d⌉ : ℝ) - 2 * (d + 1)| ≤ 6 := by
  obtain ⟨hlow, hupp⟩ := supportTimeBound_bounds d
  have hceilow := Int.le_ceil (supportTimeBound d)
  have hup : ⌈supportTimeBound d⌉ ≤ (2 * (d + 1) : ℤ) := by
    apply Int.ceil_le.mpr
    push_cast
    exact hupp
  have hupR : (⌈supportTimeBound d⌉ : ℝ) ≤ 2 * ((d : ℝ) + 1) := by
    exact_mod_cast hup
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def boolSwitch (c : Bool) : Equiv.Perm Bool where
  toFun x := x ^^ c
  invFun x := x ^^ c
  left_inv x := by simp
  right_inv x := by simp

lemma sign_boolSwitch (c : Bool) :
    Equiv.Perm.sign (boolSwitch c) = if c then (-1 : ℤˣ) else 1 := by
  cases c
  · have : boolSwitch false = 1 := by ext x; cases x <;> rfl
    rw [this]; rfl
  · have : boolSwitch true = Equiv.swap false true := by
      ext x; cases x <;> simp [boolSwitch]
    rw [this, Equiv.Perm.sign_swap (by decide)]; rfl

lemma realSign_coordinateLayer (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    realSign (coordinateLayer d j c) = ∏ y, (if c y then (-1 : ℝ) else 1) := by
  classical
  have he : coordinateLayer d j c =
      (Equiv.piSplitAt j (fun _ : Fin d => Bool)).trans
        ((Equiv.prodCongrLeft (fun y => boolSwitch (c y))).trans
          (Equiv.piSplitAt j (fun _ : Fin d => Bool)).symm) := rfl
  rw [he]
  simp [realSign, Equiv.Perm.sign_prodCongrLeft, sign_boolSwitch, apply_ite]

lemma sum_realSign_coordinateLayer (d : ℕ) (j : Fin d) :
    ∑ c : ({i : Fin d // i ≠ j} → Bool) → Bool,
      realSign (coordinateLayer d j c) = 0 := by
  classical
  simp_rw [realSign_coordinateLayer]
  rw [← Fintype.prod_sum (fun (_ : {i : Fin d // i ≠ j} → Bool) (b : Bool) =>
    if b then (-1 : ℝ) else 1)]
  simp

lemma realSign_binarySweep (d : ℕ) (c : SweepCoins d) :
    realSign (binarySweep d c) = ∏ j, realSign (coordinateLayer d j (c j)) := by
  classical
  simp [binarySweep, map_list_prod, List.map_reverse, List.prod_reverse,
    List.map_ofFn, List.prod_ofFn]

lemma sum_realSign_binarySweep (d : ℕ) (hd : 0 < d) :
    ∑ c : SweepCoins d, realSign (binarySweep d c) = 0 := by
  classical
  simp_rw [realSign_binarySweep]
  rw [← Fintype.prod_sum (fun (j : Fin d) (c : ({i : Fin d // i ≠ j} → Bool) → Bool) =>
    realSign (coordinateLayer d j c))]
  apply Finset.prod_eq_zero (i := ⟨0, hd⟩) (Finset.mem_univ _)
  exact sum_realSign_coordinateLayer d ⟨0, hd⟩

lemma finiteLaw_expectation {Ω G : Type*} [Fintype Ω] [Fintype G]
    (f : Ω → G) (a : G → ℝ) :
    ∑ g, finiteLaw f g * a g = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, a (f ω) := by
  classical
  simp only [finiteLaw, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul, Finset.mul_sum]

theorem binary_sign_annihilated (d : ℕ) (hd : 0 < d) :
    ∑ g : Equiv.Perm (Slot d), binaryLaw d g * realSign g = 0 := by
  rw [binaryLaw, finiteLaw_expectation, sum_realSign_binarySweep d hd, mul_zero]

lemma coordinateLayer_zero (d : ℕ) (j : Fin d) :
    coordinateLayer d j (fun _ => false) = 1 := by
  ext x i
  simp [coordinateLayer, Equiv.piSplitAt_symm_apply]
  intro h
  rw [h]

lemma prod_reverse_ofFn_single {G : Type*} [Monoid G] (n : ℕ) (j : Fin n) (g : G) :
    (List.ofFn (fun i : Fin n => if i = j then g else 1)).reverse.prod = g := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [List.ofFn_succ, List.ofFn_const]
    · simpa [List.ofFn_succ, (Fin.succ_ne_zero j).symm] using ih j

lemma binarySweep_zero (d : ℕ) : binarySweep d (fun _ _ => false) = 1 := by
  simp [binarySweep, coordinateLayer_zero, List.ofFn_const]

lemma binarySweep_singleLayer (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    binarySweep d (Function.update ((fun _ _ => false) : SweepCoins d) j c) = coordinateLayer d j c := by
  classical
  have h (i : Fin d) :
      coordinateLayer d i ((Function.update ((fun _ _ => false) : SweepCoins d) j c) i) =
      if i = j then coordinateLayer d j c else 1 := by
    by_cases hi : i = j
    · subst i; simp
    · simp [coordinateLayer_zero, hi]
  simp only [binarySweep, h]
  exact prod_reverse_ofFn_single d j _

def sweepReachable (d : ℕ) : Submonoid (Equiv.Perm (Slot d)) where
  carrier := {g | ∃ l : List (SweepCoins d), (l.map (binarySweep d)).prod = g}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro g h ⟨l, rfl⟩ ⟨k, rfl⟩
    exact ⟨l ++ k, by simp⟩

lemma coordinateLayer_mem_reachable (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    coordinateLayer d j c ∈ sweepReachable d := by
  refine ⟨[Function.update ((fun _ _ => false) : SweepCoins d) j c], ?_⟩
  simp [binarySweep_singleLayer]

lemma fiber_boolSwitch_eq_swap {Y : Type*} [DecidableEq Y] (y : Y) (a : Bool) :
    Equiv.prodCongrLeft (fun z => boolSwitch (decide (z = y))) =
      Equiv.swap (a, y) (!a, y) := by
  ext ⟨b, z⟩ <;> cases a <;> cases b <;> by_cases h : z = y <;>
    simp [boolSwitch, Equiv.swap_apply_def, h]

end BinaryCoordinateSweeps
end

end OAI
