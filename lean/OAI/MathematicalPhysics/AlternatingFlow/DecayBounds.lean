import OAI.MathematicalPhysics.AlternatingFlow.InitialNames

namespace OAI

section DecayBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding
open Bounds (readScale readScale_nonneg potential_decomposition norm_iterated_curl amplitude norm_comp_linear)

lemma potential_bound : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (fun x => Spatial.cutoff x *
      Spatial.shearPotential (Construction.donorIndex n) (Construction.receiverIndex n) 0
        (LocalRule.write M N n) (LocalRule.signal M N n) x) x‖ ≤
        (C ((M,N),r) : ℝ) * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ r) := by
  obtain ⟨sA, A, cA, ha⟩ := fixedPotential_scaled
  obtain ⟨sB, B, cB, hb⟩ := corePotential_scaled
  refine ⟨fun z => A ((), z.2) + B z,
    Primrec.nat_add.to_comp.comp
      (cA.comp ((Computable.const ()).pair Computable.snd)) cB, fun M N r n x => ?_⟩
  have hA : 0 ≤ (A ((),r) : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ (B ((M,N),r) : ℝ) := Nat.cast_nonneg _
  simp only [Nat.cast_add]
  have hε : 0 ≤ Scales.ε M.base N (n + 1) := Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)
  have hε' : Scales.ε M.base N (n + 1) ≤ Scales.ε M.base N n :=
    (Scales.ε_strictAnti M.base N (by have := M.base_ge_four; omega)).antitone (by omega)
  have h₁ := sA () n
  have h₂ := sB (M,N) n
  simp_rw [potential_decomposition]
  change ‖iteratedFDeriv ℝ r (fun x =>
    (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • Bounds.fixedPotential n x +
      Scales.ε M.base N (n + 1) • Bounds.corePotential M N n x) x‖ ≤ _
  have hs₁ : ContDiff ℝ ∞ (fun x =>
      (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • Bounds.fixedPotential n x) := h₁.const_smul _
  have hs₂ : ContDiff ℝ ∞ (fun x =>
      Scales.ε M.base N (n + 1) • Bounds.corePotential M N n x) := h₂.const_smul _
  rw [fun_iteratedFDeriv_add_apply
    (hs₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hs₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  apply (norm_add_le _ _).trans
  rw [iteratedFDeriv_const_smul_apply' (h₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    iteratedFDeriv_const_smul_apply' (h₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hε'), abs_of_nonneg hε]
  have haa : ‖iteratedFDeriv ℝ r (Bounds.fixedPotential n) x‖ ≤ (A ((),r) : ℝ) := by simpa using ha () r n x
  have hbb := hb (M,N) r n x
  have hscale := pow_nonneg (readScale_nonneg M N n) r
  calc
    _ ≤ Scales.ε M.base N n * (A ((),r) : ℝ) +
      Scales.ε M.base N (n + 1) * ((B ((M,N),r) : ℝ) * readScale M N n ^ r) := by
      exact add_le_add
        (mul_le_mul (by linarith) haa (norm_nonneg _) (by linarith))
        (mul_le_mul_of_nonneg_left hbb hε)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ Scales.ε M.base N n by linarith) hB,
      mul_nonneg hA (mul_nonneg hε hscale)]

lemma slot_estimate : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤
      (C ((M,N),r) : ℝ) * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1)) := by
  obtain ⟨C, hC, hc⟩ := potential_bound
  refine ⟨fun z => 2 * C (z.1,z.2+1),
    Primrec.nat_mul.to_comp.comp (Computable.const 2)
      (hC.comp (Computable.fst.pair (Computable.succ.comp Computable.snd))), fun M N r n x => ?_⟩
  have h := norm_iterated_curl (Construction.receiverIndex n) 0 _
    (Spatial.cutoff_smooth.mul (Spatial.shearPotential_smooth (Construction.donorIndex n)
      (Construction.receiverIndex n) 0 _ _
      (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n))) r x
  apply h.trans
  push_cast
  nlinarith [hc M N (r+1) n x]

def readCost (z : (Machine × ℕ) × ℕ) : ℕ :=
  1 + ∑ n ∈ Finset.range z.2, z.1.1.base ^
    (Scales.s z.1.2 n + (z.2+1) * (Scales.s z.1.2 n + 1 + Scales.K z.1.2 n))

lemma readCost_computable : Computable readCost := by
  have hM : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => z.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hN : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => z.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hs : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => Scales.s z.1.1.2 z.2) := exponent.to_comp.comp hN Computable.snd
  have hK : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => Scales.K z.1.1.2 z.2) := capacity.to_comp.comp hN Computable.snd
  have hp : Computable₂ (fun z : (Machine × ℕ) × ℕ => fun n : ℕ => z.1.1.base ^ (Scales.s z.1.2 n + (z.2+1) * (Scales.s z.1.2 n + 1 + Scales.K z.1.2 n))) := nat_pow.to_comp.comp (base.to_comp.comp hM)
    (Primrec.nat_add.to_comp.comp hs (Primrec.nat_mul.to_comp.comp
      (Computable.succ.comp (Computable.snd.comp Computable.fst))
      (Primrec.nat_add.to_comp.comp (Computable.succ.comp hs) hK)))
  unfold readCost
  exact Primrec.nat_add.to_comp.comp (Computable.const 1)
    ((nat_sum_range hp).comp Computable.id Computable.snd)

lemma uniform_read_cost (M : Machine) (N r n : ℕ) :
    Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1) ≤
      (readCost ((M,N),r) : ℝ) * Scales.ε M.base N n := by
  have hb : (1 : ℝ) ≤ M.base := by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base)
  have hε (n : ℕ) : 0 < Scales.ε M.base N n :=
    Scales.ε_pos _ _ _ (by have := M.base_ge_four; omega)
  have hD : (1 : ℝ) ≤ readCost ((M,N),r) := by
    dsimp [readCost]; push_cast
    exact le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have he : readScale M N n ^ (r + 1) =
      (M.base : ℝ) ^ ((r+1) * (Scales.s N n + 1 + Scales.K N n)) := by
    rw [readScale, ← pow_mul, Nat.mul_comm]
  by_cases hn : n < r
  · have hle : M.base ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)) ≤ readCost ((M,N),r) :=
      (Finset.single_le_sum (f := fun n => M.base ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)).trans (Nat.le_add_left _ _)
    have hpow : ((M.base : ℝ) ^ Scales.s N n) ≠ 0 := ne_of_gt (pow_pos (zero_lt_one.trans_le hb) _)
    calc
      _ ≤ readScale M N n ^ (r+1) := by
        apply mul_le_of_le_one_left (pow_nonneg (readScale_nonneg M N n) _)
        simpa [Scales.ε, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hb) _))] using
          Bounds.inverse_power_bound M (Scales.s N (n+1))
      _ = (M.base : ℝ) ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)) * Scales.ε M.base N n := by
        rw [he, pow_add, Scales.ε]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (hε n).le
  · rw [he]
    exact (Scales.derivative_cost_bound M.base N r n (by have := M.base_ge_four; omega)
      (by omega)).trans (le_mul_of_one_le_left (hε n).le hD)

lemma slot_decay : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤ (C ((M,N),r) : ℝ) * Scales.ε M.base N n := by
  obtain ⟨C,hC,hc⟩ := slot_estimate
  refine ⟨fun z => C z * (1 + readCost z), Primrec.nat_mul.to_comp.comp hC
    (Primrec.nat_add.to_comp.comp (Computable.const 1) readCost_computable), fun M N r n x => ?_⟩
  apply (hc M N r n x).trans
  push_cast
  have h := mul_le_mul_of_nonneg_left (uniform_read_cost M N r n) (Nat.cast_nonneg (C ((M,N),r)) : (0 : ℝ) ≤ _)
  nlinarith

lemma loading_bound : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r x,
    ‖iteratedFDeriv ℝ r (Construction.loading M w) x‖ ≤ C ((M,w),r) := by
  obtain ⟨hs,C,hC,hc⟩ := loadingPotential_scaled
  refine ⟨fun z => 2 * C (z.1,z.2+1), Primrec.nat_mul.to_comp.comp (Computable.const 2)
    (hC.comp (Computable.fst.pair (Computable.succ.comp Computable.snd))), fun M w r x => ?_⟩
  apply (norm_iterated_curl 1 0 _ (hs (M,w) 0) r x).trans
  have h := hc (M,w) (r+1) 0 x
  simp only [one_pow, mul_one] at h
  push_cast
  linarith

lemma piece_decay : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r n x,
    ‖iteratedFDeriv ℝ r (Construction.piece M w n) x‖ ≤ (C ((M,w),r) : ℝ) * amplitude M w.length n := by
  obtain ⟨A,hA,ha⟩ := loading_bound
  obtain ⟨B,hB,hb⟩ := slot_decay
  refine ⟨fun z => A z + B ((z.1.1,z.1.2.length),z.2), Primrec.nat_add.to_comp.comp hA
    (hB.comp (((Computable.fst.comp Computable.fst).pair
      (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.fst))).pair Computable.snd)), fun M w r n x => ?_⟩
  cases n with
  | zero =>
    simp only [Construction.piece, amplitude, mul_one, Nat.cast_add]
    exact (ha M w r x).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  | succ n =>
    simp only [Construction.piece, amplitude, Nat.cast_add]
    exact (hb M w.length r n x).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (Nat.cast_nonneg _)) (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)))

lemma pulse_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ _ => Profiles.pulse) := by
  have hclock := transition_scaled.affine (fun _ _ => zero_le_one) (fun _ _ => 2)
    (fun _ _ => -1/2) (fun _ => 2) (Computable.const 2) (by intros; norm_num)
  have he : (fun t => Real.smoothTransition (2 * t + -1/2)) = Profiles.clock := by
    funext t; unfold Profiles.clock; congr 1; ring
  obtain ⟨hs,C,hC,hc⟩ := hclock
  refine ⟨fun _ _ => Profiles.pulse_smooth, fun z => C ((),z.2+1),
    hC.comp ((Computable.const ()).pair (Computable.succ.comp Computable.snd)), fun a r n x => ?_⟩
  rw [he] at hc
  change ‖iteratedFDeriv ℝ r (deriv Profiles.clock) x‖ ≤ _
  simpa [one_pow, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ'] using hc () (r+1) 0 x

lemma pulsePiece_decay : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r n z,
    ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ ≤ (C ((M,w),r) : ℝ) * amplitude M w.length n := by
  obtain ⟨_,A,hA,ha⟩ := pulse_scaled
  obtain ⟨B,hB,hb⟩ := piece_decay
  let C := fun z : (Machine × List ℕ) × ℕ => ∑ i ∈ Finset.range (z.2+1), z.2.choose i * A ((),i) * B (z.1,z.2-i)
  have hi : Computable₂ (fun z : (Machine × List ℕ) × ℕ => fun i : ℕ => z.2.choose i * A ((),i) * B (z.1,z.2-i)) :=
    Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
      (hA.comp ((Computable.const ()).pair Computable.snd)))
      (hB.comp ((Computable.fst.comp Computable.fst).pair
        (Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  refine ⟨C, (nat_sum_range hi).comp Computable.id (Computable.succ.comp Computable.snd), fun M w r n z => ?_⟩
  have hp (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Profiles.pulse (z.1 - n)) z‖ ≤ (A ((),i) : ℝ) := by
    apply (norm_comp_linear (fun t => Profiles.pulse (t - n))
      (Profiles.pulse_smooth.comp (contDiff_id.sub contDiff_const)) (ContinuousLinearMap.fst ℝ ℝ Space)
      i z).trans
    rw [iteratedFDeriv_comp_sub]
    have h₁ : ‖iteratedFDeriv ℝ i Profiles.pulse (z.1 - n)‖ ≤ (A ((),i) : ℝ) := by simpa using ha () i 0 (z.1 - n)
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg (A ((),i)))
  have hw (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Construction.piece M w n z.2) z‖ ≤
        (B ((M,w),i) : ℝ) * amplitude M w.length n := by
    apply (norm_comp_linear (Construction.piece M w n) (Construction.piece_smooth M w n)
      (ContinuousLinearMap.snd ℝ ℝ Space) i z).trans
    have h₁ := hb M w i n z.2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (Nat.cast_nonneg (B ((M,w),i))) (Bounds.amplitude_nonneg M w.length n))
  apply (norm_iteratedFDeriv_smul_le
    (Profiles.pulse_smooth.comp (contDiff_fst.sub contDiff_const))
    ((Construction.piece_smooth M w n).comp contDiff_snd) z (WithTop.coe_le_coe.mpr le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * (A ((),i) : ℝ) * ((B ((M,w),r-i) : ℝ) * amplitude M w.length n) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul _ (hw (r - i)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg (A ((),i))))
      exact mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg _)
    _ = (C ((M,w),r) : ℝ) * amplitude M w.length n := by
      simp only [C, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_assoc]

lemma epsilon_small (M : Machine) (N n : ℕ) : Scales.ε M.base N n ≤ (1/8:ℝ)^n := by
  have hb : (2 : ℝ) ≤ M.base := by exact_mod_cast (le_trans (by decide : 2 ≤ 4) M.base_ge_four)
  have hs : 3*n ≤ Scales.s N n := by have := Scales.s_lower N n; nlinarith
  unfold Scales.ε
  have hp : (8:ℝ)^n ≤ (M.base:ℝ)^Scales.s N n := by
    calc
      _ = (2:ℝ)^(3*n) := by rw [pow_mul]; norm_num
      _ ≤ (2:ℝ)^Scales.s N n := pow_le_pow_right₀ (by norm_num) hs
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hb _
  simpa only [one_div, inv_pow] using inv_anti₀ (by positivity : (0:ℝ) < 8^n) hp

lemma weighted_epsilon (M : Machine) (N J n : ℕ) :
    (1+(n:ℝ))^J * Scales.ε M.base N n ≤ 4 * J.factorial * (1/2:ℝ)^n := by
  have hpoly : (1+(n:ℝ))^J ≤ (J.factorial:ℝ) * (4 * 4^n) := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < J.factorial)).mp
      (Real.pow_div_factorial_le_exp (1+(n:ℝ)) (by positivity) J)
    have he : Real.exp (1+(n:ℝ)) ≤ 4 * 4^n := by
      rw [Real.exp_add, show (n:ℝ) = n*1 by ring, Real.exp_nat_mul]
      exact mul_le_mul (Real.exp_one_lt_three.le.trans (by norm_num))
        (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_three.le.trans (by norm_num)) n)
        (by positivity) (by norm_num)
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg J.factorial : (0:ℝ) ≤ _)])
  calc
    _ ≤ ((J.factorial:ℝ) * (4 * 4^n)) * (1/8:ℝ)^n :=
      mul_le_mul hpoly (epsilon_small M N n) (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)) (by positivity)
    _ = _ := by rw [mul_assoc _ (4*4^n), mul_assoc 4, ← mul_pow]; norm_num; ring

lemma weighted_amplitude_sum (M : Machine) (N J : ℕ) :
    (∑' n : ℕ, (1+(n:ℝ))^J * amplitude M N n) ≤ (1 + 8 * 2^J * J.factorial : ℕ) := by
  have hs := Bounds.weighted_amplitude_summable M N J
  rw [hs.tsum_eq_zero_add]
  simp only [amplitude, Nat.cast_zero, add_zero, one_pow, mul_one]
  have hc : ∀ n : ℕ, (1+(n+1:ℕ))^J * amplitude M N (n+1) ≤
      (2:ℝ)^J * (4 * J.factorial * (1/2:ℝ)^n) := by
    intro n
    simp only [amplitude, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (2*(1+(n:ℝ)))^J * Scales.ε M.base N n := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by nlinarith) J)
        (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega))
      _ ≤ _ := by rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left (weighted_epsilon M N J n) (by positivity)
  have h := (hs.comp_injective Nat.succ_injective).tsum_le_tsum hc
    ((summable_geometric_two.mul_left (4*(J.factorial:ℝ))).mul_left ((2:ℝ)^J))
  simp only [tsum_mul_left, tsum_geometric_two, amplitude, Nat.cast_add, Nat.cast_one] at h
  push_cast
  nlinarith

end AlternatingNS.Effective

end DecayBoundsDevelopment

end OAI
