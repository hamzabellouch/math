import OAI.NumberTheory.Jacobsthal.Sieve.ClockExponentialTail

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

noncomputable def clockAtOrAbove (v : ℝ) : Kernel ℝ ℝ :=
  markedClockKernel.restrict (s := Ici v) measurableSet_Ici

instance clockAtOrAbove_isFiniteKernel (v : ℝ) : IsFiniteKernel (clockAtOrAbove v) := by
  unfold clockAtOrAbove; infer_instance

lemma clockAtOrAbove_add_below (v : ℝ) : clockAtOrAbove v + clockBelow v = markedClockKernel := by
  ext x : 1
  change (markedClockKernel x).restrict (Ici v) + (markedClockKernel x).restrict (Iio v) = _
  simpa only [compl_Ici] using Measure.restrict_add_restrict_compl (μ := markedClockKernel x) measurableSet_Ici

lemma clockBelow_increment_lower (v x : ℝ) :
    ∀ᵐ y ∂clockBelow v x, x+Real.log (4/3) ≤ y := by
  rw [clockBelow,Kernel.restrict_apply]
  exact ae_restrict_of_ae (markedClock_increment_lower x)

lemma clockBelow_pow_lower (v x : ℝ) (n : ℕ) :
    ∀ᵐ y ∂(clockBelow v ^ n) x, x+(n:ℝ)*Real.log (4/3) ≤ y := by
  induction n with
  | zero =>
    simp only [pow_zero,Nat.cast_zero,zero_mul,add_zero]
    exact (ae_dirac_iff measurableSet_Ici).mpr le_rfl
  | succ n ih =>
    rw [pow_succ']
    change ∀ᵐ y ∂(clockBelow v ∘ₖ (clockBelow v ^ n)) x, _ ≤ y
    apply Kernel.ae_comp_of_ae_ae measurableSet_Ici
    filter_upwards [ih] with y hy
    filter_upwards [clockBelow_increment_lower v y] with z hz
    push_cast
    nlinarith

lemma clockBelow_mass_eq_zero {v : ℝ} (hv : 0 < v) {n : ℕ}
    (hn : v ≤ (n:ℝ)*Real.log (4/3)) : (clockBelow v ^ n) 0 univ = 0 := by
  have hfalse : ∀ᵐ y ∂(clockBelow v ^ n) 0, False := by
    filter_upwards [clockBelow_pow_lower v 0 n,clockBelow_pow_ae_lt hv n] with y hy hvy
    linarith
  simpa only [ae_iff,not_false_eq_true,ofPred_true] using hfalse

lemma clockBelow_survival_tendsto_zero {v : ℝ} (hv : 0 < v) :
    Tendsto (fun n : ℕ => (clockBelow v ^ n) 0 univ) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (v/Real.log (4/3))
  have hNc : v ≤ (N:ℝ)*Real.log (4/3) :=
    (div_lt_iff₀ markedClock_minimum_pos).mp hN |>.le
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (clockBelow_mass_eq_zero hv (hNc.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hn) markedClock_minimum_pos.le))).symm

lemma clockExit_mass_step (v : ℝ) (n : ℕ) :
    (clockAtOrAbove v ∘ₖ (clockBelow v ^ n)) 0 univ +
      (clockBelow v ^ (n+1)) 0 univ = (clockBelow v ^ n) 0 univ := by
  have hp : clockBelow v ^ (n+1) = clockBelow v ∘ₖ (clockBelow v ^ n) := pow_succ' _ _
  calc
    _ = ((clockAtOrAbove v+clockBelow v) ∘ₖ (clockBelow v ^ n)) 0 univ := by
      rw [Kernel.comp_add_left,_root_.add_apply,Measure.add_apply,hp]
    _ = (markedClockKernel ∘ₖ (clockBelow v ^ n)) 0 univ := by rw [clockAtOrAbove_add_below]
    _ = _ := by rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]; simp

lemma clockExit_finite_mass (v : ℝ) (n : ℕ) :
    (clockBelow v ^ n) 0 univ +
      ∑ k ∈ Finset.range n, (clockAtOrAbove v ∘ₖ (clockBelow v ^ k)) 0 univ = 1 := by
  induction n with
  | zero => change (Measure.dirac (0:ℝ)) univ + 0 = 1; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (∑ k ∈ Finset.range n, (clockAtOrAbove v ∘ₖ (clockBelow v ^ k)) 0 univ)+
        ((clockAtOrAbove v ∘ₖ (clockBelow v ^ n)) 0 univ+(clockBelow v ^ (n+1)) 0 univ) := by ac_rfl
      _ = _ := by rw [clockExit_mass_step]; simpa only [add_comm] using ih

lemma clockExit_mass_one {v : ℝ} (hv : 0 < v) :
    (potential (clockAtOrAbove v) (clockBelow v)) 0 univ = 1 := by
  rw [potential,Kernel.sum_apply' _ _ MeasurableSet.univ]
  have h := (clockBelow_survival_tendsto_zero hv).add (ENNReal.tendsto_nat_tsum
    (fun n => (clockAtOrAbove v ∘ₖ (clockBelow v ^ n)) 0 univ))
  simp only [zero_add,clockExit_finite_mass] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

noncomputable def clockWindow (v H : ℝ) : Kernel ℝ ℝ :=
  markedClockKernel.restrict (s := Icc v (v+H)) measurableSet_Icc

instance clockWindow_isFiniteKernel (v H : ℝ) : IsFiniteKernel (clockWindow v H) := by
  unfold clockWindow; infer_instance

noncomputable def clockWindowHit (v H : ℝ) : ℝ≥0∞ :=
  (potential (clockWindow v H) (clockBelow v)) 0 univ

lemma clockWindow_add_over {v H : ℝ} (hH : 0 ≤ H) :
    clockWindow v H+clockOver v H = clockAtOrAbove v := by
  ext x : 1
  change (markedClockKernel x).restrict (Icc v (v+H))+
    (markedClockKernel x).restrict (Ioi (v+H)) = (markedClockKernel x).restrict (Ici v)
  have hd : Disjoint (Icc v (v+H)) (Ioi (v+H)) := by
    rw [disjoint_left]
    intro y hy hz
    exact (not_lt_of_ge hy.2) hz
  rw [← Measure.restrict_union hd measurableSet_Ioi]
  congr 1
  ext y
  simp only [mem_union,mem_Icc,mem_Ioi,mem_Ici]
  constructor
  · rintro (h|h) <;> linarith
  · intro h
    by_cases hy : y ≤ v+H
    · exact Or.inl ⟨h,hy⟩
    · exact Or.inr (lt_of_not_ge hy)

theorem clockWindowHit_add_overshoot {v H : ℝ} (hv : 0 < v) (hH : 0 ≤ H) :
    clockWindowHit v H+clockOvershoot v H = 1 := by
  rw [clockWindowHit,clockOvershoot,← Measure.add_apply,← _root_.add_apply,
    ← potential_add,clockWindow_add_over hH]
  exact clockExit_mass_one hv

theorem clockWindowHit_exponential : ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧ ∀ v H : ℝ,
    0 < v → 0 ≤ H → 1-ENNReal.ofReal (C*Real.exp (-eta*H)) ≤ clockWindowHit v H := by
  obtain ⟨eta,C,heta,hC,hTail⟩ := clockOvershoot_exponential
  refine ⟨eta,C,heta,hC,?_⟩
  intro v H hv hH
  have he : clockWindowHit v H+clockOvershoot v H = 1 := clockWindowHit_add_overshoot hv hH
  have hb : 1 ≤ clockWindowHit v H+ENNReal.ofReal (C*Real.exp (-eta*H)) := by
    rw [← he]
    exact add_le_add le_rfl (hTail v H hv hH)
  exact tsub_le_iff_right.mpr hb

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
