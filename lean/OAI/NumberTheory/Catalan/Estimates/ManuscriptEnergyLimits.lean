import OAI.NumberTheory.Catalan.Analysis.RealPlaceLimsup

namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan

theorem manuscript_energy_case_threshold {N : ℕ} (hN : 0 < N) :
    ((n N - 1 - 2 * g N : ℕ) : ℝ) = (n N : ℝ) - 1 - 2 * (g N : ℝ) := by
  have hn : 1 ≤ n N := by unfold n; omega
  have hg : 2 * g N ≤ n N - 1 := by unfold n g; omega
  rw [Nat.cast_sub hg, Nat.cast_sub hn, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]

def manuscriptEnergyCaseOne (N : ℕ) :
    Set ((Fin (n N) → ℝ) × (Fin (n N) → ℝ)) :=
  {xs | (∀ i, xs.1 i ∈ Ioo (-1 : ℝ) 1) ∧
    (∀ j, xs.2 j ∈ Ioo (0 : ℝ) 1) ∧
    (∀ i, xs.1 i ≠ 0) ∧ Function.Injective xs.1 ∧
    (((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - xs.1 i ^ 2) / (1 + xs.1 i ^ 2))}

def manuscriptEnergyCaseTwo (N : ℕ) :
    Set ((Fin (n N) → ℝ) × (Fin (n N) → ℝ)) :=
  {xs | (∀ i, xs.1 i ∈ Ioo (-1 : ℝ) 1) ∧
    (∀ j, xs.2 j ∈ Ioo (0 : ℝ) 1) ∧
    (∀ i, xs.1 i ≠ 0) ∧ Function.Injective xs.1 ∧
    ((∑ i : Fin (n N), (1 - xs.1 i ^ 2) / (1 + xs.1 i ^ 2)) ≤
      ((n N - 1 - 2 * g N : ℕ) : ℝ))}

def manuscriptMajorantSupOne (N : ℕ) : EReal :=
  sSup ((fun xs : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) => manuscriptNormalizedLogSize N
    (realEnergyMajorantOne N xs.1 xs.2)) '' manuscriptEnergyCaseOne N)

def manuscriptMajorantSupTwo (N : ℕ) : EReal :=
  sSup ((fun xs : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) => manuscriptNormalizedLogSize N
    (realEnergyMajorantTwo N xs.1 xs.2)) '' manuscriptEnergyCaseTwo N)

theorem manuscript_vandermonde_eq_zero_of_not_injective {m : ℕ}
    (s : Fin m → ℝ) (hs : ¬ Function.Injective s) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (s j - s i)) = 0 := by
  classical
  by_contra hprod
  apply hs
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hrow := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
    have hdiff := Finset.prod_ne_zero_iff.mp hrow j (Finset.mem_Ioi.mpr hlt)
    exact hdiff (sub_eq_zero.mpr hij.symm)
  · have hrow := Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
    have hdiff := Finset.prod_ne_zero_iff.mp hrow i (Finset.mem_Ioi.mpr hgt)
    exact hdiff (sub_eq_zero.mpr hij)

theorem manuscript_principal_eq_zero_of_not_injective (N : ℕ)
    (x s : Fin (n N) → ℝ) (hs : ¬ Function.Injective s) :
    realPrincipalIntegrand N x s = 0 := by
  simp [realPrincipalIntegrand, manuscript_vandermonde_eq_zero_of_not_injective s hs]

theorem manuscript_majorantOne_eq_zero_of_not_injective (N : ℕ)
    (x s : Fin (n N) → ℝ) (hs : ¬ Function.Injective s) :
    realEnergyMajorantOne N x s = 0 := by
  simp [realEnergyMajorantOne, manuscript_principal_eq_zero_of_not_injective N x s hs]

theorem manuscript_majorantTwo_eq_zero_of_not_injective (N : ℕ)
    (x s : Fin (n N) → ℝ) (hs : ¬ Function.Injective s) :
    realEnergyMajorantTwo N x s = 0 := by
  simp [realEnergyMajorantTwo, manuscript_principal_eq_zero_of_not_injective N x s hs]

theorem manuscript_energy_caseOne_limsup {lam : ℝ} (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|))
    (hv : Summable (fun j => |v j|)) :
    Filter.limsup manuscriptMajorantSupOne atTop ≤
      ((realEnergyDualConstant 1 p v
        (realEnergyRowTrialSup 1 lam p v) (realEnergyColumnTrialSup v) : ℝ) : EReal) := by
  apply manuscript_limsup_le_of_eventually_le
  intro ε hε
  obtain ⟨M, hM⟩ := realEnergyMajorantOne_uniform_dual hlam p v hp hv
    (fun z hz hz0 => realEnergyRowTrialField_le_sup (by norm_num : (0 : ℝ) ≤ 1)
      hlam p v hp hv hz hz0)
    (fun z hz => realEnergyColumnTrialField_le_sup v hv hz) hε
  filter_upwards [eventually_ge_atTop M] with N hN
  unfold manuscriptMajorantSupOne
  apply sSup_le
  rintro a ⟨⟨x, s⟩, hxs, rfl⟩
  change manuscriptNormalizedLogSize N (realEnergyMajorantOne N x s) ≤ _
  rcases hxs with ⟨hx, hs, hx0, hxi, hcase⟩
  by_cases hsi : Function.Injective s
  · by_cases hz : realEnergyMajorantOne N x s = 0
    · simp [hz]
    · rw [manuscriptNormalizedLogSize_of_ne_zero hz, Real.log_abs]
      exact EReal.coe_le_coe_iff.mpr (hM N hN x s hx hs hx0 hxi hsi hcase)
  · rw [manuscript_majorantOne_eq_zero_of_not_injective N x s hsi]
    simp

theorem manuscript_energy_caseTwo_limsup
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|))
    (hv : Summable (fun j => |v j|)) :
    Filter.limsup manuscriptMajorantSupTwo atTop ≤
      ((realEnergyDualConstant 2 p v
        (realEnergyRowTrialSup 2 0 p v) (realEnergyColumnTrialSup v) : ℝ) : EReal) := by
  apply manuscript_limsup_le_of_eventually_le
  intro ε hε
  obtain ⟨M, hM⟩ := realEnergyMajorantTwo_uniform_dual p v hp hv
    (fun z hz hz0 => realEnergyRowTrialField_le_sup (by norm_num : (0 : ℝ) ≤ 2)
      (le_refl (0 : ℝ)) p v hp hv hz hz0)
    (fun z hz => realEnergyColumnTrialField_le_sup v hv hz) hε
  filter_upwards [eventually_ge_atTop M] with N hN
  unfold manuscriptMajorantSupTwo
  apply sSup_le
  rintro a ⟨⟨x, s⟩, hxs, rfl⟩
  change manuscriptNormalizedLogSize N (realEnergyMajorantTwo N x s) ≤ _
  rcases hxs with ⟨hx, hs, hx0, hxi, _hcase⟩
  by_cases hsi : Function.Injective s
  · by_cases hz : realEnergyMajorantTwo N x s = 0
    · simp [hz]
    · rw [manuscriptNormalizedLogSize_of_ne_zero hz, Real.log_abs]
      exact EReal.coe_le_coe_iff.mpr (hM N hN x s hx hs hx0 hxi hsi)
  · rw [manuscript_majorantTwo_eq_zero_of_not_injective N x s hsi]
    simp

def manuscriptTrialExponentialDecay (u : ℕ → ℝ) : Prop :=
  ∃ K r : ℝ, 0 < r ∧ r < 1 ∧ ∀ j : ℕ, |u (j + 1)| ≤ K * r ^ (j + 1)

theorem manuscriptTrialExponentialDecay.summable {u : ℕ → ℝ}
    (hu : manuscriptTrialExponentialDecay u) : Summable (fun j => |u j|) := by
  rcases hu with ⟨K, r, hr0, hr1, hb⟩
  have hg0 : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_norm_lt_one
      (by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1)
  have hg1 : Summable (fun j : ℕ => r ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hg0
  apply (summable_nat_add_iff 1).mp
  exact (hg1.mul_left K).of_norm_bounded
    (by intro j; simpa only [Real.norm_eq_abs, abs_abs] using hb j)

theorem manuscript_energy_caseOne_limsup_of_exponential_decay
    {lam : ℝ} (hlam : 0 ≤ lam) (p v : ℕ → ℝ)
    (hp : manuscriptTrialExponentialDecay p) (hv : manuscriptTrialExponentialDecay v) :
    Filter.limsup manuscriptMajorantSupOne atTop ≤
      ((realEnergyDualConstant 1 p v
        (realEnergyRowTrialSup 1 lam p v) (realEnergyColumnTrialSup v) : ℝ) : EReal) :=
  manuscript_energy_caseOne_limsup hlam p v hp.summable hv.summable

theorem manuscript_energy_caseTwo_limsup_of_exponential_decay
    (p v : ℕ → ℝ)
    (hp : manuscriptTrialExponentialDecay p) (hv : manuscriptTrialExponentialDecay v) :
    Filter.limsup manuscriptMajorantSupTwo atTop ≤
      ((realEnergyDualConstant 2 p v
        (realEnergyRowTrialSup 2 0 p v) (realEnergyColumnTrialSup v) : ℝ) : EReal) :=
  manuscript_energy_caseTwo_limsup p v hp.summable hv.summable

theorem manuscript_energy_determinant_limsup {lam : ℝ} (hlam : 0 ≤ lam)
    (p₁ v₁ p₂ v₂ : ℕ → ℝ)
    (hp₁ : Summable (fun j => |p₁ j|)) (hv₁ : Summable (fun j => |v₁ j|))
    (hp₂ : Summable (fun j => |p₂ j|)) (hv₂ : Summable (fun j => |v₂ j|)) :
    Filter.limsup manuscriptDeterminantLogSize atTop ≤
      ((max (realEnergyDualConstant 1 p₁ v₁
        (realEnergyRowTrialSup 1 lam p₁ v₁) (realEnergyColumnTrialSup v₁))
        (realEnergyDualConstant 2 p₂ v₂
          (realEnergyRowTrialSup 2 0 p₂ v₂) (realEnergyColumnTrialSup v₂)) : ℝ) : EReal) := by
  apply manuscript_limsup_le_of_eventually_le
  intro ε hε
  filter_upwards [realDeterminant_eventually_log_sup_dual hlam
    p₁ v₁ p₂ v₂ hp₁ hv₁ hp₂ hv₂ hε] with N hN
  by_cases hz : determinant N = 0
  · rw [manuscriptDeterminantLogSize_of_eq_zero hz]
    exact bot_le
  · rw [manuscriptDeterminantLogSize_of_ne_zero hz]
    exact EReal.coe_le_coe_iff.mpr (hN hz)

theorem manuscript_energy_determinant_limsup_of_exponential_decay
    {lam : ℝ} (hlam : 0 ≤ lam) (p₁ v₁ p₂ v₂ : ℕ → ℝ)
    (hp₁ : manuscriptTrialExponentialDecay p₁) (hv₁ : manuscriptTrialExponentialDecay v₁)
    (hp₂ : manuscriptTrialExponentialDecay p₂) (hv₂ : manuscriptTrialExponentialDecay v₂) :
    Filter.limsup manuscriptDeterminantLogSize atTop ≤
      ((max (realEnergyDualConstant 1 p₁ v₁
        (realEnergyRowTrialSup 1 lam p₁ v₁) (realEnergyColumnTrialSup v₁))
        (realEnergyDualConstant 2 p₂ v₂
          (realEnergyRowTrialSup 2 0 p₂ v₂) (realEnergyColumnTrialSup v₂)) : ℝ) : EReal) :=
  manuscript_energy_determinant_limsup hlam p₁ v₁ p₂ v₂
    hp₁.summable hv₁.summable hp₂.summable hv₂.summable

theorem manuscript_energy_caseOne_limsup_sharp :
    Filter.limsup manuscriptMajorantSupOne atTop ≤
      ((-(2296789875 / 1000000000 : ℝ)) : EReal) := by
  exact (manuscript_energy_caseOne_limsup barrier_lambdas.2.1 barrierP1 barrierV1
    barrier_trials_abs_summable.2.2.1 barrier_trials_abs_summable.2.2.2).trans
      (EReal.coe_le_coe_iff.mpr realDeterminantCaseOneDual_sharp_lt.le)

theorem manuscript_energy_caseTwo_limsup_sharp :
    Filter.limsup manuscriptMajorantSupTwo atTop ≤
      ((-(2290939875 / 1000000000 : ℝ)) : EReal) := by
  exact (manuscript_energy_caseTwo_limsup barrierP2 barrierV2
    barrier_trials_abs_summable.1 barrier_trials_abs_summable.2.1).trans
      (EReal.coe_le_coe_iff.mpr realDeterminantCaseTwoDual_sharp_lt.le)

end InternalCatalan

end

end

end OAI
