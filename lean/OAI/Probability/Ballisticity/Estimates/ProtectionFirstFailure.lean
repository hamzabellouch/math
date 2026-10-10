import Mathlib
import OAI.Probability.Ballisticity.Coupling.FreshBudgetEvent
import OAI.Probability.Ballisticity.Estimates.RadixBudget

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma first_protection_failure_split_offset (q : ℕ → ℝ) (kA : ℝ) (hkA : 0≤kA)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hq : ∀ i≤n, 0≤q i ∧ q i≤1)
    (hpass : ∀ j<n, Real.exp (-kA*(s+j+1))≤∏ i∈Finset.range (j+1), q i)
    (hfail : (∏ i∈Finset.range (n+1), q i)<Real.exp (-kA*(s+n+1))) :
    q n<Real.exp (-(2*kA*(s+n+1))) ∨
      kA*(s+n+1)<∑ i∈Finset.range (n+1), cappedLogLoss (2*kA*(s+i+1)) (q i) := by
  by_cases hnew : q n<Real.exp (-(2*kA*(s+n+1)))
  · exact Or.inl hnew
  apply Or.inr
  have hlow (i : ℕ) (hi : i≤n) : Real.exp (-(2*kA*(s+i+1)))≤q i := by
    by_cases hin : i=n
    · subst i; exact not_lt.mp hnew
    · have hit : i<n := lt_of_le_of_ne hi hin
      have hprod : (∏ j∈Finset.range (i+1), q j)≤q i := by
        have hh := Finset.prod_le_prod_of_subset_of_le_one₀
          (show {i}⊆Finset.range (i+1) by simp) (fun j hj => (hq j (by simp only [Finset.mem_range] at hj; omega)).1)
          (fun j hj _ => (hq j (by simp only [Finset.mem_range] at hj; omega)).2)
        simpa using hh
      apply le_trans _ ((hpass i hit).trans hprod)
      apply Real.exp_le_exp.mpr
      have hi0 : 0 ≤ s+(i:ℝ)+1 := by positivity
      nlinarith only [mul_nonneg hkA hi0]
  have hprod : (∏ i∈Finset.range (n+1), q i)=Real.exp
      (-(∑ i∈Finset.range (n+1), cappedLogLoss (2*kA*(s+i+1)) (q i))) := by
    rw [← Finset.sum_neg_distrib,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [exp_neg_cappedLogLoss (hq i (by simpa using hi)).1,max_eq_right (hlow i (by simpa using hi))]
  rw [hprod,Real.exp_lt_exp] at hfail
  linarith only [hfail]

def firstProtectionFailure {Ω : Type*} (q : ℕ → Ω → ℝ) (kA s : ℝ) (n : ℕ) : Set Ω :=
  {ω | (∀ j<n, Real.exp (-kA*(s+j+1))≤∏ i∈Finset.range (j+1), q i ω) ∧
    (∏ i∈Finset.range (n+1), q i ω)<Real.exp (-kA*(s+n+1))}

lemma firstProtectionFailure_bound {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (q : ℕ → Ω → ℝ)
    (hqm : ∀ i, Measurable[ℱ (i+1)] (q i)) (hq : ∀ i ω, 0≤q i ω ∧ q i ω≤1)
    (kA s : ℝ) (hkA : 0≤kA) (hs : 0 ≤ s) (t C : ℝ) (ht : 0<t) (n : ℕ)
    (hstep : ∀ i<n+1, ∀ w : Ω → ℝ≥0∞, Measurable[ℱ i] w →
      (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*cappedLogLoss (2*kA*(s+i+1)) (q i ω))) ∂μ)≤
        ENNReal.ofReal (Real.exp C)*(∫⁻ ω, w ω ∂μ))
    (cap : ℝ≥0∞) (hcap : ∀ A : Set Ω, MeasurableSet[ℱ n] A →
      μ (A∩{ω | q n ω<Real.exp (-(2*kA*(s+n+1)))})≤cap*μ A)
    (A : Set Ω) (hA : MeasurableSet[ℱ 0] A) :
    μ (A∩firstProtectionFailure q kA s n)≤
      (cap+ENNReal.ofReal (Real.exp (C*(n+1)-t*(kA*(s+n+1)))))*μ A := by
  let X := fun (i : ℕ) ω => cappedLogLoss (2*kA*(s+i+1)) (q i ω)
  have hX : ∀ i, Measurable[ℱ (i+1)] (X i) := fun i =>
    @measurable_cappedLogLoss Ω (ℱ (i+1)) _ _ (hqm i)
  let E : Set Ω := {ω | kA*(s+n+1)≤∑ i∈Finset.range (n+1), X i ω}
  have hEm : MeasurableSet E := measurableSet_le measurable_const
    (Finset.measurable_fun_sum _ (fun i _ => (hX i).mono (ℱ.le _) le_rfl))
  have hAm : MeasurableSet A := ℱ.le 0 A hA
  have hW : Measurable[ℱ 0] (A.indicator (fun _ : Ω => (1:ℝ≥0∞))) := measurable_const.indicator hA
  have htail := adapted_weighted_exp_sum_tail μ ℱ X hX _ hW t C ht (n+1) hstep (kA*(s+n+1))
  have heq : μ.withDensity (A.indicator (fun _ : Ω => (1:ℝ≥0∞)))=μ.restrict A :=
    withDensity_indicator_one hAm
  rw [heq,Measure.restrict_apply hEm,lintegral_indicator hAm] at htail
  simp only [lintegral_const,one_mul,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Nat.cast_add,Nat.cast_one] at htail
  have hsub : A∩firstProtectionFailure q kA s n ⊆
      (A∩{ω | q n ω<Real.exp (-(2*kA*(s+n+1)))})∪(A∩E) := by
    rintro ω ⟨hω,hpass,hfail⟩
    rcases first_protection_failure_split_offset (fun i => q i ω) kA hkA s hs n
      (fun i _ => hq i ω) hpass hfail with h|h
    · exact Or.inl ⟨hω,h⟩
    · exact Or.inr ⟨hω,h.le⟩
  apply (measure_mono hsub).trans ((measure_union_le _ _).trans _)
  rw [add_mul]
  apply add_le_add (hcap A (ℱ.mono (Nat.zero_le n) A hA))
  simpa only [Set.inter_comm] using htail

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma protection_failure_exponents {lam Cmg A : ℝ} (hC : 0≤Cmg)
    (hA : Cmg+8≤(lam/4)*A) (k s n : ℕ) (hk : 1≤k) :
    Real.exp (-lam*((2*A*k)*((s:ℝ)+n+1))/2)+
      Real.exp ((Cmg*k)*((n:ℝ)+1)-(lam/4)*((A*k)*((s:ℝ)+n+1)))≤
        Real.exp (-5*k*((s:ℝ)+n+1)) := by
  let T : ℝ := s+n+1
  have hT : 1≤T := by dsimp [T]; linarith [Nat.cast_nonneg (α:=ℝ) s,Nat.cast_nonneg (α:=ℝ) n]
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hkT : 1≤(k:ℝ)*T := one_le_mul_of_one_le_of_one_le hk1 hT
  have hCpos : 0≤Cmg*k*T := by positivity
  have hah := mul_le_mul_of_nonneg_right hA (show 0≤(k:ℝ)*T by positivity)
  have hcap : -lam*((2*A*k)*T)/2≤-8*k*T := by nlinarith only [hah,hCpos,hkT]
  have hcount : Cmg*k*((n:ℝ)+1)≤Cmg*k*T := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp [T]; linarith [Nat.cast_nonneg (α:=ℝ) s]
  have hsum : (Cmg*k)*((n:ℝ)+1)-(lam/4)*((A*k)*T)≤-8*k*T := by
    nlinarith only [hah,hcount]
  have he : 2≤Real.exp (3*k*T) := by
    have hh := Real.add_one_le_exp (3*k*T)
    nlinarith only [hh,hkT]
  calc
    _ ≤ 2*Real.exp (-8*k*T) := by
      have h1 := Real.exp_le_exp.mpr hcap
      have h2 := Real.exp_le_exp.mpr hsum
      change Real.exp (-lam*((2*A*k)*T)/2)+Real.exp ((Cmg*k)*((n:ℝ)+1)-(lam/4)*((A*k)*T))≤_
      linarith only [h1,h2]
    _ ≤ Real.exp (3*k*T)*Real.exp (-8*k*T) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [T]; ring

theorem actual_late_protection_first_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam Cmg : ℝ, 0<lam ∧ lam≤1 ∧ 0<Cmg ∧
      ∀ A : ℝ, 1≤A → Cmg+8≤(lam/4)*A → ∀ k : ℕ, 2≤k →
      ∀ (c C : ℝ) (hc : 0<c), c≤1 → 0<C → ∃ l₀ : ℕ, 0<l₀ ∧
      ∀ Bstar : ℝ, 0<Bstar → ∃ R : ℝ, ∃ hR : 0<R,
      ∀ (ρ : ℝ) (hρR : R≤ρ), ∀ n : ℕ, (2*A*k)*(l₀+n+1)≤Bstar →
      ∀ H : ℕ → ℕ, (∀ i≤n, (H i:ℝ)≤3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(l₀+i)) →
      ∀ base : ℝ, ∀ π : Environment d → BudgetProfile (k:=k) e f base (3*c*ρ/4),
      @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π →
      ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) base)] E →
        environmentLaw ν (E∩firstProtectionFailure
          (protectionMass e f base (3*c*ρ/4) H (lateBudget c ρ l₀)
            (fun i => (lateBudget_pos hc (lt_of_lt_of_le hR hρR) l₀ i).le) π)
          (A*k) l₀ n)≤ENNReal.ofReal (Real.exp (-5*k*((l₀:ℝ)+n+1)))*environmentLaw ν E := by
  obtain ⟨lam,Cmg,hlam,hlam1,hCmg,hh⟩ := scheduled_late_step_bounds ν hue e f hef htrans
  refine ⟨lam,Cmg,hlam,hlam1,hCmg,?_⟩
  intro A hA hAchoice k hk c C hc hc1 hC
  have hk1 : 1≤k := by omega
  have hk1r : (1:ℝ)≤k := by exact_mod_cast hk1
  have hak : 1≤2*A*k := by nlinarith
  obtain ⟨l₀,hlpos,hl₀⟩ := hh k hk (2*A*k) hak c C hc hc1 hC
  refine ⟨l₀,hlpos,fun Bstar hB => ?_⟩
  obtain ⟨R,hR,hbound⟩ := hl₀ Bstar hB
  refine ⟨R,hR,?_⟩
  intro ρ hρR n hcap H hH base π hπ E hE
  have hρ := hR.trans_le hρR
  let r := lateBudget c ρ l₀
  let hr := fun i => (lateBudget_pos hc hρ l₀ i).le
  let q := protectionMass e f base (3*c*ρ/4) H r hr π
  let ℱ := protectionFiltration e base H
  have hqm : ∀ i, Measurable[ℱ (i+1)] (q i) := protectionMass_measurable e f base _ H r hr π hπ
  have hqb : ∀ i ω, 0≤q i ω ∧ q i ω≤1 := protectionMass_bounds e f base _ H r hr π
  have hiCap (i : ℕ) (hi : i≤n) : (2*A*k)*((l₀:ℝ)+i+1)≤Bstar := by
    apply le_trans _ hcap
    gcongr
  have hb (i : ℕ) (hi : i≤n) (p : BudgetProfile (k:=k) e f (protectionHeight base H i)
      (protectionGap (3*c*ρ/4) r i)) := hbound ρ hρR i (hiCap i hi) (H i) (hH i hi) _ p
  have hstep : ∀ i<n+1, ∀ w : Environment d → ℝ≥0∞, Measurable[ℱ i] w →
      (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp ((lam/4)*cappedLogLoss (2*(A*k)*((l₀:ℝ)+i+1)) (q i ω))) ∂environmentLaw ν)≤
        ENNReal.ofReal (Real.exp (Cmg*k))*(∫⁻ ω, w ω ∂environmentLaw ν) := by
    intro i hi w hw
    apply protection_capped_step ν e f base _ H r hr π hπ _ (lam/4) _ i _ w hw
    intro p
    simpa only [r,mul_assoc] using (hb i (by omega) p).1
  have hcapbound : ∀ E : Set (Environment d), MeasurableSet[ℱ n] E →
      environmentLaw ν (E∩{ω | q n ω<Real.exp (-(2*(A*k)*((l₀:ℝ)+n+1)))})≤
        ENNReal.ofReal (Real.exp (-lam*((2*A*k)*((l₀:ℝ)+n+1))/2))*environmentLaw ν E := by
    intro E hE
    apply fresh_random_budget_mass_lt ν e f _ _ _ _ (H n) _
      (protectionProfile_measurable e f base _ H r hr π hπ n) E hE
    intro η hη
    simpa only [r,mul_assoc] using (hb n le_rfl (protectionProfile e f base _ H r hr π n η)).2
  have hfirst := firstProtectionFailure_bound (environmentLaw ν) ℱ q hqm hqb (A*k) l₀
    (by positivity) (Nat.cast_nonneg _) (lam/4) (Cmg*k) (by positivity) n hstep _ hcapbound E hE
  apply hfirst.trans
  apply mul_le_mul_left
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (protection_failure_exponents hCmg.le hAchoice k l₀ n hk1)

end DirectionalTransience

end

end OAI
