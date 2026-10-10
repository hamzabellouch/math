import Mathlib
import OAI.Probability.Ballisticity.Estimates.LateMoment
import OAI.Probability.Ballisticity.Coupling.FreshMoment
import OAI.Probability.Ballisticity.Estimates.StageStopping

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace DirectionalTransience

lemma cappedLogLoss_eq_neg_log {a q : ℝ} (ha : Real.exp (-a)≤q) :
    cappedLogLoss a q= -Real.log q := by
  have hq : 0<q := (Real.exp_pos _).trans_le ha
  have hlog := Real.log_le_log (Real.exp_pos _) ha
  rw [Real.log_exp] at hlog
  simp only [cappedLogLoss,ite_eq_right hq.ne',min_eq_right (by linarith : -Real.log q≤a)]

lemma exp_neg_cappedLogLoss {a q : ℝ} (hq : 0≤q) :
    Real.exp (-cappedLogLoss a q)=max (Real.exp (-a)) q := by
  by_cases h : Real.exp (-a)≤q
  · rw [cappedLogLoss_eq_neg_log h,neg_neg,Real.exp_log ((Real.exp_pos _).trans_le h),max_eq_right h]
  · have hlt : q<Real.exp (-a) := not_le.mp h
    have hcap : cappedLogLoss a q=a := by
      unfold cappedLogLoss
      by_cases hz : q=0
      · simp [hz]
      · rw [ite_eq_right hz,min_eq_left]
        have hlog := Real.log_le_log (lt_of_le_of_ne hq (Ne.symm hz)) hlt.le
        rw [Real.log_exp] at hlog
        linarith
    rw [hcap,max_eq_left hlt.le]

lemma first_protection_failure_split (q : ℕ → ℝ) (kA : ℝ) (hkA : 0≤kA)
    (n : ℕ) (hq : ∀ i≤n, 0≤q i ∧ q i≤1)
    (hpass : ∀ j<n, Real.exp (-kA*(j+1))≤∏ i∈Finset.range (j+1), q i)
    (hfail : (∏ i∈Finset.range (n+1), q i)<Real.exp (-kA*(n+1))) :
    q n<Real.exp (-(2*kA*(n+1))) ∨
      kA*(n+1)<∑ i∈Finset.range (n+1), cappedLogLoss (2*kA*(i+1)) (q i) := by
  by_cases hnew : q n<Real.exp (-(2*kA*(n+1)))
  · exact Or.inl hnew
  apply Or.inr
  have hlow (i : ℕ) (hi : i≤n) : Real.exp (-(2*kA*(i+1)))≤q i := by
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
      have hi0 : 0≤(i:ℝ)+1 := by positivity
      nlinarith only [mul_nonneg hkA hi0]
  have hprod : (∏ i∈Finset.range (n+1), q i)=Real.exp
      (-(∑ i∈Finset.range (n+1), cappedLogLoss (2*kA*(i+1)) (q i))) := by
    rw [← Finset.sum_neg_distrib,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [exp_neg_cappedLogLoss (hq i (by simpa using hi)).1,max_eq_right (hlow i (by simpa using hi))]
  rw [hprod,Real.exp_lt_exp] at hfail
  linarith only [hfail]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def protectionHeight (base : ℝ) (H : ℕ → ℕ) : ℕ → ℝ
  | 0 => base
  | n+1 => protectionHeight base H n + H n

def protectionGap (G : ℝ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => G
  | n+1 => protectionGap G r n-r n

lemma protectionHeight_mono (base : ℝ) (H : ℕ → ℕ) : Monotone (protectionHeight base H) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

lemma protectionHeight_eq (base : ℝ) (H : ℕ → ℕ) (n : ℕ) :
    protectionHeight base H n=base+∑ i∈Finset.range n, (H i:ℝ) := by
  induction n with
  | zero => simp [protectionHeight]
  | succ n ih => simp [protectionHeight,ih,Finset.sum_range_succ,add_assoc]

lemma protectionGap_eq (G : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    protectionGap G r n=G-∑ i∈Finset.range n, r i := by
  induction n with
  | zero => simp [protectionGap]
  | succ n ih => simp [protectionGap,ih,Finset.sum_range_succ,sub_sub]

noncomputable def protectionProfile {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) :
    (n : ℕ) → Environment d → BudgetProfile (k:=k) e f
      (protectionHeight base H n) (protectionGap G r n)
  | 0 => π
  | n+1 => fun ω => nextBudgetProfile e f (H n) _ _ (r n) (hr n)
      (protectionProfile e f base G H r hr π n ω) ω

lemma protectionProfile_measurable {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π) (n : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e))
      (protectionHeight base H n))) _ (protectionProfile e f base G H r hr π n) := by
  induction n with
  | zero => exact hπ
  | succ n ih => exact nextBudgetProfile_measurable_below e f _ _ _ (hr n) (H n) _ ih

def protectionFiltration {d : ℕ} (e : Direction d) (base : ℝ) (H : ℕ → ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Environment d)) where
  seq n := rowSigma (BelowHeight (realPosition (step e)) (protectionHeight base H n))
  mono' _ _ hij := rowSigma_mono (fun _ hx => lt_of_lt_of_le hx (protectionHeight_mono base H hij))
  le' _ := rowSigma_le _

noncomputable def protectionMass {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) : ℝ :=
  relativeBudgetMass e f (H n) (r n) (protectionProfile e f base G H r hr π n ω).val ω

lemma protectionMass_measurable {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π) (n : ℕ) :
    Measurable[protectionFiltration e base H (n+1)] (protectionMass e f base G H r hr π n) := by
  have hpm := protectionProfile_measurable e f base G H r hr π hπ n
  apply (budgetProfileMass_joint_rows e f _ _ (H n) (r n)
    (BelowHeight (realPosition (step e)) (protectionHeight base H (n+1))) ?_).comp
      ((hpm.mono ((protectionFiltration e base H).mono (Nat.le_succ n)) le_rfl).prodMk measurable_id)
  intro x hx j y hy
  change dot (realPosition y) (realPosition (step e)) < protectionHeight base H n+H n
  simpa only [hx j] using hy.2

lemma protectionMass_bounds {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    0≤protectionMass e f base G H r hr π n ω ∧ protectionMass e f base G H r hr π n ω≤1 :=
  relativeBudgetMass_bounds e f (H n) (r n) _ ω

lemma protection_capped_step {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (base G : ℝ) (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π)
    (a t : ℝ) (c : ℝ≥0∞) (n : ℕ)
    (hb : ∀ p : BudgetProfile (k:=k) e f (protectionHeight base H n) (protectionGap G r n),
      (∫⁻ ω, ENNReal.ofReal (Real.exp (t*cappedLogLoss a
        (relativeBudgetMass e f (H n) (r n) p.val ω))) ∂environmentLaw ν)≤c)
    (w : Environment d → ℝ≥0∞) (hw : Measurable[protectionFiltration e base H n] w) :
    (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*cappedLogLoss a
      (protectionMass e f base G H r hr π n ω))) ∂environmentLaw ν)≤c*(∫⁻ ω, w ω ∂environmentLaw ν) := by
  apply fresh_budget_capped_moment ν e f _ _ (H n) (r n) a t
    (S:=BelowHeight (realPosition (step e)) (protectionHeight base H n))
    (T:={y | protectionHeight base H n≤dot (realPosition y) (realPosition (step e))})
    ?_ ?_ _ (protectionProfile_measurable e f base G H r hr π hπ n) w hw c hb
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt.mpr (show protectionHeight base H n≤dot (realPosition x) (realPosition (step e)) from hy))
      (show dot (realPosition x) (realPosition (step e))<protectionHeight base H n from hx)
  · intro x hx y hy
    change protectionHeight base H n≤dot (realPosition y) (realPosition (step e))
    simpa only [hx] using hy.1

theorem protection_capped_sum_tail {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (base G : ℝ) (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π)
    (a : ℕ → ℝ) (t C : ℝ) (ht : 0<t)
    (hb : ∀ n, ∀ p : BudgetProfile (k:=k) e f (protectionHeight base H n) (protectionGap G r n),
      (∫⁻ ω, ENNReal.ofReal (Real.exp (t*cappedLogLoss (a n)
        (relativeBudgetMass e f (H n) (r n) p.val ω))) ∂environmentLaw ν)≤ENNReal.ofReal (Real.exp C))
    (n : ℕ) (v : ℝ) :
    environmentLaw ν {ω | v≤∑ i∈Finset.range n, cappedLogLoss (a i)
      (protectionMass e f base G H r hr π i ω)}≤ENNReal.ofReal (Real.exp (C*n-t*v)) := by
  apply adapted_exp_sum_tail (environmentLaw ν) (protectionFiltration e base H) _ ?_ t C ht ?_ n v
  · intro i
    exact @measurable_cappedLogLoss (Environment d) (protectionFiltration e base H (i+1))
      (a i) _ (protectionMass_measurable e f base G H r hr π hπ i)
  · intro i w hw
    exact protection_capped_step ν e f base G H r hr π hπ (a i) t _ i (hb i) w hw

end DirectionalTransience

end

end OAI
