import Mathlib
import OAI.Probability.SKSupport.Diffusion.ExpectedFeedbackStep
import OAI.Probability.SKSupport.Foundations.SumRangeBlocks
import OAI.Probability.SKSupport.Backward.Backward

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Nonuniform
open WeakIto Heat
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def time (h : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 := ∑ k ∈ Finset.range n, h k

@[simp] lemma time_zero (h : ℕ → ℝ≥0) : time h 0 = 0 := by simp [time]
@[simp] lemma time_succ (h : ℕ → ℝ≥0) (n : ℕ) : time h (n+1) = time h n+h n := by
  simp only [time,Finset.sum_range_succ]
lemma time_mono (h : ℕ → ℝ≥0) : Monotone (time h) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [time_succ]
  exact le_add_of_nonneg_right (bot_le : (0:ℝ≥0) ≤ h n)

lemma coe_time_succ (h : ℕ → ℝ≥0) (n : ℕ) : (time h (n+1):ℝ) = (time h n:ℝ)+(h n:ℝ) := by
  rw [time_succ,NNReal.coe_add]

def controlled (B α : ℝ≥0 → Ω → ℝ) (h c : ℕ → ℝ≥0) (x : ℝ) : ℕ → Ω → ℝ
  | 0, _ => x
  | k+1, ξ => controlled B α h c x k ξ + (B (time h (k+1)) ξ-B (time h k) ξ)+
      stepDrift (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ

lemma controlled_adapted {B α : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ξ, |α t ξ| ≤ 1) (h c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (time h n)]
      (controlled B α h c x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hle := time_mono h (Nat.le_succ n)
    have hYm := ih.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBs := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (time h n)).measurable.mono
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (time h (n+1))).measurable
    have hAm := progressive_stepDrift_measurable _ hap hab (time h n) (h n) (c n)
    rw [← time_succ] at hAm
    exact (hYm.add (hBt.sub hBs)).add hAm

lemma controlled_integrable {B α : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (ham : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2))
    (hab : ∀ t ξ, |α t ξ| ≤ 1) (h c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) :
    Integrable (controlled B α h c x n) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  induction n with
  | zero => exact integrable_const x
  | succ n ih =>
    exact (ih.add ((hB.integrable_eval _).sub (hB.integrable_eval _))).add
      (stepDrift_integrable ham' (fun r ξ => hab _ ξ) (time h n) (h n) (c n)
        (h n).coe_nonneg (c n).coe_nonneg)

omit mΩ in
lemma controlled_formula (B α : ℝ≥0 → Ω → ℝ) (h c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) (ξ : Ω) :
    controlled B α h c x n ξ = x+B (time h n) ξ-B 0 ξ+
      ∑ k ∈ Finset.range n, stepDrift (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ := by
  induction n with
  | zero => simp [controlled]
  | succ n ih => rw [controlled,ih,Finset.sum_range_succ]; ring

def elementary (h : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) : ℕ → ℝ≥0 → Ω → ℝ
  | 0, _, _ => 0
  | n+1, t, ξ => if time h n ≤ t ∧ t < time h (n+1) then a n ξ else elementary h a n t ξ

omit mΩ in
lemma elementary_bound (h : ℕ → ℝ≥0) {a : ℕ → Ω → ℝ} (ha : ∀ k ξ, |a k ξ| ≤ 1)
    (n : ℕ) (t : ℝ≥0) (ξ : Ω) : |elementary h a n t ξ| ≤ 1 := by
  induction n with
  | zero => simp [elementary]
  | succ n ih => simp only [elementary]; split_ifs <;> first | exact ha n ξ | exact ih

lemma elementary_progressive (ℱ : Filtration ℝ≥0 mΩ) (h : ℕ → ℝ≥0)
    {a : ℕ → Ω → ℝ} (ha : ∀ n, Measurable[ℱ (time h n)] (a n)) (n : ℕ) :
    IsProgressive ℱ (elementary h a n) := by
  induction n with
  | zero => exact isProgressive_const ℱ 0
  | succ n ih =>
    intro s
    by_cases hns : time h n ≤ s
    · have ham : Measurable[ℱ s] (a n) := (ha n).mono (ℱ.mono hns) le_rfl
      let : MeasurableSpace Ω := ℱ s
      have htime : Measurable (fun p : Set.Iic s × Ω => (p.1:ℝ≥0)) :=
        measurable_subtype_coe.comp measurable_fst
      have hset : MeasurableSet {p : Set.Iic s × Ω |
          time h n ≤ (p.1:ℝ≥0) ∧ (p.1:ℝ≥0) < time h (n+1)} :=
        (measurableSet_le (measurable_const : Measurable (fun _ : Set.Iic s × Ω => time h n)) htime).inter
          (measurableSet_lt (α := ℝ≥0) (f := fun p : Set.Iic s × Ω => (p.1:ℝ≥0))
            (g := fun _ : Set.Iic s × Ω => time h (n+1)) htime measurable_const)
      exact (ham.comp measurable_snd).ite hset (ih s)
    · convert ih s using 1
      funext p
      have hn : ¬time h n ≤ (p.1:ℝ≥0) := fun ht => hns (ht.trans p.1.property)
      simp only [elementary,hn,false_and,↓reduceIte]

omit mΩ in
lemma elementary_on_step (h : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (n k : ℕ) (hk : k < n)
    (t : ℝ≥0) (ht : time h k ≤ t ∧ t < time h (k+1)) (ξ : Ω) :
    elementary h a n t ξ = a k ξ := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst k; simp only [elementary,ite_eq_left ht]
    · have hk' : k < n := by omega
      have hlt : t < time h n := ht.2.trans_le (time_mono h (by omega : k+1 ≤ n))
      simp only [elementary,not_le.mpr hlt,false_and,↓reduceIte]
      exact ih hk'

omit mΩ in
lemma elementary_integral_on_step (h : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ)
    (n k : ℕ) (hk : k < n) (φ : ℝ → ℝ) (ξ : Ω) :
    (∫ r in (time h k:ℝ)..(time h k:ℝ)+(h k:ℝ),
      φ (elementary h a n (Real.toNNReal r) ξ)) = (h k:ℝ)*φ (a k ξ) := by
  have he : (∫ r in (time h k:ℝ)..(time h k:ℝ)+(h k:ℝ),
      φ (elementary h a n (Real.toNNReal r) ξ)) =
      ∫ _r in (time h k:ℝ)..(time h k:ℝ)+(h k:ℝ), φ (a k ξ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [(h k).coe_nonneg])
    intro r hr
    have hr0 : 0 ≤ r := (time h k).coe_nonneg.trans hr.1.le
    have ht : time h k ≤ Real.toNNReal r ∧ Real.toNNReal r < time h (k+1) := by
      constructor
      · apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ hr0]
        exact hr.1.le
      · apply NNReal.coe_lt_coe.mp
        rw [Real.coe_toNNReal _ hr0,coe_time_succ]
        exact hr.2
    change φ (elementary h a n (Real.toNNReal r) ξ) = φ (a k ξ)
    rw [elementary_on_step h a n k hk _ ht ξ]
  rw [he,intervalIntegral.integral_const]
  simp only [add_sub_cancel_left,smul_eq_mul]

structure GridData (N : ℕ) (h c : ℕ → ℝ≥0) (F D : ℕ → ℝ → ℝ → ℝ) where
  C₂ : ℝ≥0
  C₃ : ℝ≥0
  Ct : ℝ≥0
  L : ℝ≥0
  Γ : ℝ≥0
  smooth : ∀ k t, ContDiff ℝ 3 (F k t)
  gradient_bound : ∀ k t z, |deriv (F k t) z| ≤ 1
  seam : ∀ k < N, F k (time h (k+1)) = F (k+1) (time h (k+1))
  coefficient_bound : ∀ k < N, c k ≤ Γ
  second_bound : ∀ k < N, ∀ t z, |deriv (deriv (F k t)) z| ≤ C₂
  third_bound : ∀ k < N, ∀ t z, |iteratedDeriv 3 (F k t) z| ≤ C₃
  rate_measurable : ∀ k t, Measurable (D k t)
  rate_bound : ∀ k < N, ∀ t z, |D k t z| ≤ Ct
  time_derivative : ∀ k < N, ∀ r ∈ Icc (time h k:ℝ) (time h (k+1):ℝ), ∀ z,
      HasDerivWithinAt (fun t => F k t z) (D k r z)
        (Icc (time h k:ℝ) (time h (k+1):ℝ)) r
  rate_joint : ∀ k < N, ∀ r ∈ Icc (time h k:ℝ) (time h (k+1):ℝ),
      ∀ s ∈ Icc (time h k:ℝ) (time h (k+1):ℝ), ∀ z y,
      |D k r z-D k s y| ≤ (L:ℝ)*(|r-s|+|z-y|)
  pde : ∀ k < N, ∀ t ∈ Icc (time h k:ℝ) (time h (k+1):ℝ), ∀ z,
      D k t z+(1/2:ℝ)*deriv (deriv (F k t)) z+(c k:ℝ)/2*(deriv (F k t) z)^2 = 0

def profit (B α : ℝ≥0 → Ω → ℝ) (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  (∫ ξ, f (controlled B α h c x N ξ) ∂P)-
    ∑ k ∈ Finset.range N, ∫ ξ, stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ ∂P

lemma telescope_bound (Q K ε : ℕ → ℝ) (n : ℕ)
    (hs : ∀ k < n, Q (k+1)-Q k-K k ≤ ε k) :
    Q n-Q 0-(∑ k ∈ Finset.range n, K k) ≤ ∑ k ∈ Finset.range n, ε k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun k hk => hs k (by omega))
    have hlast := hs n (by omega)
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    linarith

lemma GridData.mesh_upper {B α : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ξ, |α t ξ| ≤ 1) {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (x : ℝ) :
    profit (P := P) B α h c (F N (time h N)) x N-F 0 0 x ≤
      ∑ k ∈ Finset.range N, verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have ham := progressive_joint_measurable _ hap
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  let Q (k : ℕ) := ∫ ξ, F k (time h k) (controlled B α h c x k ξ) ∂P
  let K (k : ℕ) := ∫ ξ, stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ ∂P
  have hstep (k : ℕ) (hk : k < N) : Q (k+1)-Q k-K k ≤ verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k) := by
    have hleft : (time h k:ℝ) ∈ Icc (time h k:ℝ) (time h (k+1):ℝ) :=
      ⟨le_rfl,NNReal.coe_le_coe.mpr (time_mono h (Nat.le_succ k))⟩
    have hu := expected_verification_step hB hm (time h k) (h k) (c k)
      (controlled_adapted hm hap hab h c x k) (controlled_integrable hB ham hab h c x k)
      (α := fun r => α (Real.toNNReal r)) ham' (fun r ξ => hab _ ξ)
      (sd.smooth k) 1 sd.C₂ sd.C₃ sd.Ct sd.L
      (sd.gradient_bound k) (sd.second_bound k hk) (sd.third_bound k hk)
      (sd.rate_measurable k _) (sd.rate_bound k hk _)
      (by simpa only [coe_time_succ] using sd.time_derivative k hk)
      (by simpa only [coe_time_succ] using
        fun r hr z y => sd.rate_joint k hk r hr (time h k) hleft z y)
      (sd.pde k hk (time h k) hleft)
    have he : (fun ξ => F k ((time h k:ℝ)+(h k:ℝ))
        (controlled B α h c x k ξ+(B (time h k+h k) ξ-B (time h k) ξ)+
          stepDrift (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ)) =
        fun ξ => F (k+1) (time h (k+1)) (controlled B α h c x (k+1) ξ) := by
      funext ξ
      rw [← time_succ,← coe_time_succ,sd.seam k hk]
      rfl
    rw [he] at hu
    exact hu.trans (verificationError_mono (c k) sd.Γ sd.C₂ sd.C₂ sd.C₃ sd.C₃ sd.L sd.L (h k)
      (sd.coefficient_bound k hk) le_rfl le_rfl le_rfl)
  have hh := telescope_bound Q K (fun k => verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k)) N hstep
  have hz : Q 0 = F 0 0 x := by simp [Q,controlled]
  rw [hz] at hh
  dsimp only [profit]
  linarith

def euler (B : ℝ≥0 → Ω → ℝ) (h c : ℕ → ℝ≥0) (u : ℕ → ℝ → ℝ) (x : ℝ) : ℕ → Ω → ℝ
  | 0, _ => x
  | k+1, ξ => euler B h c u x k ξ+(B (time h (k+1)) ξ-B (time h k) ξ)+
      (c k:ℝ)*(h k:ℝ)*u k (euler B h c u x k ξ)

lemma euler_adapted {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (h c : ℕ → ℝ≥0) {u : ℕ → ℝ → ℝ} (hum : ∀ k, Measurable (u k)) (x : ℝ) (n : ℕ) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (time h n)]
      (euler B h c u x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hle := time_mono h (Nat.le_succ n)
    have hYm := ih.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBs := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (time h n)).measurable.mono
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (time h (n+1))).measurable
    exact (hYm.add (hBt.sub hBs)).add (((hum n).comp hYm).const_mul ((c n:ℝ)*(h n:ℝ)))

omit mΩ in
lemma euler_controlled {B : ℝ≥0 → Ω → ℝ} (h c : ℕ → ℝ≥0) (u : ℕ → ℝ → ℝ)
    (x : ℝ) (n k : ℕ) (hk : k ≤ n) (ξ : Ω) :
    controlled B (elementary h (fun j ξ => u j (euler B h c u x j ξ)) n) h c x k ξ =
      euler B h c u x k ξ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < n := by omega
    have he := elementary_integral_on_step h (fun j ξ => u j (euler B h c u x j ξ)) n k hk'
      (fun z => (c k:ℝ)*z) ξ
    change stepDrift (fun r => elementary h (fun j ξ => u j (euler B h c u x j ξ)) n (Real.toNNReal r))
      (time h k) (h k) (c k) ξ = (h k:ℝ)*((c k:ℝ)*u k (euler B h c u x k ξ)) at he
    rw [controlled,he,ih (by omega),euler]
    ring

lemma GridData.mesh_lower {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (x : ℝ) :
    ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α ∧
      (∀ t ξ, |α t ξ| ≤ 1) ∧
      F 0 0 x-(∑ k ∈ Finset.range N, verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k)) ≤
        profit (P := P) B α h c (F N (time h N)) x N := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let u (k : ℕ) := deriv (F k (time h k))
  let a (k : ℕ) (ξ : Ω) := u k (euler B h c u x k ξ)
  let α := elementary h a N
  have hum : ∀ k, Measurable (u k) := fun k =>
    (show ContDiff ℝ 2 (u k) from (sd.smooth k _).deriv').continuous.measurable
  have hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α :=
    elementary_progressive _ h (fun k => (hum k).comp (euler_adapted hm h c hum x k)) N
  have hab : ∀ t ξ, |α t ξ| ≤ 1 := elementary_bound h (fun k ξ => sd.gradient_bound _ _ _) N
  refine ⟨α,hap,hab,?_⟩
  have ham := progressive_joint_measurable _ hap
  have hgrid (k : ℕ) (hk : k ≤ N) (ξ : Ω) :
      controlled B α h c x k ξ = euler B h c u x k ξ := euler_controlled h c u x N k hk ξ
  let Q (k : ℕ) := ∫ ξ, F k (time h k) (controlled B α h c x k ξ) ∂P
  let K (k : ℕ) := ∫ ξ, stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ ∂P
  have hstep (k : ℕ) (hk : k < N) : -Q (k+1)-(-Q k)-(-K k) ≤
      verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k) := by
    have hleft : (time h k:ℝ) ∈ Icc (time h k:ℝ) (time h (k+1):ℝ) :=
      ⟨le_rfl,NNReal.coe_le_coe.mpr (time_mono h (Nat.le_succ k))⟩
    have hg := expected_feedback_step hB hm (time h k) (h k) (c k)
      (controlled_adapted hm hap hab h c x k) (controlled_integrable hB ham hab h c x k)
      (sd.smooth k) sd.C₂ sd.C₃ sd.Ct sd.L (sd.gradient_bound k) (sd.second_bound k hk)
      (sd.third_bound k hk) (sd.rate_measurable k _) (sd.rate_bound k hk _)
      (by simpa only [coe_time_succ] using sd.time_derivative k hk)
      (by simpa only [coe_time_succ] using
        fun r hr z y => sd.rate_joint k hk r hr (time h k) hleft z y)
      (sd.pde k hk (time h k) hleft)
    have he : (fun ξ => F k ((time h k:ℝ)+(h k:ℝ))
        (controlled B α h c x k ξ+(B (time h k+h k) ξ-B (time h k) ξ)+
          (c k:ℝ)*(h k:ℝ)*deriv (F k (time h k)) (controlled B α h c x k ξ))) =
        fun ξ => F (k+1) (time h (k+1)) (controlled B α h c x (k+1) ξ) := by
      funext ξ
      rw [← time_succ,← coe_time_succ,sd.seam k hk]
      rw [hgrid k hk.le,hgrid (k+1) (by omega)]
      rfl
    rw [he] at hg
    have hK : K k = (c k:ℝ)*(h k:ℝ)/2*
        (∫ ξ, (deriv (F k (time h k)) (controlled B α h c x k ξ))^2 ∂P) := by
      dsimp only [K]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      have hh := elementary_integral_on_step h a N k hk (fun z => (c k:ℝ)*z^2) ξ
      change stepCost (fun r => α (Real.toNNReal r)) (time h k) (h k) (c k) ξ = _
      rw [stepCost,hh]
      dsimp only [a,u]
      rw [hgrid k hk.le]
      ring
    have hg' : |Q (k+1)-Q k-K k| ≤ verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k) := by
      rw [hK]
      exact hg.trans (verificationError_mono (c k) sd.Γ sd.C₂ sd.C₂ sd.C₃ sd.C₃ sd.L sd.L (h k)
        (sd.coefficient_bound k hk) le_rfl le_rfl le_rfl)
    linarith [(abs_le.mp hg').1]
  have hh := telescope_bound (fun k => -Q k) (fun k => -K k)
    (fun k => verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k)) N hstep
  have hz : Q 0 = F 0 0 x := by simp [Q,controlled]
  rw [hz,Finset.sum_neg_distrib] at hh
  change F 0 0 x-(∑ k ∈ Finset.range N, verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h k)) ≤
    Q N-∑ k ∈ Finset.range N, K k
  linarith

def refineLengths (h : ℕ → ℝ≥0) (m : ℕ) : ℕ → ℝ≥0 := fun j => h (j/m)/(m:ℝ≥0)

lemma refine_time_block (h : ℕ → ℝ≥0) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    time (refineLengths h m) (k*m) = time h k := by
  apply NNReal.coe_injective
  simp only [time,NNReal.coe_sum,refineLengths,NNReal.coe_div,NNReal.coe_natCast]
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ j ∈ Finset.range m, (h ((i*m+j)/m):ℝ)/(m:ℝ)) =
      ∑ _j ∈ Finset.range m, (h i:ℝ)/(m:ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [refined_coefficient hm (Finset.mem_range.mp hj)]
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma refine_time_inside (h : ℕ → ℝ≥0) {m : ℕ} (hm : 0 < m) (k j : ℕ) (hj : j ≤ m) :
    time (refineLengths h m) (k*m+j) = time h k+(j:ℝ≥0)*(h k/(m:ℝ≥0)) := by
  induction j with
  | zero => simp only [refine_time_block h hm,Nat.cast_zero,zero_mul,add_zero]
  | succ j ih =>
    have hjm : j < m := by omega
    rw [show k*m+(j+1) = (k*m+j)+1 by omega,time_succ,ih (by omega)]
    simp only [refineLengths,refined_coefficient hm hjm,Nat.cast_add,Nat.cast_one]
    ring

lemma refine_cell_subset (h : ℕ → ℝ≥0) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Icc (time (refineLengths h m) j:ℝ) (time (refineLengths h m) (j+1):ℝ) ⊆
      Icc (time h (j/m):ℝ) (time h (j/m+1):ℝ) := by
  have hl : j/m*m ≤ j := Nat.div_mul_le_self _ _
  have hu : j+1 ≤ (j/m+1)*m := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self _)
  intro r hr
  constructor
  · have ht := time_mono (refineLengths h m) hl
    rw [refine_time_block h hm] at ht
    exact (NNReal.coe_le_coe.mpr ht).trans hr.1
  · have ht := time_mono (refineLengths h m) hu
    rw [refine_time_block h hm] at ht
    exact hr.2.trans (NNReal.coe_le_coe.mpr ht)

lemma grid_drift_refinement {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ξ, |α r ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) (n m : ℕ) (hmpos : 0 < m) (ξ : Ω) :
    (∑ j ∈ Finset.range (n*m), stepDrift α (time (refineLengths h m) j)
      (refineLengths h m j) (c (j/m)) ξ) =
      ∑ k ∈ Finset.range n, stepDrift α (time h k) (h k) (c k) ξ := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (∑ j ∈ Finset.range m, stepDrift α (time (refineLengths h m) (k*m+j))
      (refineLengths h m (k*m+j)) (c ((k*m+j)/m)) ξ) =
      ∑ j ∈ Finset.range m, stepDrift α ((time h k:ℝ)+(j:ℝ)*((h k:ℝ)/(m:ℝ)))
        ((h k:ℝ)/(m:ℝ)) (c k) ξ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    rw [refine_time_inside h hmpos k j hjm.le]
    simp only [refineLengths,refined_coefficient hmpos hjm,NNReal.coe_add,NNReal.coe_mul,
      NNReal.coe_div,NNReal.coe_natCast]
  rw [he]
  exact stepDrift_subdivision hm hb (time h k) (h k) (c k) (h k).coe_nonneg m hmpos ξ

lemma grid_cost_refinement {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ξ, |α r ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) (n m : ℕ) (hmpos : 0 < m) (ξ : Ω) :
    (∑ j ∈ Finset.range (n*m), stepCost α (time (refineLengths h m) j)
      (refineLengths h m j) (c (j/m)) ξ) =
      ∑ k ∈ Finset.range n, stepCost α (time h k) (h k) (c k) ξ := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (∑ j ∈ Finset.range m, stepCost α (time (refineLengths h m) (k*m+j))
      (refineLengths h m (k*m+j)) (c ((k*m+j)/m)) ξ) =
      ∑ j ∈ Finset.range m, stepCost α ((time h k:ℝ)+(j:ℝ)*((h k:ℝ)/(m:ℝ)))
        ((h k:ℝ)/(m:ℝ)) (c k) ξ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    rw [refine_time_inside h hmpos k j hjm.le]
    simp only [refineLengths,refined_coefficient hmpos hjm,NNReal.coe_add,NNReal.coe_mul,
      NNReal.coe_div,NNReal.coe_natCast]
  rw [he]
  exact stepCost_subdivision hm hb (time h k) (h k) (c k) (h k).coe_nonneg m hmpos ξ
lemma controlled_refinement (B : ℝ≥0 → Ω → ℝ) {α : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2)) (hb : ∀ r ξ, |α r ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) (x : ℝ) (n m : ℕ) (hmpos : 0 < m) (ξ : Ω) :
    controlled B α (refineLengths h m) (fun j => c (j/m)) x (n*m) ξ =
      controlled B α h c x n ξ := by
  have hm' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    hm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  simp only [controlled_formula,refine_time_block h hmpos]
  rw [grid_drift_refinement hm' (fun r ξ => hb _ ξ) h c n m hmpos ξ]

lemma profit_refinement {B α : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P]
    (ham : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2)) (hab : ∀ t ξ, |α t ξ| ≤ 1)
    (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (x : ℝ) (N m : ℕ) (hmpos : 0 < m) :
    profit (P := P) B α (refineLengths h m) (fun j => c (j/m)) f x (N*m) =
      profit (P := P) B α h c f x N := by
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  unfold profit
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with ξ
    rw [controlled_refinement B ham hab h c x N m hmpos ξ]
  · have hi (d a : ℝ≥0) (s : ℝ) : Integrable (stepCost (fun r => α (Real.toNNReal r)) s d a) P :=
      stepCost_integrable (α := fun r => α (Real.toNNReal r)) ham' (fun r ξ => hab _ ξ) s d a d.coe_nonneg a.coe_nonneg
    rw [← integral_finsetSum (Finset.range (N*m)) (fun j _ => hi _ _ _),
      ← integral_finsetSum (Finset.range N) (fun k _ => hi _ _ _)]
    apply integral_congr_ae
    filter_upwards [] with ξ
    exact grid_cost_refinement ham' (fun r ξ => hab _ ξ) h c N m hmpos ξ

noncomputable def GridData.refine {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (m : ℕ) (hm : 0 < m) :
    GridData (N*m) (refineLengths h m) (fun j => c (j/m)) (fun j => F (j/m)) (fun j => D (j/m)) := by
  have hq (j : ℕ) (hj : j < N*m) : j/m < N := (Nat.div_lt_iff_lt_mul hm).mpr hj
  refine ⟨sd.C₂,sd.C₃,sd.Ct,sd.L,sd.Γ,
    fun j => sd.smooth (j/m), fun j => sd.gradient_bound (j/m), ?_,
    fun j hj => sd.coefficient_bound _ (hq j hj),
    fun j hj => sd.second_bound _ (hq j hj),
    fun j hj => sd.third_bound _ (hq j hj), fun j => sd.rate_measurable (j/m),
    fun j hj => sd.rate_bound _ (hq j hj), ?_,?_,?_⟩
  · intro j hj
    rcases refinement_successor hm j with he | ⟨he,hde⟩
    · rw [he]
    · rw [he,hde,refine_time_block h hm]
      exact sd.seam (j/m) (hq j hj)
  · intro j hj r hr z
    exact (sd.time_derivative _ (hq j hj) r (refine_cell_subset h hm j hr) z).mono
      (refine_cell_subset h hm j)
  · intro j hj r hr s hs z y
    exact sd.rate_joint _ (hq j hj) r (refine_cell_subset h hm j hr) s
      (refine_cell_subset h hm j hs) z y
  · intro j hj t ht z
    exact sd.pde _ (hq j hj) t (refine_cell_subset h hm j ht) z

lemma sum_error_refinement (h : ℕ → ℝ≥0) (N m : ℕ) (hm : 0 < m) (Γ C₂ C₃ L : ℝ≥0) :
    (∑ j ∈ Finset.range (N*m), verificationError Γ C₂ C₃ L (refineLengths h m j)) =
      ∑ k ∈ Finset.range N, (m:ℝ)*verificationError Γ C₂ C₃ L ((h k:ℝ)/(m:ℝ)) := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (∑ j ∈ Finset.range m, verificationError Γ C₂ C₃ L (refineLengths h m (k*m+j))) =
      ∑ _j ∈ Finset.range m, verificationError Γ C₂ C₃ L ((h k:ℝ)/(m:ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [refineLengths,refined_coefficient hm (Finset.mem_range.mp hj),NNReal.coe_div,NNReal.coe_natCast]
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma refined_error_limit (h : ℕ → ℝ≥0) (N : ℕ) (Γ C₂ C₃ L : ℝ≥0) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range N,
      (m:ℝ)*verificationError Γ C₂ C₃ L ((h k:ℝ)/(m:ℝ))) atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range N) (fun k _ => verificationError_limit (h k) Γ C₂ C₃ L)

def objectives {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t)) (h c : ℕ → ℝ≥0)
    (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ α : ℝ≥0 → Ω → ℝ,
    IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α ∧
    (∀ t ξ, |α t ξ| ≤ 1) ∧ v = profit (P := P) B α h c f x N}

lemma objectives_nonempty {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : (objectives (P := P) hm h c f x N).Nonempty := by
  exact ⟨_,fun _ _ => 0,isProgressive_const _ _,by simp,rfl⟩

lemma GridData.control_upper {B α : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ξ, |α t ξ| ≤ 1) {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (x : ℝ) :
    profit (P := P) B α h c (F N (time h N)) x N ≤ F 0 0 x := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hlim := refined_error_limit h N sd.Γ sd.C₂ sd.C₃ sd.L
  have hh : profit (P := P) B α h c (F N (time h N)) x N-F 0 0 x ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm1
    have hmpos : 0 < m := by omega
    have hu := (sd.refine m hmpos).mesh_upper hB hm hap hab x
    have hdiv : N*m/m = N := by rw [Nat.mul_comm,Nat.mul_div_cancel_left _ hmpos]
    change profit (P := P) B α (refineLengths h m) (fun j => c (j/m))
      (F (N*m/m) (time (refineLengths h m) (N*m))) x (N*m)-F (0/m) 0 x ≤
      ∑ j ∈ Finset.range (N*m), verificationError sd.Γ sd.C₂ sd.C₃ sd.L (refineLengths h m j) at hu
    rw [hdiv,refine_time_block h hmpos,Nat.zero_div,
      profit_refinement (progressive_joint_measurable _ hap) hab h c _ x N m hmpos,
      sum_error_refinement h N m hmpos] at hu
    exact hu
  linarith

lemma GridData.control_lower {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {N : ℕ} {h c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : GridData N h c F D) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v ∈ objectives (P := P) hm h c (F N (time h N)) x N, F 0 0 x-ε ≤ v := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hlim := refined_error_limit h N sd.Γ sd.C₂ sd.C₃ sd.L
  obtain ⟨m,hm1,he⟩ := ((eventually_ge_atTop (1:ℕ)).and (hlim.eventually (gt_mem_nhds hε))).exists
  have hmpos : 0 < m := by omega
  obtain ⟨α,hap,hab,hl⟩ := (sd.refine m hmpos).mesh_lower hB hm x
  have hdiv : N*m/m = N := by rw [Nat.mul_comm,Nat.mul_div_cancel_left _ hmpos]
  change F (0/m) 0 x-(∑ j ∈ Finset.range (N*m),
    verificationError sd.Γ sd.C₂ sd.C₃ sd.L (refineLengths h m j)) ≤
    profit (P := P) B α (refineLengths h m) (fun j => c (j/m))
      (F (N*m/m) (time (refineLengths h m) (N*m))) x (N*m) at hl
  rw [hdiv,refine_time_block h hmpos,Nat.zero_div,
    profit_refinement (progressive_joint_measurable _ hap) hab h c _ x N m hmpos,
    sum_error_refinement h N m hmpos] at hl
  refine ⟨_,⟨α,hap,hab,rfl⟩,?_⟩
  linarith

def cascadeV (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, x => f x
  | n+1, k, x => logSemigroup (c k) (h k) (cascadeV h c f n (k+1)) x

lemma cascadeV_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) : LipschitzWith K (cascadeV h c f N k) := by
  induction N generalizing k with
  | zero => exact hf
  | succ N ih => exact logSemigroup_lipschitz (ih (k+1)) (c k).coe_nonneg (h k)

lemma cascadeV_regular {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) : RegularDatum (cascadeV h c f N k) := by
  induction N generalizing k with
  | zero => exact hf
  | succ N ih =>
    exact regularDatum_logSemigroup (ih (k+1))
      (cascadeV_lipschitz hLip h c N (k+1)) (c k).coe_nonneg (h k)

def cascadeVAt (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ :=
  cascadeV h c f (N-k) k

def cellVHeat (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ → ℝ :=
  backward (c k) (time h (min (k+1) N)) (cascadeVAt h c f N (k+1))

def cellVRate (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ → ℝ :=
  backwardRate (c k) (time h (min (k+1) N)) (cascadeVAt h c f N (k+1))

lemma cellVHeat_verificationData {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) :
    VerificationData (cellVHeat h c f N k) (cellVRate h c f N k) (c k) (time h (min (k+1) N)) :=
  backward_verificationData (cascadeV_regular hf hLip h c _ _)
    (cascadeV_lipschitz hLip h c _ _) (c k).coe_nonneg _

lemma cellVHeat_left {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) (hk : k ≤ N) :
    cellVHeat h c f N k (time h k) = cascadeVAt h c f N k := by
  by_cases he : k = N
  · subst k
    funext x
    simpa [cellVHeat,cascadeVAt,cascadeV,Nat.min_eq_right (Nat.le_succ N)] using
      backward_terminal (c N) (time h N) f x
  · have hk' : k < N := lt_of_le_of_ne hk he
    have hN : N-k = (N-(k+1))+1 := by omega
    funext x
    unfold cellVHeat cascadeVAt backward
    rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
    have ht : (time h (k+1):ℝ)-(time h k:ℝ) = (h k:ℝ) := by rw [coe_time_succ]; ring
    rw [ht,hN,cascadeV]
    exact varianceLogHeat_eq_logSemigroup
      (cascadeV_regular hf hLip h c _ _).smooth.continuous.measurable (c k) (h k) x

lemma cellVHeat_right (h c : ℕ → ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) (hk : k < N) :
    cellVHeat h c f N k (time h (k+1)) = cascadeVAt h c f N (k+1) := by
  funext x
  dsimp only [cellVHeat]
  rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
  exact backward_terminal _ _ _ _

lemma cellVHeat_seam {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N k : ℕ) (hk : k < N) :
    cellVHeat h c f N k (time h (k+1)) = cellVHeat h c f N (k+1) (time h (k+1)) := by
  rw [cellVHeat_right h c f N k hk,cellVHeat_left hf hLip h c N (k+1) (by omega)]

noncomputable def cellVHeat_gridData {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N : ℕ) : GridData N h c (cellVHeat h c f N) (cellVRate h c f N) := by
  classical
  have hd (k : ℕ) := cellVHeat_verificationData hf hLip h c N k
  have hb (k : ℕ) := (hd k).bounds
  choose C₂ C₃ Ct L H using hb
  refine ⟨(Finset.range N).sup C₂,(Finset.range N).sup C₃,
    (Finset.range N).sup Ct,(Finset.range N).sup L,(Finset.range N).sup c,
    fun k => (hd k).smooth,fun k => (hd k).gradient_bound,
    cellVHeat_seam hf hLip h c N,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    exact Finset.le_sup (f := c) (Finset.mem_range.mpr hk)
  · intro k hk t z
    exact ((H k).1 t z).trans (by exact_mod_cast Finset.le_sup (f := C₂) (Finset.mem_range.mpr hk))
  · intro k hk t z
    exact ((H k).2.1 t z).trans (by exact_mod_cast Finset.le_sup (f := C₃) (Finset.mem_range.mpr hk))
  · exact fun k => (H k).2.2.1
  · intro k hk t z
    exact ((H k).2.2.2.1 t z).trans (by exact_mod_cast Finset.le_sup (f := Ct) (Finset.mem_range.mpr hk))
  · intro k hk r hr z
    have hs : Icc (time h k:ℝ) (time h (k+1):ℝ) ⊆ Icc (0:ℝ) (time h (min (k+1) N):ℝ) := by
      rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
      exact fun s hs => ⟨(time h k).coe_nonneg.trans hs.1,hs.2⟩
    exact ((H k).2.2.2.2.1 r (hs hr) z).mono hs
  · intro k hk r hr s hs z y
    have hsub : Icc (time h k:ℝ) (time h (k+1):ℝ) ⊆ Icc (0:ℝ) (time h (min (k+1) N):ℝ) := by
      rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
      exact fun t ht => ⟨(time h k).coe_nonneg.trans ht.1,ht.2⟩
    exact ((H k).2.2.2.2.2.1 r (hsub hr) s (hsub hs) z y).trans (by
      gcongr
      exact_mod_cast Finset.le_sup (f := L) (Finset.mem_range.mpr hk))
  · intro k hk t ht z
    apply (H k).2.2.2.2.2.2 t
    rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
    exact ⟨(time h k).coe_nonneg.trans ht.1,ht.2⟩

theorem cascadeV_eq_control_sup {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (h c : ℕ → ℝ≥0) (N : ℕ) (x : ℝ) :
    cascadeV h c f N 0 x = sSup (objectives (P := P) hm h c f x N) := by
  let sd := cellVHeat_gridData hf hLip h c N
  have hend : cellVHeat h c f N N (time h N) = f := by
    rw [cellVHeat_left hf hLip h c N N le_rfl]
    simp [cascadeVAt,cascadeV]
  have hstart : cellVHeat h c f N 0 0 x = cascadeV h c f N 0 x := by
    have he := congrFun (cellVHeat_left hf hLip h c N 0 (Nat.zero_le N)) x
    simpa only [time_zero,NNReal.coe_zero,cascadeVAt,Nat.sub_zero] using he
  have hu : ∀ v ∈ objectives (P := P) hm h c f x N, v ≤ cascadeV h c f N 0 x := by
    intro v hv
    obtain ⟨α,hap,hab,hv⟩ := hv
    rw [hv]
    have hh := sd.control_upper hB hm hap hab x
    change profit (P := P) B α h c (cellVHeat h c f N N (time h N)) x N ≤
      cellVHeat h c f N 0 0 x at hh
    rwa [hend,hstart] at hh
  have hb : BddAbove (objectives (P := P) hm h c f x N) := ⟨_,hu⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hh := sd.control_lower hB hm x hε
    change ∃ v ∈ objectives (P := P) hm h c (cellVHeat h c f N N (time h N)) x N,
      cellVHeat h c f N 0 0 x-ε ≤ v at hh
    rw [hend,hstart] at hh
    obtain ⟨v,hv,hl⟩ := hh
    have hs := le_csSup hb hv
    linarith
  · exact csSup_le (objectives_nonempty hm h c f x N) hu

end ZeroTemperatureSK.Nonuniform

end
end

end OAI
