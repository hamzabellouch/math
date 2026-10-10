import Mathlib
import OAI.Combinatorics.UniformKServer.ConditionalLaw

namespace OAI

                                   
section

                                                                    
                                                                          
                                                                              
                                                                     
namespace UniformKServer.RankTracking

variable {Ω : Type*} [Fintype Ω]

def average (μ : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, μ ω * X ω

def measurableAt (F : ℕ → Setoid Ω) (t : ℕ) (X : Ω → ℝ) : Prop :=
  ∀ ω ω', (F t).r ω ω' → X ω = X ω'

structure Input (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_total : ∑ ω, weight ω = 1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω ω', (filtration (t + 1)).r ω ω' → (filtration t).r ω ω'
  posterior : ℕ → Ω → ℝ
  filtered : ℕ → Ω → ℝ
  posterior_range : ∀ t ω, posterior t ω ∈ Set.Icc (0 : ℝ) 1
  filtered_range : ∀ t ω, filtered t ω ∈ Set.Icc (0 : ℝ) 1
  posterior_measurable : ∀ t, measurableAt filtration t (posterior t)
  filtering : ∀ t X, measurableAt filtration t X →
    average weight (fun ω => X ω * (filtered (t + 1) ω - posterior t ω)) = 0

noncomputable def reference (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) : ℕ → Ω → ℝ
  | 0, ω => I.posterior 0 ω
  | t + 1, ω =>
    if f (I.posterior (t + 1) ω) ≤ (1 + ξ) * f (reference I f ξ t ω) ∧
       f (reference I f ξ t ω) ≤ (1 + ξ) * f (I.posterior (t + 1) ω)
    then reference I f ξ t ω else I.posterior (t + 1) ω

noncomputable def estimate (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  f (reference I f ξ t ω)

def potential (p r : ℝ) : ℝ := p * (1 - p) + (p - r) ^ 2

def driftBudget (I : Input Ω) (H : ℕ) : ℝ :=
  ∑ t ∈ Finset.range H,
    average I.weight (fun ω => |I.posterior (t + 1) ω - I.filtered (t + 1) ω|)


theorem average_add (μ X Y : Ω → ℝ) :
    average μ (fun ω => X ω + Y ω) = average μ X + average μ Y := by
  simp [average, mul_add, Finset.sum_add_distrib]

theorem average_mono {μ X Y : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (h : ∀ ω, X ω ≤ Y ω) :
    average μ X ≤ average μ Y := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hμ ω)

theorem potential_range {p r : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : potential p r ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hp with ⟨hp, hp'⟩
  rcases hr with ⟨hr, hr'⟩
  constructor
  · exact add_nonneg (mul_nonneg hp (sub_nonneg.mpr hp')) (sq_nonneg _)
  · unfold potential
    have h₁ := mul_nonneg (sub_nonneg.mpr hp') (mul_nonneg hr (sub_nonneg.mpr hr'))
    have h₂ := mul_nonneg hp (mul_nonneg hr (sub_nonneg.mpr hr'))
    have h₃ := mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hr')
    have h₄ := mul_nonneg hp hr
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hp')]

theorem reset_identity (p p' pminus r r' : ℝ) (hr : r' = r ∨ r' = p') :
    potential p' r' + (r' - r)^2 = potential p r +
      (1 - 2*r) * (pminus - p) + (1 - 2*r) * (p' - pminus) := by
  rcases hr with h | h <;> subst r' <;> unfold potential <;> ring

theorem drift_slope {r d : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (1 - 2*r) * d ≤ |d| := by
  have h : |1 - 2*r| ≤ 1 := abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩
  calc
    (1 - 2*r)*d ≤ |(1 - 2*r)*d| := le_abs_self _
    _ = |1 - 2*r| * |d| := abs_mul _ _
    _ ≤ 1 * |d| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = |d| := one_mul _

theorem credit_step (I : Input Ω) (r : ℕ → Ω → ℝ)
    (hrange : ∀ t ω, r t ω ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ t, measurableAt I.filtration t (r t))
    (hstep : ∀ t ω, r (t+1) ω = r t ω ∨ r (t+1) ω = I.posterior (t+1) ω)
    (t : ℕ) :
    average I.weight (fun ω => potential (I.posterior (t+1) ω) (r (t+1) ω)) +
      average I.weight (fun ω => (r (t+1) ω - r t ω)^2) ≤
    average I.weight (fun ω => potential (I.posterior t ω) (r t ω)) +
      average I.weight (fun ω => |I.posterior (t+1) ω - I.filtered (t+1) ω|) := by
  have hmart := I.filtering t (fun ω => 1 - 2*r t ω) (by
    intro ω ω' hω
    change 1 - 2*r t ω = 1 - 2*r t ω'
    rw [hmeas t ω ω' hω])
  rw [← average_add]
  calc
    _ = average I.weight (fun ω => potential (I.posterior t ω) (r t ω) +
        (1-2*r t ω)*(I.filtered (t+1) ω - I.posterior t ω) +
        (1-2*r t ω)*(I.posterior (t+1) ω - I.filtered (t+1) ω)) := by
          congr 1
          funext ω
          exact reset_identity _ _ _ _ _ (hstep t ω)
    _ ≤ average I.weight (fun ω => potential (I.posterior t ω) (r t ω) +
        (1-2*r t ω)*(I.filtered (t+1) ω - I.posterior t ω) +
        |I.posterior (t+1) ω - I.filtered (t+1) ω|) := by
          apply average_mono I.weight_nonneg
          intro ω
          gcongr
          exact drift_slope (hrange t ω)
    _ = _ := by rw [average_add, average_add, hmart, add_zero]

theorem reset_credit (I : Input Ω) (r : ℕ → Ω → ℝ)
    (hrange : ∀ t ω, r t ω ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ t, measurableAt I.filtration t (r t))
    (hstep : ∀ t ω, r (t+1) ω = r t ω ∨ r (t+1) ω = I.posterior (t+1) ω)
    (H : ℕ) :
    (∑ t ∈ Finset.range H, average I.weight (fun ω => (r (t+1) ω - r t ω)^2)) ≤
      driftBudget I H + 1 := by
  have telescope : ∀ H, (∑ t ∈ Finset.range H,
      average I.weight (fun ω => (r (t+1) ω - r t ω)^2)) +
      average I.weight (fun ω => potential (I.posterior H ω) (r H ω)) ≤
      driftBudget I H + average I.weight (fun ω => potential (I.posterior 0 ω) (r 0 ω)) := by
    intro H
    induction H with
    | zero => simp [driftBudget]
    | succ H ih =>
      have hs := credit_step I r hrange hmeas hstep H
      simp only [Finset.sum_range_succ, driftBudget] at *
      linarith
  have hlo : 0 ≤ average I.weight (fun ω => potential (I.posterior H ω) (r H ω)) := by
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (I.weight_nonneg ω)
      (potential_range (I.posterior_range H ω) (hrange H ω)).1
  have hhi : average I.weight (fun ω => potential (I.posterior 0 ω) (r 0 ω)) ≤ 1 := by
    calc
      _ ≤ average I.weight (fun _ => 1) := average_mono I.weight_nonneg
        (fun ω => (potential_range (I.posterior_range 0 ω) (hrange 0 ω)).2)
      _ = 1 := by simp [average, I.weight_total]
  linarith [telescope H]


theorem reference_range (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) :
    ∀ t ω, reference I f ξ t ω ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => exact I.posterior_range 0
  | succ t ih =>
    intro ω
    rw [reference]
    split
    · exact ih ω
    · exact I.posterior_range (t+1) ω

theorem reference_measurable (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) :
    ∀ t, measurableAt I.filtration t (reference I f ξ t) := by
  intro t
  induction t with
  | zero => exact I.posterior_measurable 0
  | succ t ih =>
    intro ω ω' hω
    have hp := I.posterior_measurable (t+1) ω ω' hω
    have hr := ih ω ω' (I.refines t ω ω' hω)
    simp only [reference, hp, hr]

theorem reference_step (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    reference I f ξ (t+1) ω = reference I f ξ t ω ∨
      reference I f ξ (t+1) ω = I.posterior (t+1) ω := by
  rw [reference]
  split <;> simp

theorem square_root_failure_ordered {a b ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hξ : 0 < ξ) (hξ' : ξ < 1/2) (hfail : (1+ξ)*a < b) :
    ξ * |a-b| ≤ 5*(Real.sqrt a - Real.sqrt b)^2 := by
  have ha' := Real.sqrt_nonneg a
  have hb' := Real.sqrt_nonneg b
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hab : a < b := by nlinarith
  have hdiff : 0 ≤ Real.sqrt b - Real.sqrt a := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hab.le)
  have hsum : 0 < Real.sqrt b + Real.sqrt a := by
    have : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by linarith)
    linarith
  have hprod : (Real.sqrt b+Real.sqrt a)*(Real.sqrt b-Real.sqrt a) = b-a := by
    nlinarith
  have hnorm : (Real.sqrt b+Real.sqrt a)^2 ≤ 2*(a+b) := by
    nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt a)]
  have hnorm' := mul_le_mul_of_nonneg_left hnorm hξ.le
  have hsmall := mul_le_mul_of_nonneg_right hξ'.le (sub_nonneg.mpr hab.le)
  have hsq : ξ*(Real.sqrt b+Real.sqrt a)^2 ≤ 5*(b-a) := by
    nlinarith
  have hratio : ξ*(Real.sqrt b+Real.sqrt a) ≤ 5*(Real.sqrt b-Real.sqrt a) := by
    apply (mul_le_mul_iff_right₀ hsum).mp
    nlinarith [hprod]
  have hfin := mul_le_mul_of_nonneg_right hratio hdiff
  rw [abs_of_neg (sub_neg.mpr hab)]
  nlinarith [hprod]

theorem square_root_failure {a b ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hξ : 0 < ξ) (hξ' : ξ < 1/2)
    (hfail : ¬ (a ≤ (1+ξ)*b ∧ b ≤ (1+ξ)*a)) :
    ξ * |a-b| ≤ 5*(Real.sqrt a - Real.sqrt b)^2 := by
  by_cases hab : a ≤ (1+ξ)*b
  · have h : (1+ξ)*a < b := lt_of_not_ge (fun h => hfail ⟨hab, h⟩)
    exact square_root_failure_ordered ha hb hξ hξ' h
  · have h := square_root_failure_ordered hb ha hξ hξ' (lt_of_not_ge hab)
    simpa only [abs_sub_comm b a, sub_sq_comm (Real.sqrt b) (Real.sqrt a)] using h

theorem estimate_spec (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) (hξ : 0 < ξ)
    (hf : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f p) (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹ * f (I.posterior t ω) ≤ estimate I f ξ t ω ∧
      estimate I f ξ t ω ≤ (1+ξ) * f (I.posterior t ω) := by
  have hpos : 0 < 1+ξ := by linarith
  have hself : f (I.posterior t ω) ≤ (1+ξ)*f (I.posterior t ω) := by
    have := hf _ (I.posterior_range t ω)
    nlinarith
  have hsym : f (I.posterior t ω) ≤ (1+ξ)*estimate I f ξ t ω ∧
      estimate I f ξ t ω ≤ (1+ξ)*f (I.posterior t ω) := by
    cases t with
    | zero => simpa [estimate, reference] using And.intro hself hself
    | succ t =>
      simp only [estimate, reference]
      split
      · assumption
      · exact ⟨hself, hself⟩
  constructor
  · have hdiv : f (I.posterior t ω) / (1+ξ) ≤ estimate I f ξ t ω :=
      (div_le_iff₀ hpos).mpr (by nlinarith [hsym.1])
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  · exact hsym.2

theorem estimate_step (I : Input Ω) (f : ℝ → ℝ) (ξ K : ℝ)
    (hξ : 0 < ξ) (hξ' : ξ < 1/2) (hK : 0 ≤ K)
    (hf : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f p)
    (hLip : ∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      |Real.sqrt (f p) - Real.sqrt (f q)| ≤ K * |p - q|)
    (t : ℕ) (ω : Ω) :
    |estimate I f ξ (t+1) ω - estimate I f ξ t ω| ≤
      (5*K^2/ξ)*(reference I f ξ (t+1) ω - reference I f ξ t ω)^2 := by
  have hpos := I.posterior_range (t+1) ω
  have hprev := reference_range I f ξ t ω
  unfold estimate
  rw [reference]
  split_ifs with h
  · simp
  · have hfails := square_root_failure (hf _ hpos) (hf _ hprev) hξ hξ' h
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK (abs_nonneg _))).mpr
      (hLip _ hpos _ hprev)
    simp only [mul_pow, sq_abs] at hsq
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hξ).mpr
    nlinarith


theorem average_mul (μ X : Ω → ℝ) (C : ℝ) :
    average μ (fun ω => C * X ω) = C * average μ X := by
  simp only [average, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Source Lemma lem:rank-tracking, with the absolute constant made explicit
as five times the common squared Lipschitz constant of the square root. -/
theorem relative_tracker (I : Input Ω) (f : ℝ → ℝ) (ξ K : ℝ)
    (hξ : 0 < ξ) (hξ' : ξ < 1/2) (hK : 0 ≤ K)
    (hf : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f p)
    (hLip : ∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      |Real.sqrt (f p) - Real.sqrt (f q)| ≤ K * |p - q|) :
    (∀ t ω, (1+ξ)⁻¹ * f (I.posterior t ω) ≤ estimate I f ξ t ω ∧
      estimate I f ξ t ω ≤ (1+ξ) * f (I.posterior t ω)) ∧
    (∀ H, (∑ t ∈ Finset.range H, average I.weight
      (fun ω => |estimate I f ξ (t+1) ω - estimate I f ξ t ω|)) ≤
      (5*K^2/ξ) * (driftBudget I H + 1)) := by
  constructor
  · exact estimate_spec I f ξ hξ hf
  · intro H
    have hC : 0 ≤ 5*K^2/ξ := div_nonneg (by positivity) hξ.le
    calc
      _ ≤ ∑ t ∈ Finset.range H, (5*K^2/ξ) * average I.weight
          (fun ω => (reference I f ξ (t+1) ω - reference I f ξ t ω)^2) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [← average_mul]
        exact average_mono I.weight_nonneg (estimate_step I f ξ K hξ hξ' hK hf hLip t)
      _ = (5*K^2/ξ) * ∑ t ∈ Finset.range H, average I.weight
          (fun ω => (reference I f ξ (t+1) ω - reference I f ξ t ω)^2) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (reset_credit I (reference I f ξ) (reference_range I f ξ)
          (reference_measurable I f ξ) (reference_step I f ξ) H) hC


/-- The held posterior used for the source's fixed-threshold core flags. -/
noncomputable def absoluteReference (I : Input Ω) (δ : ℝ) : ℕ → Ω → ℝ
  | 0, ω => I.posterior 0 ω
  | t + 1, ω =>
    if |I.posterior (t + 1) ω - absoluteReference I δ t ω| ≤ δ
    then absoluteReference I δ t ω else I.posterior (t + 1) ω

noncomputable def refreshCount (I : Input Ω) (δ : ℝ) (H : ℕ) : ℝ :=
  ∑ t ∈ Finset.range H, average I.weight (fun ω =>
    if absoluteReference I δ (t+1) ω = absoluteReference I δ t ω then 0 else 1)


theorem absoluteReference_range (I : Input Ω) (δ : ℝ) :
    ∀ t ω, absoluteReference I δ t ω ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => exact I.posterior_range 0
  | succ t ih =>
    intro ω
    rw [absoluteReference]
    split
    · exact ih ω
    · exact I.posterior_range (t+1) ω

theorem absoluteReference_measurable (I : Input Ω) (δ : ℝ) :
    ∀ t, measurableAt I.filtration t (absoluteReference I δ t) := by
  intro t
  induction t with
  | zero => exact I.posterior_measurable 0
  | succ t ih =>
    intro ω ω' hω
    have hp := I.posterior_measurable (t+1) ω ω' hω
    have hr := ih ω ω' (I.refines t ω ω' hω)
    simp only [absoluteReference, hp, hr]

theorem absoluteReference_step (I : Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) :
    absoluteReference I δ (t+1) ω = absoluteReference I δ t ω ∨
      absoluteReference I δ (t+1) ω = I.posterior (t+1) ω := by
  rw [absoluteReference]
  split <;> simp

theorem absoluteReference_spec (I : Input Ω) (δ : ℝ) (hδ : 0 ≤ δ) (t : ℕ) (ω : Ω) :
    |I.posterior t ω - absoluteReference I δ t ω| ≤ δ := by
  cases t with
  | zero => simpa [absoluteReference] using hδ
  | succ t =>
    rw [absoluteReference]
    split
    · assumption
    · simpa using hδ

theorem absolute_refresh_charge (I : Input Ω) (δ : ℝ) (hδ : 0 < δ) (t : ℕ) (ω : Ω) :
    (if absoluteReference I δ (t+1) ω = absoluteReference I δ t ω then (0 : ℝ) else 1) ≤
      (δ^2)⁻¹ * (absoluteReference I δ (t+1) ω - absoluteReference I δ t ω)^2 := by
  rw [absoluteReference]
  split_ifs with h hsame
  · positivity
  · simp at hsame
  · positivity
  · have hl : δ < |I.posterior (t+1) ω - absoluteReference I δ t ω| := lt_of_not_ge h
    have hs : δ^2 ≤ (I.posterior (t+1) ω - absoluteReference I δ t ω)^2 := by
      nlinarith [sq_abs (I.posterior (t+1) ω - absoluteReference I δ t ω)]
    have hd : 0 < δ^2 := sq_pos_of_pos hδ
    calc
      1 = (δ^2)⁻¹ * δ^2 := (inv_mul_cancel₀ (ne_of_gt hd)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hd.le)

/-- The fixed absolute threshold part of source Lemma lem:rank-tracking. -/
theorem absolute_tracker (I : Input Ω) (δ : ℝ) (hδ : 0 < δ) :
    (∀ t ω, |I.posterior t ω - absoluteReference I δ t ω| ≤ δ) ∧
    (∀ H, refreshCount I δ H ≤ (δ^2)⁻¹ * (driftBudget I H + 1)) := by
  constructor
  · exact absoluteReference_spec I δ hδ.le
  · intro H
    calc
      _ ≤ ∑ t ∈ Finset.range H, (δ^2)⁻¹ * average I.weight
          (fun ω => (absoluteReference I δ (t+1) ω - absoluteReference I δ t ω)^2) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [← average_mul]
        exact average_mono I.weight_nonneg (absolute_refresh_charge I δ hδ t)
      _ = (δ^2)⁻¹ * ∑ t ∈ Finset.range H, average I.weight
          (fun ω => (absoluteReference I δ (t+1) ω - absoluteReference I δ t ω)^2) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (reset_credit I (absoluteReference I δ) (absoluteReference_range I δ)
          (absoluteReference_measurable I δ) (absoluteReference_step I δ) H)
        (inv_nonneg.mpr (sq_nonneg δ))

end UniformKServer.RankTracking

end



end OAI
