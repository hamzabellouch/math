import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.EntryIndex
import OAI.Combinatorics.KMedianRecovery.Geometry.RoundingPrecision

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus

noncomputable def samplingRate : ℝ :=
  NearClients.progressConstant mainKappa ^ 2 * menuConstant mainKappa mainKappa_pos *
    (2:ℝ)^(-(10/(9*mainKappa)+1))

lemma samplingRate_pos : 0 < samplingRate := by
  exact mul_pos (mul_pos (pow_pos (NearClients.progressConstant_pos mainKappa mainKappa_pos) _)
    (menuConstant_pos mainKappa mainKappa_pos)) (Real.rpow_pos_of_pos (by norm_num) _)

lemma samplingBound_eq (m : ℕ) : samplingBound m = samplingRate^m := by
  have hh : (2:ℝ)^(-((10/(9*mainKappa)+1)*m)) =
      ((2:ℝ)^(-(10/(9*mainKappa)+1)))^m := by
    rw [← neg_mul,Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  simp only [samplingBound, samplingRate, hh, mul_pow, pow_mul]

lemma sampling_exponential : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
    Real.exp (-C*m) ≤ (1/2:ℝ)^(2*m) * samplingBound m := by
  let r := (1/2:ℝ)^2 * samplingRate
  have hr : 0 < r := mul_pos (by norm_num) samplingRate_pos
  refine ⟨1+|Real.log r|,by positivity,?_⟩
  intro m
  rw [samplingBound_eq, pow_mul, ← mul_pow]
  change Real.exp (-(1+|Real.log r|)*(m:ℝ)) ≤ r^m
  conv_rhs => rw [← Real.exp_log hr,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hl := neg_abs_le (Real.log r)
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable local instance (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _

theorem rounded_records_success (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (1/2:ℝ)^(2*C.bad.card) * samplingBound C.bad.card ≤ Guided.hitMass
      (update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card))
      (Guided.rounded (mainActual D S Δ C.bad.card) (Sum.inl ()))
      (C.stop hD Δ) (2*C.bad.card) (some State.initial) := by
  classical
  exact (mul_le_mul_of_nonneg_left (C.actual_records_success hD F hOF Δ hΔ hP hm)
    (by positivity)).trans (Guided.rounded_hitMass _ _ _ _ _ _)

end MetricKMedianRecovery.Sampling.Comparison

namespace MetricKMedianRecovery.Guided.FixedDyadic
open FiniteSampling
variable {S A : Type*} [Fintype A] [DecidableEq A]

noncomputable def kernel (p : Kernel S A) (b : ℕ) (default : A) : Kernel S A where
  weight s := Dyadic.weight (p.weight s) b default
  nonneg s := Dyadic.weight_nonneg (p.weight s) b default
  total s := Dyadic.weight_total (p.weight s) (p.nonneg s) (p.total s) b default

noncomputable def draw (p : Kernel S A) (b : ℕ) (default : A) (s : S)
    (bits : Fin b → Bool) : A := Dyadic.draw (p.weight s) (p.nonneg s) (p.total s) b default bits

lemma draw_average (p : Kernel S A) (b : ℕ) (default : A) (s : S) (g : A → ℝ) :
    average (fun bits => g (draw p b default s bits)) =
      ∑ a, (kernel p b default).weight s a * g a := by
  rw [average,Fintype.expect_eq_sum_div_card]
  simpa only [draw,kernel,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
    using Dyadic.draw_average (p.weight s) (p.nonneg s) (p.total s) b default g

noncomputable def actions (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A) :
    (n : ℕ) → S → (Fin n → Fin b → Bool) → (Fin n → A)
  | 0, _, _ => Fin.elim0
  | n+1, s, bits =>
    let a := draw p b default s (bits 0)
    Fin.cons a (actions f p b default n (f s a) (Fin.tail bits))

theorem actions_average (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (g : (Fin n → A) → ℝ) :
    average (fun bits => g (actions f p b default n s bits)) =
      ∑ a : Fin n → A, pathWeight f (kernel p b default).weight n s a * g a := by
  classical
  induction n generalizing s with
  | zero =>
    simp only [actions,average_const,pathWeight,one_mul]
    simp only [Fintype.sum_unique]
    congr 1
  | succ n ih =>
    rw [average_fin_succ,sum_fin_succ]
    simp only [actions,Fin.cons_zero,Fin.tail_cons,pathWeight]
    conv_lhs =>
      arg 1; ext bits
      rw [ih (f s (draw p b default s bits)) (fun seed => g (Fin.cons (draw p b default s bits) seed))]
    rw [draw_average p b default s
      (fun a => ∑ seed : Fin n → A,
        pathWeight f (kernel p b default).weight n (f s a) seed * g (Fin.cons a seed))]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    ring

lemma actions_probability (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (E : (Fin n → A) → Prop) :
    probability (fun bits => E (actions f p b default n s bits)) =
      eventMass f (kernel p b default).weight n s E := by
  classical
  unfold probability
  rw [actions_average f p b default n s (fun a => if E a then 1 else 0)]
  simp only [eventMass,mul_ite,mul_one,mul_zero]

def Precise (f : S → A → S) (p : Kernel S A) (b : ℕ) : ℕ → S → Prop
  | 0, _ => True
  | n+1, s => (∀ a, 0 < p.weight s a → 2 ≤ (2:ℝ)^b * p.weight s a) ∧
      ∀ a, Precise f p b n (f s a)

omit [DecidableEq A] in
lemma precise_mono (f : S → A → S) (p : Kernel S A) {b c : ℕ} (hbc : b ≤ c)
    (n : ℕ) (s : S) (h : Precise f p b n s) : Precise f p c n s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (f s a) (h.2 a)⟩
    intro a ha
    exact (h.1 a ha).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hbc) ha.le)

omit [DecidableEq A] in

theorem exists_precision (f : S → A → S) (p : Kernel S A) (n : ℕ) (s : S) :
    ∃ b, Precise f p b n s := by
  classical
  induction n generalizing s with
  | zero => exact ⟨0,True.intro⟩
  | succ n ih =>
    obtain ⟨b,hb⟩ := Dyadic.exists_precision (p.weight s)
    have hnext : ∀ a, ∃ c, Precise f p c n (f s a) := fun a => ih (f s a)
    choose c hc using hnext
    refine ⟨b+∑ a, c a,?_,?_⟩
    · intro a ha
      exact (hb a ha).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right _ _)) ha.le)
    · intro a
      apply precise_mono f p (n := n) (s := f s a) _ (hc a)
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans
        (Nat.le_add_left _ _)

lemma weight_lower (p : Kernel S A) (b : ℕ) (default : A) (s : S)
    (h : ∀ a, 0 < p.weight s a → 2 ≤ (2:ℝ)^b * p.weight s a) (a : A) :
    (1/2:ℝ)*p.weight s a ≤ (kernel p b default).weight s a := by
  simpa only [kernel,div_eq_mul_inv,one_mul,mul_comm] using
    Dyadic.weight_lower (p.weight s) (p.nonneg s) b default a h

lemma path_lower (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (h : Precise f p b n s) (seed : Fin n → A) :
    (1/2:ℝ)^n * pathWeight f p.weight n s seed ≤
      pathWeight f (kernel p b default).weight n s seed := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    have hh := mul_le_mul (weight_lower p b default s h.1 (seed 0))
      (ih (f s (seed 0)) (h.2 (seed 0)) (Fin.tail seed))
      (mul_nonneg (by positivity) (pathWeight_nonneg f p.weight p.nonneg _ _ _))
      ((kernel p b default).nonneg s (seed 0))
    simpa only [pathWeight,pow_succ,mul_mul_mul_comm,mul_comm,mul_left_comm,mul_assoc] using hh

theorem event_lower (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (h : Precise f p b n s) (E : (Fin n → A) → Prop) :
    (1/2:ℝ)^n * eventMass f p.weight n s E ≤
      probability (fun bits => E (actions f p b default n s bits)) := by
  classical
  rw [actions_probability,eventMass,eventMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro seed _
  split_ifs with he
  · exact path_lower f p b default n s h seed
  · simp only [mul_zero,le_refl]

theorem bounded_fair_realization (f : S → A → S) (p : Kernel S A) (default : A)
    (n : ℕ) (s : S) :
    ∃ b, ∀ E : (Fin n → A) → Prop,
      (1/2:ℝ)^n * eventMass f p.weight n s E ≤
        probability (fun bits => E (actions f p b default n s bits)) := by
  obtain ⟨b,hb⟩ := exists_precision f p n s
  exact ⟨b,fun E => event_lower f p b default n s hb E⟩

end MetricKMedianRecovery.Guided.FixedDyadic

end OAI
