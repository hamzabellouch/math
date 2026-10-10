import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open Filter MeasureTheory
open scoped BigOperators Topology BoundedContinuousFunction

namespace SharpTerminalLeave

def unitTime (t : ℝ) : ℝ := max 0 (min 1 t)

theorem unitTime_nonneg (t : ℝ) : 0 ≤ unitTime t := le_max_left _ _
theorem unitTime_le_one (t : ℝ) : unitTime t ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)
theorem unitTime_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : unitTime t = t := by
  simp [unitTime, min_eq_right ht.2, max_eq_right ht.1]
theorem continuous_unitTime : Continuous unitTime :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_prod_sub_prod_le_sum {α : Type*} (s : Finset α) (f g : α → ℝ)
    (hf : ∀ a ∈ s, f a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ a ∈ s, g a ∈ Set.Icc (0 : ℝ) 1) :
    |(∏ a ∈ s, f a) - ∏ a ∈ s, g a| ≤ ∑ a ∈ s, |f a - g a| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hfs := fun a (ha : a ∈ s) => hf a (Finset.mem_insert_of_mem ha)
    have hgs := fun a (ha : a ∈ s) => hg a (Finset.mem_insert_of_mem ha)
    have hp : |∏ i ∈ s, f i| ≤ 1 := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun i hi => (hfs i hi).1)]
      exact Finset.prod_le_one₀ (fun index hindex => (hfs index hindex).1)
        (fun index hindex => (hfs index hindex).2)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |(f a - g a) * (∏ i ∈ s, f i) +
          g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by congr 1; ring
      _ ≤ |f a - g a| * |∏ i ∈ s, f i| +
          |g a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
        simpa only [abs_mul] using abs_add_le
          ((f a - g a) * (∏ i ∈ s, f i))
          (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
      _ ≤ |f a - g a| * 1 + 1 * (∑ i ∈ s, |f i - g i|) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        · exact mul_le_mul (by simpa only [abs_of_nonneg hga.1] using hga.2)
            (ih hfs hgs) (abs_nonneg _) zero_le_one
      _ = _ := by ring

section Cavity
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def messageCandidates (H : τ → Finset ι) (e : ι) (parent : Option τ) : Finset τ :=
  Finset.univ.filter (fun T => e ∈ H T ∧ some T ≠ parent)

noncomputable def messageIntegral (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (e : ι) (T : τ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..unitTime t, ∏ f ∈ (H T).erase e, q f (some T) s

noncomputable def cavityOperator (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (e : ι) (parent : Option τ) (t : ℝ) : ℝ :=
  ∏ T ∈ messageCandidates H e parent, (1 - messageIntegral H q e T t)

noncomputable def cavityDepth (H : τ → Finset ι) : ℕ → ι → Option τ → ℝ → ℝ
  | 0 => fun _ _ _ => 1
  | k + 1 => cavityOperator H (cavityDepth H k)

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem continuous_message_integrand (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hq : ∀ e p, Continuous (q e p)) (e : ι) (T : τ) :
    Continuous (fun s => ∏ f ∈ (H T).erase e, q f (some T) s) := by
  exact continuous_finsetProd _ (fun f _ => hq f (some T))

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem continuous_messageIntegral (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hq : ∀ e p, Continuous (q e p)) (e : ι) (T : τ) :
    Continuous (messageIntegral H q e T) := by
  exact (intervalIntegral.continuous_primitive
    (fun a b => (continuous_message_integrand H q hq e T).intervalIntegrable a b) 0).comp
      continuous_unitTime

omit [Fintype ι] in
theorem continuous_cavityOperator (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hq : ∀ e p, Continuous (q e p)) (e : ι) (p : Option τ) :
    Continuous (cavityOperator H q e p) := by
  exact continuous_finsetProd _ (fun T _ =>
    continuous_const.sub (continuous_messageIntegral H q hq e T))

omit [Fintype ι] in
theorem continuous_cavityDepth (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) :
    Continuous (cavityDepth H k e p) := by
  induction k generalizing e p with
  | zero => exact continuous_const
  | succ k ih => exact continuous_cavityOperator H _ ih e p

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem messageIntegral_mem_unit (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hc : ∀ e p, Continuous (q e p))
    (hq : ∀ e p t, q e p t ∈ Set.Icc (0 : ℝ) 1) (e : ι) (T : τ) (t : ℝ) :
    messageIntegral H q e T t ∈ Set.Icc (0 : ℝ) 1 := by
  have ha : ∀ s, 0 ≤ ∏ f ∈ (H T).erase e, q f (some T) s := fun s =>
    Finset.prod_nonneg fun f _ => (hq f (some T) s).1
  have hb : ∀ s, (∏ f ∈ (H T).erase e, q f (some T) s) ≤ 1 := fun s =>
    Finset.prod_le_one₀ (fun edge _ => (hq edge (some T) s).1)
      (fun edge _ => (hq edge (some T) s).2)
  refine ⟨intervalIntegral.integral_nonneg_of_forall (unitTime_nonneg t) ha, ?_⟩
  have hu := intervalIntegral.integral_mono_on (μ := volume) (unitTime_nonneg t)
    ((continuous_message_integrand H q hc e T).intervalIntegrable 0 (unitTime t))
    (continuous_const.intervalIntegrable 0 (unitTime t)) (fun s _ => hb s)
  have : messageIntegral H q e T t ≤ unitTime t := by simpa [messageIntegral] using hu
  exact this.trans (unitTime_le_one t)

omit [Fintype ι] in
theorem cavityOperator_mem_unit (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hc : ∀ e p, Continuous (q e p))
    (hq : ∀ e p t, q e p t ∈ Set.Icc (0 : ℝ) 1) (e : ι) (p : Option τ) (t : ℝ) :
    cavityOperator H q e p t ∈ Set.Icc (0 : ℝ) 1 := by
  have hh : ∀ T, 1 - messageIntegral H q e T t ∈ Set.Icc (0 : ℝ) 1 := by
    intro T
    have h := messageIntegral_mem_unit H q hc hq e T t
    constructor <;> linarith [h.1, h.2]
  exact ⟨Finset.prod_nonneg (fun T _ => (hh T).1),
    Finset.prod_le_one₀ (fun triangle _ => (hh triangle).1)
      (fun triangle _ => (hh triangle).2)⟩

omit [Fintype ι] in
theorem cavityDepth_mem_unit (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) (t : ℝ) :
    cavityDepth H k e p t ∈ Set.Icc (0 : ℝ) 1 := by
  induction k generalizing e p t with
  | zero => exact ⟨zero_le_one, le_rfl⟩
  | succ k ih => exact cavityOperator_mem_unit H _ (continuous_cavityDepth H k) ih e p t

def cavityBranching : ℝ := (Fintype.card τ : ℝ) * Fintype.card ι

omit [DecidableEq ι] [DecidableEq τ] in
theorem cavityBranching_nonneg : 0 ≤ cavityBranching (ι := ι) (τ := τ) := by
  unfold cavityBranching
  positivity

theorem cavityOperator_lipschitz (H : τ → Finset ι)
    (q r : ι → Option τ → ℝ → ℝ)
    (hqc : ∀ e p, Continuous (q e p)) (hrc : ∀ e p, Continuous (r e p))
    (hq : ∀ e p t, q e p t ∈ Set.Icc (0 : ℝ) 1)
    (hr : ∀ e p t, r e p t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ → ℝ) (hbc : Continuous b) (hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ b s)
    (hqr : ∀ e p s, s ∈ Set.Icc (0 : ℝ) 1 → |q e p s - r e p s| ≤ b s)
    (e : ι) (p : Option τ) (t : ℝ) :
    |cavityOperator H q e p t - cavityOperator H r e p t| ≤
      cavityBranching (ι := ι) (τ := τ) * ∫ s in (0 : ℝ)..unitTime t, b s := by
  have ht : ∀ s ∈ Set.Icc (0 : ℝ) (unitTime t), s ∈ Set.Icc (0 : ℝ) 1 :=
    fun s hs => ⟨hs.1, hs.2.trans (unitTime_le_one t)⟩
  have hbi : 0 ≤ ∫ s in (0 : ℝ)..unitTime t, b s := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (unitTime_nonneg t)
      (continuous_const.intervalIntegrable 0 (unitTime t))
      (hbc.intervalIntegrable 0 (unitTime t)) (fun s hs => hb s (ht s hs))
    simpa using h
  have hinner : ∀ T s, s ∈ Set.Icc (0 : ℝ) (unitTime t) →
      |(∏ f ∈ (H T).erase e, q f (some T) s) -
        ∏ f ∈ (H T).erase e, r f (some T) s| ≤ (Fintype.card ι : ℝ) * b s := by
    intro T s hs
    calc
      _ ≤ ∑ f ∈ (H T).erase e, |q f (some T) s - r f (some T) s| :=
        abs_prod_sub_prod_le_sum _ _ _ (fun f _ => hq f (some T) s) (fun f _ => hr f (some T) s)
      _ ≤ ∑ _f ∈ (H T).erase e, b s :=
        Finset.sum_le_sum fun f _ => hqr f (some T) s (ht s hs)
      _ = (((H T).erase e).card : ℝ) * b s := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ ((H T).erase e))
        (hb s (ht s hs))
  have hint : ∀ T, |messageIntegral H q e T t - messageIntegral H r e T t| ≤
      (Fintype.card ι : ℝ) * ∫ s in (0 : ℝ)..unitTime t, b s := by
    intro T
    have hqint := (continuous_message_integrand H q hqc e T).intervalIntegrable (μ := volume) 0 (unitTime t)
    have hrint := (continuous_message_integrand H r hrc e T).intervalIntegrable (μ := volume) 0 (unitTime t)
    rw [messageIntegral, messageIntegral, ← intervalIntegral.integral_sub hqint hrint]
    calc
      _ ≤ ∫ s in (0 : ℝ)..unitTime t,
          |(∏ f ∈ (H T).erase e, q f (some T) s) -
            ∏ f ∈ (H T).erase e, r f (some T) s| :=
        intervalIntegral.abs_integral_le_integral_abs (unitTime_nonneg t)
      _ ≤ ∫ s in (0 : ℝ)..unitTime t, (Fintype.card ι : ℝ) * b s := by
        apply intervalIntegral.integral_mono_on (unitTime_nonneg t)
          (((continuous_message_integrand H q hqc e T).sub
            (continuous_message_integrand H r hrc e T)).abs.intervalIntegrable 0 (unitTime t))
          ((continuous_const.mul hbc).intervalIntegrable 0 (unitTime t))
        exact hinner T
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hqf : ∀ T ∈ messageCandidates H e p,
      1 - messageIntegral H q e T t ∈ Set.Icc (0 : ℝ) 1 := by
    intro T _
    have h := messageIntegral_mem_unit H q hqc hq e T t
    constructor <;> linarith [h.1, h.2]
  have hrf : ∀ T ∈ messageCandidates H e p,
      1 - messageIntegral H r e T t ∈ Set.Icc (0 : ℝ) 1 := by
    intro T _
    have h := messageIntegral_mem_unit H r hrc hr e T t
    constructor <;> linarith [h.1, h.2]
  calc
    _ ≤ ∑ T ∈ messageCandidates H e p,
        |(1 - messageIntegral H q e T t) - (1 - messageIntegral H r e T t)| :=
      abs_prod_sub_prod_le_sum _ _ _ hqf hrf
    _ ≤ ∑ _T ∈ messageCandidates H e p,
        (Fintype.card ι : ℝ) * ∫ s in (0 : ℝ)..unitTime t, b s := by
      apply Finset.sum_le_sum
      intro T _
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hint T
    _ = ((messageCandidates H e p).card : ℝ) *
        ((Fintype.card ι : ℝ) * ∫ s in (0 : ℝ)..unitTime t, b s) := by simp
    _ ≤ (Fintype.card τ : ℝ) *
        ((Fintype.card ι : ℝ) * ∫ s in (0 : ℝ)..unitTime t, b s) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.card_le_univ (messageCandidates H e p)
      · positivity
    _ = _ := by rw [cavityBranching]; ring

theorem cavityDepth_succ_diff (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) (t : ℝ) :
    |cavityDepth H (k + 1) e p t - cavityDepth H k e p t| ≤
      cavityBranching (ι := ι) (τ := τ) ^ k * (unitTime t) ^ k / k.factorial := by
  let M := cavityBranching (ι := ι) (τ := τ)
  have hM : 0 ≤ M := cavityBranching_nonneg
  induction k generalizing e p t with
  | zero =>
    have h := cavityDepth_mem_unit H 1 e p t
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, div_one]
    change |cavityDepth H 1 e p t - 1| ≤ 1
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  | succ k ih =>
    let b : ℝ → ℝ := fun s => M ^ k / (k.factorial : ℝ) * s ^ k
    have hbc : Continuous b := continuous_const.mul (continuous_id.pow k)
    have hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ b s := by
      intro s hs
      exact mul_nonneg (div_nonneg (pow_nonneg hM _) (Nat.cast_nonneg _))
        (pow_nonneg hs.1 _)
    have hd : ∀ e p s, s ∈ Set.Icc (0 : ℝ) 1 →
        |cavityDepth H (k + 1) e p s - cavityDepth H k e p s| ≤ b s := by
      intro e p s hs
      have h := ih e p s
      rw [unitTime_of_mem hs] at h
      simpa only [b, M, div_mul_eq_mul_div] using h
    have h := cavityOperator_lipschitz H (cavityDepth H (k + 1)) (cavityDepth H k)
      (continuous_cavityDepth H (k + 1)) (continuous_cavityDepth H k)
      (cavityDepth_mem_unit H (k + 1)) (cavityDepth_mem_unit H k)
      b hbc hb hd e p t
    change |cavityOperator H (cavityDepth H (k + 1)) e p t -
      cavityOperator H (cavityDepth H k) e p t| ≤ _
    apply h.trans_eq
    simp only [b, intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero k),
      sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    dsimp [M]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

abbrev CavitySpace (ι τ : Type*) := ι → Option τ → (ℝ →ᵇ ℝ)

noncomputable def cavityDepthBCF (H : τ → Finset ι) (k : ℕ) : CavitySpace ι τ :=
  fun e p => BoundedContinuousFunction.mkOfBound
    ⟨cavityDepth H k e p, continuous_cavityDepth H k e p⟩ 1 (by
      intro x y
      change |cavityDepth H k e p x - cavityDepth H k e p y| ≤ 1
      have hx := cavityDepth_mem_unit H k e p x
      have hy := cavityDepth_mem_unit H k e p y
      exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩)

omit [Fintype ι] in
@[simp] theorem cavityDepthBCF_apply (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) (t : ℝ) :
    cavityDepthBCF H k e p t = cavityDepth H k e p t := rfl

theorem cavityDepthBCF_succ_dist (H : τ → Finset ι) (k : ℕ) :
    dist (cavityDepthBCF H k) (cavityDepthBCF H (k + 1)) ≤
      cavityBranching (ι := ι) (τ := τ) ^ k / k.factorial := by
  have hb : 0 ≤ cavityBranching (ι := ι) (τ := τ) ^ k / (k.factorial : ℝ) :=
    div_nonneg (pow_nonneg cavityBranching_nonneg _) (Nat.cast_nonneg _)
  rw [dist_comm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro e
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro p
  apply (BoundedContinuousFunction.norm_le hb).mpr
  intro t
  change |cavityDepth H (k + 1) e p t - cavityDepth H k e p t| ≤ _
  apply (cavityDepth_succ_diff H k e p t).trans
  calc
    _ = (cavityBranching (ι := ι) (τ := τ) ^ k / k.factorial) * (unitTime t) ^ k := by ring
    _ ≤ (cavityBranching (ι := ι) (τ := τ) ^ k / k.factorial) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (unitTime_nonneg t) (unitTime_le_one t)) hb
    _ = _ := mul_one _

theorem cavityDepthBCF_cauchy (H : τ → Finset ι) : CauchySeq (cavityDepthBCF H) :=
  cauchySeq_of_dist_le_of_summable _ (cavityDepthBCF_succ_dist H)
    (Real.summable_pow_div_factorial _)

noncomputable def cavityLimitBCF (H : τ → Finset ι) : CavitySpace ι τ :=
  (cauchySeq_tendsto_of_complete (cavityDepthBCF_cauchy H)).choose

theorem tendsto_cavityDepthBCF (H : τ → Finset ι) :
    Tendsto (cavityDepthBCF H) atTop (𝓝 (cavityLimitBCF H)) :=
  (cauchySeq_tendsto_of_complete (cavityDepthBCF_cauchy H)).choose_spec

noncomputable def cavityLimit (H : τ → Finset ι) (e : ι) (p : Option τ) (t : ℝ) : ℝ :=
  cavityLimitBCF H e p t

theorem continuous_cavityLimit (H : τ → Finset ι) (e : ι) (p : Option τ) :
    Continuous (cavityLimit H e p) := (cavityLimitBCF H e p).continuous

theorem tendsto_cavityDepth (H : τ → Finset ι) (e : ι) (p : Option τ) (t : ℝ) :
    Tendsto (fun k => cavityDepth H k e p t) atTop (𝓝 (cavityLimit H e p t)) := by
  have h := ((tendsto_pi_nhds.mp (tendsto_cavityDepthBCF H)) e)
  have h' := (tendsto_pi_nhds.mp h) p
  exact ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto
    (cavityLimitBCF H e p)).comp h'

theorem cavityLimit_mem_unit (H : τ → Finset ι) (e : ι) (p : Option τ) (t : ℝ) :
    cavityLimit H e p t ∈ Set.Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (tendsto_cavityDepth H e p t)
    (Eventually.of_forall fun k => cavityDepth_mem_unit H k e p t)

omit [DecidableEq ι] [DecidableEq τ] in

theorem cavitySpace_eval_sub_le (q r : CavitySpace ι τ) (e : ι) (p : Option τ) (t : ℝ) :
    |q e p t - r e p t| ≤ ‖q - r‖ := by
  exact ((BoundedContinuousFunction.norm_coe_le_norm (q e p - r e p) t).trans
    (norm_le_pi_norm ((q - r) e) p)).trans (norm_le_pi_norm (q - r) e)

theorem cavityLimit_product (H : τ → Finset ι) (e : ι) (p : Option τ) (t : ℝ) :
    cavityLimit H e p t = cavityOperator H (cavityLimit H) e p t := by
  let d : ℕ → ℝ := fun k => ‖cavityDepthBCF H k - cavityLimitBCF H‖
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_cavityDepthBCF H).sub (tendsto_const_nhds (x := cavityLimitBCF H))).norm
  have hbound : ∀ k,
      |cavityDepth H (k + 1) e p t - cavityOperator H (cavityLimit H) e p t| ≤
        cavityBranching (ι := ι) (τ := τ) * (unitTime t * d k) := by
    intro k
    have h := cavityOperator_lipschitz H (cavityDepth H k) (cavityLimit H)
      (continuous_cavityDepth H k) (continuous_cavityLimit H)
      (cavityDepth_mem_unit H k) (cavityLimit_mem_unit H)
      (fun _ => d k) continuous_const (fun _ _ => norm_nonneg _)
      (fun f o s _ => cavitySpace_eval_sub_le (cavityDepthBCF H k) (cavityLimitBCF H) f o s)
      e p t
    simpa only [cavityDepth, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h
  have herr : Tendsto (fun k =>
      |cavityDepth H (k + 1) e p t - cavityOperator H (cavityLimit H) e p t|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) hbound
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.mul hd)
  have hop : Tendsto (fun k => cavityDepth H (k + 1) e p t) atTop
      (𝓝 (cavityOperator H (cavityLimit H) e p t)) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    simpa only [Real.dist_eq] using herr
  exact tendsto_nhds_unique ((tendsto_cavityDepth H e p t).comp
    (tendsto_add_atTop_nat 1)) hop

omit [Fintype ι] in
@[simp] theorem cavityDepth_zero_time (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) :
    cavityDepth H k e p 0 = 1 := by
  cases k <;> simp [cavityDepth, cavityOperator, messageIntegral, unitTime]

@[simp] theorem cavityLimit_zero_time (H : τ → Finset ι) (e : ι) (p : Option τ) :
    cavityLimit H e p 0 = 1 := by
  apply tendsto_nhds_unique (tendsto_cavityDepth H e p 0)
  simpa only [cavityDepth_zero_time] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
    atTop (𝓝 1))

omit [Fintype ι] in
theorem messageCandidates_omission (H : τ → Finset ι) (e : ι) (T : τ) :
    messageCandidates H e (some T) = (messageCandidates H e none).erase T := by
  ext U
  simp [messageCandidates, and_comm]

theorem cavityLimit_omission (H : τ → Finset ι) (e : ι) (T : τ)
    (he : e ∈ H T) (t : ℝ) :
    cavityLimit H e none t = cavityLimit H e (some T) t *
      (1 - messageIntegral H (cavityLimit H) e T t) := by
  rw [cavityLimit_product H e none t, cavityLimit_product H e (some T) t]
  unfold cavityOperator
  rw [messageCandidates_omission]
  exact (Finset.prod_erase_mul _ _ (by simp [messageCandidates, he])).symm

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem messageIntegral_le_time (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hc : ∀ e p, Continuous (q e p))
    (hq : ∀ e p t, q e p t ∈ Set.Icc (0 : ℝ) 1) (e : ι) (T : τ) (t : ℝ) :
    messageIntegral H q e T t ≤ unitTime t := by
  have hu := intervalIntegral.integral_mono_on (μ := volume) (unitTime_nonneg t)
    ((continuous_message_integrand H q hc e T).intervalIntegrable 0 (unitTime t))
    (continuous_const.intervalIntegrable 0 (unitTime t)) (fun s _ =>
      Finset.prod_le_one₀ (fun edge _ => (hq edge (some T) s).1)
        (fun edge _ => (hq edge (some T) s).2))
  simpa [messageIntegral] using hu

theorem cavityLimit_factor_pos (H : τ → Finset ι) (e : ι) (T : τ)
    {t : ℝ} (ht : t < 1) :
    0 < 1 - messageIntegral H (cavityLimit H) e T t := by
  have hb := messageIntegral_le_time H (cavityLimit H) (continuous_cavityLimit H)
    (cavityLimit_mem_unit H) e T t
  have htime : unitTime t < 1 := by
    exact max_lt zero_lt_one ((min_le_right 1 t).trans_lt ht)
  linarith

theorem cavityLimit_pos (H : τ → Finset ι) (e : ι) (p : Option τ)
    {t : ℝ} (ht : t < 1) : 0 < cavityLimit H e p t := by
  rw [cavityLimit_product]
  exact Finset.prod_pos (fun T _ => cavityLimit_factor_pos H e T ht)

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem messageIntegral_hasDerivAt (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hc : ∀ e p, Continuous (q e p))
    (e : ι) (T : τ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (messageIntegral H q e T)
      (∏ f ∈ (H T).erase e, q f (some T) t) t := by
  have hcont := continuous_message_integrand H q hc e T
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 t) hcont.stronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  simp only [messageIntegral, unitTime_of_mem ⟨le_of_lt hx.1, le_of_lt hx.2⟩]

theorem cavityLimit_hasDerivAt (H : τ → Finset ι) (e : ι) (p : Option τ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (cavityLimit H e p)
      (-cavityLimit H e p t *
        ∑ T ∈ messageCandidates H e p,
          (∏ f ∈ (H T).erase e, cavityLimit H f (some T) t) /
            (1 - messageIntegral H (cavityLimit H) e T t)) t := by
  let F : τ → ℝ → ℝ := fun T s => 1 - messageIntegral H (cavityLimit H) e T s
  let J : τ → ℝ := fun T => ∏ f ∈ (H T).erase e, cavityLimit H f (some T) t
  have hF : ∀ T, HasDerivAt (F T) (-J T) t := by
    intro T
    convert (hasDerivAt_const t (1 : ℝ)).sub
      (messageIntegral_hasDerivAt H (cavityLimit H) (continuous_cavityLimit H) e T ht) using 1
    simp only [J, zero_sub]
  have hd := HasDerivAt.finsetProd (u := messageCandidates H e p) (fun T _ => hF T)
  have heq : (∏ T ∈ messageCandidates H e p, F T) = cavityLimit H e p := by
    funext s
    simpa only [Finset.prod_apply, cavityOperator, F] using (cavityLimit_product H e p s).symm
  rw [heq] at hd
  convert hd using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hc : cavityLimit H e p t =
      (∏ U ∈ (messageCandidates H e p).erase T, F U t) * F T t := by
    rw [cavityLimit_product]
    exact (Finset.prod_erase_mul _ _ hT).symm
  have hp : F T t ≠ 0 := ne_of_gt (cavityLimit_factor_pos H e T ht.2)
  simp only [smul_eq_mul]
  change -cavityLimit H e p t * (J T / F T t) = _
  rw [hc]
  field_simp

noncomputable def cavityTime (D s : ℝ) : ℝ := (Real.exp (2 * s) - 1) / (2 * D)

noncomputable def cavityLog (H : τ → Finset ι) (D : ℝ) (e : ι) (s : ℝ) : ℝ :=
  Real.log (cavityLimit H e none (cavityTime D s)) + s

noncomputable def cavityMessage (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ) (s : ℝ) : ℝ :=
  messageIntegral H (cavityLimit H) e T (cavityTime D s)

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem cavityTime_hasDerivAt (D s : ℝ) :
    HasDerivAt (cavityTime D) (Real.exp (2 * s) / D) s := by
  have hh := (((hasDerivAt_id s).const_mul 2).exp.sub_const 1).div_const (2 * D)
  convert hh using 1 <;> (try rfl)
  simp only [id_eq, mul_one]
  ring

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
@[simp] theorem cavityTime_zero (D : ℝ) : cavityTime D 0 = 0 := by
  simp [cavityTime]

theorem cavityLog_zero (H : τ → Finset ι) (D : ℝ) (e : ι) : cavityLog H D e 0 = 0 := by
  simp [cavityLog, cavityTime, cavityLimit_zero_time]

theorem cavityLog_exp (H : τ → Finset ι) (D : ℝ) (e : ι) {s : ℝ}
    (ht : cavityTime D s < 1) :
    cavityLimit H e none (cavityTime D s) = Real.exp (cavityLog H D e s - s) := by
  simp only [cavityLog, add_sub_cancel_right]
  exact (Real.exp_log (cavityLimit_pos H e none ht)).symm

theorem cavityLog_parent (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ)
    (he : e ∈ H T) {s : ℝ} (ht : cavityTime D s < 1) :
    cavityLimit H e (some T) (cavityTime D s) =
      Real.exp (cavityLog H D e s - s) / (1 - cavityMessage H D e T s) := by
  apply (eq_div_iff (ne_of_gt (cavityLimit_factor_pos H e T ht))).mpr
  simpa only [cavityMessage, cavityLog_exp H D e ht] using
    (cavityLimit_omission H e T he (cavityTime D s)).symm

theorem cavityLog_hasDerivAt (H : τ → Finset ι) (D : ℝ) (e : ι)
    {s : ℝ} (ht : cavityTime D s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (cavityLog H D e)
      (1 - Real.exp (2 * s) / D *
        ∑ T ∈ messageCandidates H e none,
          (∏ f ∈ (H T).erase e, cavityLimit H f (some T) (cavityTime D s)) /
            (1 - cavityMessage H D e T s)) s := by
  have hp := cavityLimit_pos H e none ht.2
  have hh := ((cavityLimit_hasDerivAt H e none ht).comp s (cavityTime_hasDerivAt D s)).log hp.ne'
  have hh' := hh.add (hasDerivAt_id s)
  convert hh' using 1 <;> try rfl
  dsimp only [Function.comp_apply, cavityMessage]
  field_simp
  ring

theorem cavityMessage_hasDerivAt (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ)
    {s : ℝ} (ht : cavityTime D s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (cavityMessage H D e T)
      (Real.exp (2 * s) / D *
        ∏ f ∈ (H T).erase e, cavityLimit H f (some T) (cavityTime D s)) s := by
  convert (messageIntegral_hasDerivAt H (cavityLimit H) (continuous_cavityLimit H) e T ht).comp s
    (cavityTime_hasDerivAt D s) using 1 <;> try rfl
  ring

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in

theorem triangle_children {H : τ → Finset ι} {e : ι} {T : τ}
    (hcard : (H T).card = 3) (he : e ∈ H T) :
    ∃ f g, f ≠ g ∧ (H T).erase e = {f, g} ∧ f ∈ H T ∧ g ∈ H T := by
  have hh : ((H T).erase e).card = 2 := by
    rw [Finset.card_erase_of_mem he, hcard]
  rcases Finset.card_eq_two.mp hh with ⟨f, g, hfg, hset⟩
  refine ⟨f, g, hfg, hset, ?_, ?_⟩
  · have hm : f ∈ (H T).erase e := by rw [hset]; simp
    exact Finset.mem_of_mem_erase hm
  · have hm : g ∈ (H T).erase e := by rw [hset]; simp
    exact Finset.mem_of_mem_erase hm

theorem cavity_triangle_summand (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ)
    {f g : ι} (hfg : f ≠ g) (hchildren : (H T).erase e = {f, g})
    (hf : f ∈ H T) (hg : g ∈ H T) {s : ℝ} (ht : cavityTime D s < 1) :
    Real.exp (2 * s) *
        ((∏ u ∈ (H T).erase e, cavityLimit H u (some T) (cavityTime D s)) /
          (1 - cavityMessage H D e T s)) =
      Real.exp (cavityLog H D f s + cavityLog H D g s) /
        ((1 - cavityMessage H D e T s) * (1 - cavityMessage H D f T s) *
          (1 - cavityMessage H D g T s)) := by
  have he0 := (cavityLimit_factor_pos H e T ht).ne'
  have hf0 := (cavityLimit_factor_pos H f T ht).ne'
  have hg0 := (cavityLimit_factor_pos H g T ht).ne'
  rw [hchildren, Finset.prod_pair hfg, cavityLog_parent H D f T hf ht,
    cavityLog_parent H D g T hg ht]
  have heq : Real.exp (2 * s) * (Real.exp (cavityLog H D f s - s) *
      Real.exp (cavityLog H D g s - s)) =
      Real.exp (cavityLog H D f s + cavityLog H D g s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  dsimp only [cavityMessage] at *
  field_simp
  nlinarith [heq]

theorem cavity_triangle_message_summand (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ)
    {f g : ι} (hfg : f ≠ g) (hchildren : (H T).erase e = {f, g})
    (hf : f ∈ H T) (hg : g ∈ H T) {s : ℝ} (ht : cavityTime D s < 1) :
    Real.exp (2 * s) *
        (∏ u ∈ (H T).erase e, cavityLimit H u (some T) (cavityTime D s)) =
      Real.exp (cavityLog H D f s + cavityLog H D g s) /
        ((1 - cavityMessage H D f T s) * (1 - cavityMessage H D g T s)) := by
  have hf0 := (cavityLimit_factor_pos H f T ht).ne'
  have hg0 := (cavityLimit_factor_pos H g T ht).ne'
  rw [hchildren, Finset.prod_pair hfg, cavityLog_parent H D f T hf ht,
    cavityLog_parent H D g T hg ht]
  have heq : Real.exp (2 * s) * (Real.exp (cavityLog H D f s - s) *
      Real.exp (cavityLog H D g s - s)) =
      Real.exp (cavityLog H D f s + cavityLog H D g s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  dsimp only [cavityMessage] at *
  field_simp
  nlinarith [heq]

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem continuous_cavityTime (D : ℝ) : Continuous (cavityTime D) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const |>.div_const _

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem cavityTime_mono {D : ℝ} (hD : 0 < D) : Monotone (cavityTime D) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sub_le_sub_right (Real.exp_le_exp.mpr (by linarith)) _

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem cavityTime_pos {D s : ℝ} (hD : 0 < D) (hs : 0 < s) : 0 < cavityTime D s := by
  apply div_pos _ (by positivity)
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))

theorem continuous_cavityMessage (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ) :
    Continuous (cavityMessage H D e T) :=
  (continuous_messageIntegral H (cavityLimit H) (continuous_cavityLimit H) e T).comp
    (continuous_cavityTime D)

@[simp] theorem cavityMessage_zero (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ) :
    cavityMessage H D e T 0 = 0 := by
  simp [cavityMessage, messageIntegral, unitTime]

theorem cavityMessage_nonneg (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ) (s : ℝ) :
    0 ≤ cavityMessage H D e T s :=
  (messageIntegral_mem_unit H (cavityLimit H) (continuous_cavityLimit H)
    (cavityLimit_mem_unit H) e T (cavityTime D s)).1

theorem continuousOn_cavityLog (H : τ → Finset ι) {D S : ℝ}
    (hD : 0 < D) (hS : cavityTime D S < 1) (e : ι) :
    ContinuousOn (cavityLog H D e) (Set.Icc 0 S) := by
  apply ContinuousOn.add _ continuousOn_id
  exact ((continuous_cavityLimit H e none).comp (continuous_cavityTime D)).continuousOn.log
    (fun s hs => (cavityLimit_pos H e none ((cavityTime_mono hD hs.2).trans_lt hS)).ne')

end Cavity
end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
