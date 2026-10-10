import Mathlib

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace HardSphere.DyadicSkeleton

abbrev Index := Fin 2 × ℕ × ℕ
abbrev Noise := Index → unitInterval

def law : Measure Noise := Measure.infinitePi (fun _ : Index ↦ volume)
instance : IsProbabilityMeasure law := by unfold law; infer_instance

def uniform (ω : Noise) (j : Fin 2) (ℓ k : ℕ) : ℝ :=
  2 * (ω (j,ℓ,k) : ℝ) - 1

lemma uniform_abs_le (ω : Noise) (j : Fin 2) (ℓ k : ℕ) :
    |uniform ω j ℓ k| ≤ 1 := by
  have h := (ω (j,ℓ,k)).property
  simp only [uniform, abs_le]
  constructor <;> linarith [h.1,h.2]

@[fun_prop] lemma measurable_uniform (j : Fin 2) (ℓ k : ℕ) :
    Measurable (fun ω ↦ uniform ω j ℓ k) := by
  unfold uniform
  fun_prop

def decay : ℝ := (2:ℝ)^(-(1:ℝ)/4)
def cvel : ℝ := (1-decay)/2

lemma decay_pos : 0 < decay := Real.rpow_pos_of_pos (by norm_num) _
lemma decay_lt_one : decay < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
lemma cvel_pos : 0 < cvel := by unfold cvel; linarith [decay_lt_one]

def velocity (ω : Noise) (j : Fin 2) (i : ℕ) : ℝ :=
  cvel * ∑' ℓ : ℕ, decay^ℓ * uniform ω j ℓ (i/2^ℓ)

def position (ω : Noise) (j : Fin 2) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range t, velocity ω j i

lemma summable_velocity (ω : Noise) (j : Fin 2) (i : ℕ) :
    Summable (fun ℓ : ℕ ↦ decay^ℓ * uniform ω j ℓ (i/2^ℓ)) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one decay_pos.le decay_lt_one)
  intro ℓ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg decay_pos.le _)]
  exact (mul_le_mul_of_nonneg_left (uniform_abs_le ω j ℓ _) (pow_nonneg decay_pos.le _)).trans_eq (mul_one _)

lemma velocity_abs_le (ω : Noise) (j : Fin 2) (i : ℕ) :
    |velocity ω j i| ≤ 1/2 := by
  have hsum : |∑' ℓ : ℕ, decay^ℓ * uniform ω j ℓ (i/2^ℓ)| ≤
      ∑' ℓ : ℕ, decay^ℓ := by
    apply (norm_tsum_le_tsum_norm (summable_velocity ω j i).norm).trans
    apply Summable.tsum_le_tsum _ (summable_velocity ω j i).norm
      (summable_geometric_of_lt_one decay_pos.le decay_lt_one)
    intro ℓ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg decay_pos.le _)]
    simpa using mul_le_mul_of_nonneg_left (uniform_abs_le ω j ℓ _) (pow_nonneg decay_pos.le _)
  rw [tsum_geometric_of_lt_one decay_pos.le decay_lt_one] at hsum
  rw [velocity,abs_mul,abs_of_pos cvel_pos]
  calc
    _ ≤ cvel * (1-decay)⁻¹ := mul_le_mul_of_nonneg_left hsum cvel_pos.le
    _ = 1/2 := by
      unfold cvel
      have hd : 1-decay ≠ 0 := ne_of_gt (sub_pos.mpr decay_lt_one)
      field_simp

@[fun_prop] lemma measurable_velocity (j : Fin 2) (i : ℕ) :
    Measurable (fun ω ↦ velocity ω j i) := by
  unfold velocity
  apply Measurable.const_mul
  exact Measurable.tsum (fun ℓ ↦ measurable_const.mul (measurable_uniform j ℓ _))

@[fun_prop] lemma measurable_position (j : Fin 2) (t : ℕ) :
    Measurable (fun ω ↦ position ω j t) := by
  unfold position
  fun_prop

lemma position_succ (ω : Noise) (j : Fin 2) (t : ℕ) :
    position ω j (t+1) = position ω j t + velocity ω j t := by
  exact Finset.sum_range_succ _ _

lemma exists_fresh_block (t k : ℕ) (hk : 0 < k) :
    ∃ ℓ b : ℕ, t ≤ b*2^ℓ ∧ (b+1)*2^ℓ ≤ t+k ∧ k ≤ 4*2^ℓ := by
  by_cases hk1 : k=1
  · subst k
    exact ⟨0,t,by simp,by simp,by norm_num⟩
  have hk2 : 1 ≤ k/2 := by omega
  let ℓ := Nat.log 2 (k/2)
  let d := 2^ℓ
  have hd : 0 < d := by dsimp [d]; positivity
  have hdle : d ≤ k/2 := Nat.pow_log_le_self 2 (by omega)
  have hdgt : k/2 < 2*d := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (k/2)
    simpa only [Nat.pow_succ,Nat.mul_comm] using h
  refine ⟨ℓ,t/d+1,?_,?_,?_⟩
  · change t ≤ (t/d+1)*d
    have h₁ := Nat.mod_lt t hd
    have h₂ := Nat.mod_add_div t d
    nlinarith
  · change (t/d+1+1)*d ≤ t+k
    have h := Nat.div_mul_le_self t d
    have h₂ : 2*d ≤ k := by omega
    nlinarith
  · change k ≤ 4*d
    omega

lemma resample_preserving (q : Index) :
    MeasurePreserving (fun z : Noise × unitInterval ↦ Function.update z.1 q z.2)
      (law.prod volume) law := by
  classical
  refine ⟨measurable_update', ?_⟩
  apply Measure.eq_infinitePi
  intro s A hA
  rw [Measure.map_apply measurable_update' (.pi s.countable_toSet fun i _ ↦ hA i)]
  by_cases hq : q ∈ s
  · have he : (fun z : Noise × unitInterval ↦ Function.update z.1 q z.2) ⁻¹'
        ((s : Set Index).pi A) = ((s.erase q : Set Index).pi A) ×ˢ A q := by
      ext z
      simp only [mem_preimage,Set.mem_pi,Finset.mem_coe,mem_prod,Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun i hi ↦ ?_, ?_⟩
        · simpa [Function.update_of_ne hi.1] using h i hi.2
        · simpa using h q hq
      · rintro ⟨h,h'⟩ i hi
        by_cases hiq : i=q
        · subst i; simpa using h'
        · simpa [Function.update_of_ne hiq] using h i ⟨hiq,hi⟩
    rw [he,Measure.prod_prod,law,Measure.infinitePi_pi _ (fun i _ ↦ hA i)]
    exact Finset.prod_erase_mul s (fun i ↦ volume (A i)) hq
  · have he : (fun z : Noise × unitInterval ↦ Function.update z.1 q z.2) ⁻¹'
        ((s : Set Index).pi A) = ((s : Set Index).pi A) ×ˢ univ := by
      ext z
      simp only [mem_preimage,Set.mem_pi,Finset.mem_coe,mem_prod,mem_univ,and_true]
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      have hiq : i≠q := by intro he; subst i; exact hq hi
      rw [Function.update_of_ne hiq]
    rw [he,Measure.prod_prod,measure_univ,mul_one,law,
      Measure.infinitePi_pi _ (fun i _ ↦ hA i)]

lemma lintegral_resample (q : Index) (f : Noise → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ω ∂law) =
      ∫⁻ ω, ∫⁻ x : unitInterval, f (Function.update ω q x) ∂volume ∂law := by
  rw [← (resample_preserving q).lintegral_comp hf]
  exact lintegral_prod _ (hf.comp measurable_update').aemeasurable

lemma velocity_update_sub (ω : Noise) (j : Fin 2) (ℓ b i : ℕ)
    (x : unitInterval) :
    velocity (Function.update ω (j,ℓ,b) x) j i - velocity ω j i =
      if i/2^ℓ=b then cvel * decay^ℓ * (2*((x:ℝ)-(ω (j,ℓ,b):ℝ))) else 0 := by
  classical
  rw [velocity,velocity,←mul_sub,← (summable_velocity _ j i).tsum_sub
    (summable_velocity ω j i)]
  have he : (fun a ↦ decay^a * uniform (Function.update ω (j,ℓ,b) x) j a (i/2^a) -
      decay^a * uniform ω j a (i/2^a)) =
      (fun a ↦ if a=ℓ then decay^ℓ *
        (if i/2^ℓ=b then 2*((x:ℝ)-(ω (j,ℓ,b):ℝ)) else 0) else 0) := by
    funext a
    by_cases ha : a=ℓ
    · subst a
      by_cases hi : i/2^ℓ=b
      · simp [hi,uniform]
        ring
      · simp [hi,uniform]
    · simp [ha,uniform]
  rw [he,tsum_ite_eq]
  split_ifs <;> ring

lemma position_update_past (ω : Noise) (j : Fin 2) (ℓ b t : ℕ)
    (ht : t ≤ b*2^ℓ) (x : unitInterval) :
    position (Function.update ω (j,ℓ,b) x) j t = position ω j t := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < b*2^ℓ := (Finset.mem_range.mp hi).trans_le ht
  have hn : i/2^ℓ ≠ b := by
    intro he
    have hd := Nat.div_mul_le_self i (2^ℓ)
    rw [he] at hd
    omega
  have h := velocity_update_sub ω j ℓ b i x
  rw [ite_eq_right hn] at h
  linarith

lemma block_filter (ℓ b n : ℕ) (hn : (b+1)*2^ℓ ≤ n) :
    (Finset.range n).filter (fun i ↦ i/2^ℓ=b) =
      Finset.Ico (b*2^ℓ) ((b+1)*2^ℓ) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
  constructor
  · rintro ⟨hi,hd⟩
    have hlo := Nat.div_mul_le_self i (2^ℓ)
    have hhi := Nat.mod_lt i (by positivity : 0 < 2^ℓ)
    have he := Nat.mod_add_div i (2^ℓ)
    rw [hd] at hlo he
    constructor
    · exact hlo
    · nlinarith
  · rintro ⟨hlo,hhi⟩
    exact ⟨hhi.trans_le hn,Nat.div_eq_of_lt_le hlo hhi⟩

lemma position_update_future (ω : Noise) (j : Fin 2) (ℓ b n : ℕ)
    (hn : (b+1)*2^ℓ ≤ n) (x : unitInterval) :
    position (Function.update ω (j,ℓ,b) x) j n - position ω j n =
      (2^ℓ:ℕ) * cvel * decay^ℓ * (2*((x:ℝ)-(ω (j,ℓ,b):ℝ))) := by
  classical
  rw [position,position,← Finset.sum_sub_distrib]
  simp_rw [velocity_update_sub]
  rw [← Finset.sum_filter,block_filter ℓ b n hn]
  simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
  have he : (b+1)*2^ℓ-b*2^ℓ=2^ℓ := by rw [Nat.add_mul,one_mul,Nat.add_sub_cancel_left]
  rw [he]
  ring

lemma position_update_other (ω : Noise) (j j' : Fin 2) (hjj : j' ≠ j)
    (ℓ b n : ℕ) (x : unitInterval) :
    position (Function.update ω (j,ℓ,b) x) j' n = position ω j' n := by
  unfold position velocity
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply tsum_congr
  intro a
  have hn : (j',a,i/2^a) ≠ (j,ℓ,b) := by
    intro h; exact hjj (congrArg Prod.fst h)
  simp only [uniform,Function.update_of_ne hn]

lemma affine_interval_volume (A B y R : ℝ) (hA : 0 < A) :
    volume {x : unitInterval | |A*(x:ℝ)+B-y| ≤ R} ≤ ENNReal.ofReal (2*R/A) := by
  rw [unitInterval.volume_apply]
  have hs : Subtype.val '' {x : unitInterval | |A*(x:ℝ)+B-y| ≤ R} ⊆
      Icc ((y-B-R)/A) ((y-B+R)/A) := by
    rintro z ⟨x,hx,rfl⟩
    change |A*(x:ℝ)+B-y| ≤ R at hx
    have hx' := abs_le.mp hx
    constructor
    · rw [div_le_iff₀ hA]
      nlinarith
    · rw [le_div_iff₀ hA]
      nlinarith
  refine (measure_mono hs).trans_eq ?_
  rw [Real.volume_Icc]
  congr 1
  ring

def coordinateTest (j : Fin 2) (n : ℕ) (y R : ℝ) (ω : Noise) : ℝ≥0∞ :=
  {ω | |position ω j n-y| ≤ R}.indicator (fun _ ↦ 1) ω

@[fun_prop] lemma measurable_coordinateTest (j : Fin 2) (n : ℕ) (y R : ℝ) :
    Measurable (coordinateTest j n y R) := by
  apply measurable_const.indicator
  exact measurableSet_le ((measurable_position j n).sub_const y).abs measurable_const

lemma coordinateTest_update_other (ω : Noise) (j j' : Fin 2) (hjj : j' ≠ j)
    (ℓ b n : ℕ) (y R : ℝ) (x : unitInterval) :
    coordinateTest j' n y R (Function.update ω (j,ℓ,b) x) =
      coordinateTest j' n y R ω := by
  simp only [coordinateTest,Set.indicator_apply,Set.mem_ofPred_eq,
    position_update_other ω j j' hjj ℓ b n x]

lemma coordinateTest_update_past (ω : Noise) (j j' : Fin 2)
    (ℓ b n : ℕ) (hn : n ≤ b*2^ℓ) (y R : ℝ) (x : unitInterval) :
    coordinateTest j' n y R (Function.update ω (j,ℓ,b) x) =
      coordinateTest j' n y R ω := by
  by_cases hjj : j'=j
  · subst j'
    simp only [coordinateTest,Set.indicator_apply,Set.mem_ofPred_eq,
      position_update_past ω j ℓ b n hn x]
  · exact coordinateTest_update_other ω j j' hjj ℓ b n y R x

def freshScale (ℓ : ℕ) : ℝ := (2^ℓ:ℕ) * cvel * decay^ℓ
lemma freshScale_pos (ℓ : ℕ) : 0 < freshScale ℓ := by
  unfold freshScale
  exact mul_pos (mul_pos (by positivity) cvel_pos) (pow_pos decay_pos _)

lemma fresh_coordinate_integral (ω : Noise) (j : Fin 2) (ℓ b n : ℕ)
    (hn : (b+1)*2^ℓ ≤ n) (y R : ℝ) :
    (∫⁻ x : unitInterval, coordinateTest j n y R (Function.update ω (j,ℓ,b) x)) ≤
      ENNReal.ofReal (R/freshScale ℓ) := by
  let A := 2*freshScale ℓ
  let B := position ω j n - 2*freshScale ℓ*(ω (j,ℓ,b):ℝ)
  have he (x : unitInterval) : position (Function.update ω (j,ℓ,b) x) j n =
      A*(x:ℝ)+B := by
    have h := position_update_future ω j ℓ b n hn x
    change _ = freshScale ℓ * (2*((x:ℝ)-(ω (j,ℓ,b):ℝ))) at h
    dsimp only [A,B]
    linarith
  have hm : MeasurableSet {x : unitInterval | |A*(x:ℝ)+B-y| ≤ R} := by
    apply measurableSet_le _ measurable_const
    fun_prop
  simp only [coordinateTest,Set.indicator_apply,Set.mem_ofPred_eq,he]
  change (∫⁻ x : unitInterval,
    {x : unitInterval | |A*(x:ℝ)+B-y| ≤ R}.indicator (fun _ ↦ 1) x) ≤ _
  rw [lintegral_indicator hm]
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
  refine (affine_interval_volume A B y R (mul_pos (by norm_num) (freshScale_pos ℓ))).trans_eq ?_
  congr 1
  dsimp only [A]
  field_simp

lemma fresh_weighted_coordinate (j : Fin 2) (ℓ b n : ℕ)
    (hn : (b+1)*2^ℓ ≤ n) (y R : ℝ) (H : Noise → ℝ≥0∞) (hH : Measurable H)
    (hinv : ∀ ω x, H (Function.update ω (j,ℓ,b) x) = H ω) :
    (∫⁻ ω, H ω * coordinateTest j n y R ω ∂law) ≤
      ENNReal.ofReal (R/freshScale ℓ) * ∫⁻ ω, H ω ∂law := by
  rw [lintegral_resample (j,ℓ,b) (fun ω ↦ H ω * coordinateTest j n y R ω)
    (hH.mul (measurable_coordinateTest j n y R))]
  simp_rw [hinv]
  calc
    _ = ∫⁻ ω, H ω * ∫⁻ x : unitInterval,
        coordinateTest j n y R (Function.update ω (j,ℓ,b) x) ∂volume ∂law := by
      apply lintegral_congr
      intro ω
      exact lintegral_const_mul _ ((measurable_coordinateTest j n y R).comp
        (measurable_update ω))
    _ ≤ ∫⁻ ω, H ω * ENNReal.ofReal (R/freshScale ℓ) ∂law := by
      apply lintegral_mono
      intro ω
      exact mul_le_mul_right (fresh_coordinate_integral ω j ℓ b n hn y R) (H ω)
    _ = _ := by rw [lintegral_mul_const _ hH,mul_comm]

def nearTest (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise) : ℝ≥0∞ :=
  coordinateTest 0 n (y 0) R ω * coordinateTest 1 n (y 1) R ω

@[fun_prop] lemma measurable_nearTest (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) :
    Measurable (nearTest n y R) :=
  (measurable_coordinateTest 0 n (y 0) R).mul (measurable_coordinateTest 1 n (y 1) R)

lemma nearTest_le_one (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise) :
    nearTest n y R ω ≤ 1 := by
  unfold nearTest coordinateTest
  simp only [Set.indicator_apply]
  split_ifs <;> simp_all

def PastInvariant (t : ℕ) (H : Noise → ℝ≥0∞) : Prop :=
  ∀ (j : Fin 2) (ℓ b : ℕ), t ≤ b*2^ℓ → ∀ ω x,
    H (Function.update ω (j,ℓ,b) x) = H ω

lemma nearTest_pastInvariant (n t : ℕ) (hnt : n ≤ t) (y : Fin 2 → ℝ) (R : ℝ) :
    PastInvariant t (nearTest n y R) := by
  intro j ℓ b hb ω x
  simp only [nearTest,coordinateTest_update_past ω j 0 ℓ b n (hnt.trans hb),
    coordinateTest_update_past ω j 1 ℓ b n (hnt.trans hb)]

lemma fresh_weighted_pair (ℓ b n : ℕ) (hn : (b+1)*2^ℓ ≤ n)
    (y : Fin 2 → ℝ) (R : ℝ) (H : Noise → ℝ≥0∞) (hH : Measurable H)
    (hinv : ∀ j : Fin 2, ∀ ω x, H (Function.update ω (j,ℓ,b) x) = H ω) :
    (∫⁻ ω, H ω * nearTest n y R ω ∂law) ≤
      ENNReal.ofReal (R/freshScale ℓ)^2 * ∫⁻ ω, H ω ∂law := by
  let a := ENNReal.ofReal (R/freshScale ℓ)
  calc
    _ = ∫⁻ ω, (H ω * coordinateTest 1 n (y 1) R ω) *
        coordinateTest 0 n (y 0) R ω ∂law := by
      apply lintegral_congr; intro ω; simp only [nearTest]; ring
    _ ≤ a * ∫⁻ ω, H ω * coordinateTest 1 n (y 1) R ω ∂law :=
      fresh_weighted_coordinate 0 ℓ b n hn (y 0) R _
        (hH.mul (measurable_coordinateTest 1 n (y 1) R)) (by
          intro ω x
          rw [hinv 0,coordinateTest_update_other ω 0 1 (by decide)])
    _ ≤ a * (a * ∫⁻ ω, H ω ∂law) :=
      mul_le_mul_right (fresh_weighted_coordinate 1 ℓ b n hn (y 1) R H hH (hinv 1)) a
    _ = _ := by ring

lemma freshScale_eq_rpow (ℓ : ℕ) :
    freshScale ℓ = cvel * ((2:ℝ)^ℓ)^((3:ℝ)/4) := by
  have hd : decay^ℓ = ((2:ℝ)^ℓ)^(-(1:ℝ)/4) := by
    rw [decay,← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [freshScale,Nat.cast_pow,Nat.cast_ofNat,hd]
  calc
    _ = cvel * (((2:ℝ)^ℓ)^((1:ℝ)) * ((2:ℝ)^ℓ)^(-(1:ℝ)/4)) := by
      rw [Real.rpow_one]; ring
    _ = cvel * ((2:ℝ)^ℓ)^((1:ℝ)+(-(1:ℝ)/4)) := by
      rw [Real.rpow_add (by positivity)]
    _ = _ := by norm_num

lemma freshScale_sq (ℓ : ℕ) :
    freshScale ℓ ^ 2 = cvel^2 * ((2:ℝ)^ℓ)^((3:ℝ)/2) := by
  rw [freshScale_eq_rpow,mul_pow,← Real.rpow_mul_natCast (by positivity)]
  norm_num

lemma freshScale_gap_bound (k ℓ : ℕ) (hk : 0 < k) (hkℓ : k ≤ 4*2^ℓ) (R : ℝ) :
    (R/freshScale ℓ)^2 ≤ (16*R^2/cvel^2) * (k:ℝ)^(-(3:ℝ)/2) := by
  have hd : 0 < (2:ℝ)^ℓ := by positivity
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hpow : (k:ℝ)^((3:ℝ)/2) ≤ 16*((2:ℝ)^ℓ)^((3:ℝ)/2) := by
    have hg : (k:ℝ) ≤ 4*(2:ℝ)^ℓ := by exact_mod_cast hkℓ
    calc
      _ ≤ (4*(2:ℝ)^ℓ)^((3:ℝ)/2) :=
        Real.rpow_le_rpow hk'.le hg (by norm_num)
      _ = (4:ℝ)^((3:ℝ)/2) * ((2:ℝ)^ℓ)^((3:ℝ)/2) :=
        Real.mul_rpow (by norm_num) hd.le
      _ ≤ 16 * ((2:ℝ)^ℓ)^((3:ℝ)/2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
          (by norm_num : (3:ℝ)/2 ≤ 2)
        norm_num at h ⊢
  have hc2 : 0 < cvel^2 := sq_pos_of_pos cvel_pos
  have hd2 : 0 < ((2:ℝ)^ℓ)^((3:ℝ)/2) := Real.rpow_pos_of_pos hd _
  have hk2 : 0 < (k:ℝ)^((3:ℝ)/2) := Real.rpow_pos_of_pos hk' _
  rw [div_pow,freshScale_sq]
  rw [show -(3:ℝ)/2 = -((3:ℝ)/2) by ring,Real.rpow_neg hk'.le,← div_eq_mul_inv]
  apply (div_le_div_iff₀ (mul_pos hc2 hd2) hk2).mpr
  calc
    _ ≤ R^2 * (16*((2:ℝ)^ℓ)^((3:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg R)
    _ = _ := by field_simp [ne_of_gt cvel_pos]

end HardSphere.DyadicSkeleton
end
end

end OAI
