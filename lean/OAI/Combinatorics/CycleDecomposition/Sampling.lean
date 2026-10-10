import Mathlib

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15

section

namespace ErdosGallai.Sampling
open MeasureTheory ProbabilityTheory Finset Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

lemma exp_half_bound : exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  nlinarith [exp_one_lt_d9, exp_pos (1 / 2 : ℝ)]

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

theorem bernoulli_sum_upper_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | 2 * p * s.card ≤ ∑ i ∈ s, X i ω} ≤ exp (-p * s.card / 3) := by
  have hInt : Integrable (fun ω => exp ((1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (2 * p * s.card)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(1 / 2 : ℝ) * (2 * p * s.card)) *
        exp ((s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (-p * s.card + (s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

section ProductSamples
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

noncomputable def sampleMeasure (V : Type cycleUniverse5) [Fintype V] (p : unitInterval) : Measure (V → Bool) :=
  Measure.pi (fun _ : V => bernoulliMeasure true false p)

instance sampleMeasure_probability (p : unitInterval) : IsProbabilityMeasure (sampleMeasure V p) := by
  unfold sampleMeasure
  infer_instance

def sampleVertices (ω : V → Bool) : Finset V := Finset.univ.filter (fun v => ω v = true)

def sampleIndicator (v : V) (ω : V → Bool) : ℝ := if ω v then 1 else 0

lemma sampleIndicator_measurable {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (v : V) : Measurable (sampleIndicator v) :=
  measurable_of_finite _

lemma sampleIndicator_values {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (v : V) (ω : V → Bool) :
    sampleIndicator v ω = 0 ∨ sampleIndicator v ω = 1 := by
  simp only [sampleIndicator]; split <;> simp

lemma sampleIndicator_indep {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) :
    iIndepFun (sampleIndicator (V := V)) (sampleMeasure V p) := by
  exact iIndepFun_pi (X := fun _ : V => fun b : Bool => if b then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma sampleIndicator_integral {V : Type cycleUniverse9} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) (v : V) :
    ∫ ω, sampleIndicator v ω ∂sampleMeasure V p = (p : ℝ) := by
  have hl := (measurePreserving_eval (fun _ : V => bernoulliMeasure true false p) v).hasLaw
  have hi := hl.integral_comp (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  simpa [sampleMeasure, sampleIndicator, integral_bernoulliMeasure] using hi

lemma sampleIndicator_sum (S : Finset V) (ω : V → Bool) :
    (∑ v ∈ S, sampleIndicator v ω) = ((S ∩ sampleVertices ω).card : ℝ) := by
  simp only [sampleIndicator,  Finset.sum_boole]
  congr 2
  ext v
  simp [sampleVertices]

lemma sample_card_lower_tail (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | ((S ∩ sampleVertices ω).card : ℝ) ≤ (p : ℝ) * S.card / 2} ≤
      exp (-(p : ℝ) * S.card / 8) := by
  simpa only [sampleIndicator_sum] using bernoulli_sum_lower_tail S
    sampleIndicator_measurable (sampleIndicator_indep p) sampleIndicator_values
    (p : ℝ) p.property.1 (sampleIndicator_integral p)

lemma sample_card_upper_tail (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | 2 * (p : ℝ) * S.card ≤ ((S ∩ sampleVertices ω).card : ℝ)} ≤
      exp (-(p : ℝ) * S.card / 3) := by
  simpa only [sampleIndicator_sum] using bernoulli_sum_upper_tail S
    sampleIndicator_measurable (sampleIndicator_indep p) sampleIndicator_values
    (p : ℝ) p.property.1 (sampleIndicator_integral p)

lemma sample_miss_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | Disjoint S (sampleVertices ω)} = (1 - (p : ℝ)) ^ S.card := by
  have heq : {ω | Disjoint S (sampleVertices ω)} =
      Set.univ.pi (fun v : V => if v ∈ S then {false} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Finset.disjoint_left, sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · simp only [hv, ↓reduceIte, Set.mem_singleton_iff]
        cases hi : ω v <;> simp_all
      · simp [hv]
    · intro h v hv ht
      have := h v
      simp_all
  rw [heq, Measure.real, sampleMeasure, Measure.pi_pi, ENNReal.toReal_prod]
  have hpv (v : V) :
      ((bernoulliMeasure true false p) (if v ∈ S then {false} else Set.univ)).toReal =
        if v ∈ S then 1 - (p : ℝ) else 1 := by
    by_cases hv : v ∈ S
    · simp only [hv, ↓reduceIte]
      change (bernoulliMeasure true false p).real {false} = _
      exact bernoulliMeasure_real_apply_of_notMem_of_mem p (by simp) (by simp) (by simp)
    · simp [hv]
  simp_rw [hpv]
  simp

lemma sample_miss_bound (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | Disjoint S (sampleVertices ω)} ≤ exp (-(p : ℝ) * S.card) := by
  rw [sample_miss_probability]
  calc
    (1 - (p : ℝ)) ^ S.card ≤ exp (-(p : ℝ)) ^ S.card := by
      apply pow_le_pow_left₀ (sub_nonneg.mpr p.property.2)
      linarith [add_one_le_exp (-(p : ℝ))]
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma sample_contains_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p) {ω | S ⊆ sampleVertices ω} = ENNReal.ofReal (p : ℝ) ^ S.card := by
  have heq : {ω | S ⊆ sampleVertices ω} =
      Set.univ.pi (fun v : V => if v ∈ S then {true} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Finset.subset_iff, sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v
      by_cases hv : v ∈ S <;> simp_all
    · intro h v hv
      simpa [hv] using h v
  rw [heq, sampleMeasure, Measure.pi_pi]
  have hpv (v : V) :
      bernoulliMeasure true false p (if v ∈ S then {true} else Set.univ) =
        if v ∈ S then ENNReal.ofReal (p : ℝ) else 1 := by
    by_cases hv : v ∈ S
    · simp only [hv, ↓reduceIte]
      rw [bernoulliMeasure_apply_of_mem_of_notMem p (by simp) (by simp) (by simp)]
      exact ENNReal.ofReal_coe_nnreal.symm
    · simp [hv]
  simp_rw [hpv]
  simp

lemma sample_contains_real_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | S ⊆ sampleVertices ω} = (p : ℝ) ^ S.card := by
  rw [Measure.real, sample_contains_probability, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal p.property.1]

lemma sample_blocks_independent {I : Type cycleUniverse10} (p : unitInterval) (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepSet (fun i => {ω | S i ⊆ sampleVertices ω}) (sampleMeasure V p) := by
  classical
  rw [iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)]
  intro t
  have heq : (⋂ i ∈ t, {ω | S i ⊆ sampleVertices ω}) =
      {ω | t.biUnion S ⊆ sampleVertices ω} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.biUnion_subset]
  rw [heq, sample_contains_probability, Finset.card_biUnion]
  · simp_rw [sample_contains_probability]
    exact (Finset.prod_pow_eq_pow_sum t (fun i => (S i).card) _).symm
  · intro i _ j _ hij
    exact hS hij

noncomputable def blockIndicator (S : Finset V) : (V → Bool) → ℝ :=
  {ω | S ⊆ sampleVertices ω}.indicator (fun _ => 1)

lemma blockIndicator_values (S : Finset V) (ω : V → Bool) :
    blockIndicator S ω = 0 ∨ blockIndicator S ω = 1 := by
  classical
  by_cases h : S ⊆ sampleVertices ω <;> simp [blockIndicator, h]

lemma blockIndicator_integral (p : unitInterval) (S : Finset V) :
    ∫ ω, blockIndicator S ω ∂sampleMeasure V p = (p : ℝ) ^ S.card := by
  rw [blockIndicator, integral_indicator_const _ MeasurableSet.of_discrete,
    sample_contains_real_probability]
  simp

lemma sample_blocks_lower_tail {I : Type cycleUniverse11} (p : unitInterval) (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) (d : ℕ)
    (hd : ∀ i, (S i).card = d) (t : Finset I) :
    (sampleMeasure V p).real {ω | (∑ i ∈ t, blockIndicator (S i) ω) ≤
      (p : ℝ) ^ d * t.card / 2} ≤ exp (-(p : ℝ) ^ d * t.card / 8) := by
  apply bernoulli_sum_lower_tail t (fun _ => measurable_of_finite _)
    (sample_blocks_independent p S hS).iIndepFun_indicator
    (fun i => blockIndicator_values (S i)) ((p : ℝ) ^ d) (pow_nonneg p.property.1 _)
  intro i
  change (∫ ω, blockIndicator (S i) ω ∂sampleMeasure V p) = _
  rw [blockIndicator_integral, hd]

lemma sample_weight_sum (A : Finset V) (w : V → ℝ) (ω : V → Bool) :
    (∑ v ∈ A ∩ sampleVertices ω, w v) = ∑ v ∈ A, w v * sampleIndicator v ω := by
  rw [← Finset.sum_ite_mem]
  apply Finset.sum_congr rfl
  intro v _
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and, sampleIndicator]
  split <;> simp_all

lemma sample_weight_integral (p : unitInterval) (A : Finset V) (w : V → ℝ) :
    ∫ ω, (∑ v ∈ A ∩ sampleVertices ω, w v) ∂sampleMeasure V p =
      (p : ℝ) * ∑ v ∈ A, w v := by
  simp_rw [sample_weight_sum]
  rw [integral_finsetSum A (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_const_mul, sampleIndicator_integral]
  rw [← Finset.sum_mul, mul_comm]

lemma nonnegative_markov_quarter {Ω : Type cycleUniverse12} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hi : Integrable X μ) (hn : ∀ ω, 0 ≤ X ω) {B : ℝ} (hB : 0 < B)
    (he : ∫ ω, X ω ∂μ ≤ B) : μ.real {ω | 4 * B < X ω} ≤ 1 / 4 := by
  have hb := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hn) hi (4 * B)
  have hm : μ.real {ω | 4 * B < X ω} ≤ μ.real {ω | 4 * B ≤ X ω} :=
    measureReal_mono (fun ω (h : 4 * B < X ω) => h.le)
  nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * B)]

lemma sample_weight_markov (p : unitInterval) (hp : 0 < (p : ℝ))
    (A : Finset V) (w : V → ℝ) (hw : ∀ v ∈ A, 0 ≤ w v)
    {B : ℝ} (hB : 0 < B) (hs : ∑ v ∈ A, w v ≤ B) :
    (sampleMeasure V p).real {ω | 4 * (p : ℝ) * B < ∑ v ∈ A ∩ sampleVertices ω, w v} ≤
      1 / 4 := by
  have ht := nonnegative_markov_quarter (μ := sampleMeasure V p)
    (X := fun ω => ∑ v ∈ A ∩ sampleVertices ω, w v) Integrable.of_finite
    (fun ω => Finset.sum_nonneg (fun v hv => hw v (Finset.mem_inter.mp hv).1))
    (mul_pos hp hB) (by rw [sample_weight_integral]; exact mul_le_mul_of_nonneg_left hs hp.le)
  simpa only [mul_assoc] using ht

theorem exists_small_weighted_hitting_set {I : Type cycleUniverse13} (A : Finset V) (hA : A.Nonempty)
    (good : Finset I) (K : I → Finset V) (hKA : ∀ i ∈ good, K i ⊆ A)
    (w : V → ℝ) (hw : ∀ v ∈ A, 0 ≤ w v) {B d : ℝ}
    (hB : 0 < B) (hs : ∑ v ∈ A, w v ≤ B)
    (hd : ∀ i ∈ good, d ≤ (K i).card)
    (q : unitInterval) (hq : 0 < (q : ℝ))
    (hmiss : (good.card : ℝ) * exp (-(q : ℝ) * d) < 1 / 2) :
    ∃ S : Finset V, S ⊆ A ∧ (S.card : ℝ) ≤ 4 * (q : ℝ) * A.card ∧
      (∑ v ∈ S, w v) ≤ 4 * (q : ℝ) * B ∧ ∀ i ∈ good, ¬Disjoint (K i) S := by
  classical
  let μ := sampleMeasure V q
  let E₁ : Set (V → Bool) := {ω | 4 * (q : ℝ) * A.card < ((A ∩ sampleVertices ω).card : ℝ)}
  let E₂ : Set (V → Bool) := {ω | 4 * (q : ℝ) * B < ∑ v ∈ A ∩ sampleVertices ω, w v}
  let E₃ : Set (V → Bool) := ⋃ i ∈ good, {ω | Disjoint (K i) (sampleVertices ω)}
  have h₁ : μ.real E₁ ≤ 1 / 4 := by
    have ht := sample_weight_markov q hq A (fun _ => (1 : ℝ)) (by simp)
      (show (0 : ℝ) < A.card by exact_mod_cast hA.card_pos) (by simp)
    simpa [μ, E₁] using ht
  have h₂ : μ.real E₂ ≤ 1 / 4 := sample_weight_markov q hq A w hw hB hs
  have h₃ : μ.real E₃ < 1 / 2 := by
    calc
      μ.real E₃ ≤ ∑ i ∈ good, μ.real {ω | Disjoint (K i) (sampleVertices ω)} :=
        measureReal_biUnion_finset_le good _
      _ ≤ ∑ i ∈ good, exp (-(q : ℝ) * d) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sample_miss_bound q (K i)).trans (exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left (hd i hi) (neg_nonpos.mpr hq.le)))
      _ = (good.card : ℝ) * exp (-(q : ℝ) * d) := by simp
      _ < _ := hmiss
  have hf : μ.real (E₁ ∪ E₂ ∪ E₃) < 1 := by
    have ha := measureReal_union_le (μ := μ) (E₁ ∪ E₂) E₃
    have hb := measureReal_union_le (μ := μ) E₁ E₂
    linarith
  have hne : E₁ ∪ E₂ ∪ E₃ ≠ Set.univ := by
    intro h
    rw [h] at hf
    have hu : μ.real Set.univ = 1 := by simp [μ, Measure.real]
    linarith
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hn := hω
  simp only [Set.mem_union, not_or] at hn
  refine ⟨A ∩ sampleVertices ω, Finset.inter_subset_left, le_of_not_gt hn.1.1,
    le_of_not_gt hn.1.2, ?_⟩
  intro i hi hdj
  apply hn.2
  simp only [E₃, Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨i, hi, ?_⟩
  apply Finset.disjoint_left.mpr
  intro v hv hvs
  exact Finset.disjoint_left.mp hdj hv (Finset.mem_inter.mpr ⟨hKA i hi hv, hvs⟩)

end ProductSamples

section FiniteUnion
variable {Ω : Type cycleUniverse14} {I : Type cycleUniverse15} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exists_avoiding_finite_events (s : Finset I) (E : I → Set Ω)
    (h : ∑ i ∈ s, μ.real (E i) < 1) : ∃ ω, ∀ i ∈ s, ω ∉ E i := by
  by_contra hn
  push Not at hn
  have cover : (⋃ i ∈ s, E i) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi, he⟩ := hn ω
    exact ⟨i, hi, he⟩
  have hu := measureReal_biUnion_finset_le (μ := μ) s E
  rw [cover] at hu
  have : μ.real Set.univ = 1 := by simp [Measure.real]
  rw [this] at hu
  linarith

end FiniteUnion
end ErdosGallai.Sampling
end

end OAI
