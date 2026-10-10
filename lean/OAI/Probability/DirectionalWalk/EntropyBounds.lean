import OAI.Probability.DirectionalWalk.EntropyTransforms

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma geometric_comparison_sum (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∑' n : ℕ, ENNReal.ofReal ((1-r)*r^n)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr0.le n))
    ((summable_geometric_of_lt_one hr0.le hr1).mul_left (1-r)),tsum_mul_left,
    tsum_geometric_of_lt_one hr0.le hr1]
  simp [ne_of_gt (sub_pos.mpr hr1)]

lemma geometric_comparison_cost (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    -Real.log (ENNReal.ofReal ((1-r)*r^n)).toReal = -Real.log (1-r) - n*Real.log r := by
  rw [ENNReal.toReal_ofReal (by positivity),Real.log_mul (by linarith) (pow_ne_zero _ hr0.ne'),Real.log_pow]
  ring

lemma entropy_nat_moment (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun k : ℕ => (k : ℝ)) μ) (a : ℝ) (ha : 0 < a)
    (hmean : (∫ k : ℕ, (k : ℝ) ∂μ) ≤ a) :
    Integrable (atomInfo μ) μ ∧ discreteEntropy μ ≤ 1 + Real.log (a+1) := by
  let r := a/(a+1)
  have ha1 : 0 < a+1 := by linarith
  have hr0 : 0 < r := div_pos ha ha1
  have hr1 : r < 1 := (div_lt_one ha1).mpr (by linarith)
  let q := fun n : ℕ => ENNReal.ofReal ((1-r)*r^n)
  have hq : (∑' n, q n) = 1 := geometric_comparison_sum r hr0 hr1
  have hq0 : ∀ n, q n ≠ 0 := by intro n; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hcost : Integrable (fun n => -Real.log (q n).toReal) μ := by
    simp only [q,geometric_comparison_cost r hr0 hr1]
    exact (integrable_const _).sub (hi.mul_const _)
  refine ⟨integrable_atomInfo_of_comparison μ q hq0 (by rw [hq]; simp) hcost, ?_⟩
  have hb := discreteEntropy_le_comparison μ q hq0 (by rw [hq]; simp) hcost
  rw [hq,ENNReal.toReal_one,add_sub_cancel_right] at hb
  simp only [q,geometric_comparison_cost r hr0 hr1] at hb
  rw [integral_sub (integrable_const _) (hi.mul_const _),integral_const,probReal_univ,
    smul_eq_mul,one_mul,integral_mul_const] at hb
  have he : 1-r = (a+1)⁻¹ := by dsimp [r]; field_simp; ring
  have hl : -Real.log r = Real.log (1+1/a) := by
    rw [← Real.log_inv]
    congr 1
    dsimp [r]
    field_simp
  have hlog : 0 ≤ Real.log (1+1/a) := Real.log_nonneg (by
    have hh : 0 ≤ 1/a := by positivity
    linarith)
  have hlog' : Real.log (1+1/a) ≤ 1/a := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+1/a by positivity)
    linarith
  rw [he,Real.log_inv] at hb
  have hh : (∫ k : ℕ, (k : ℝ) ∂μ) * Real.log (1+1/a) ≤ 1 := by
    calc
      _ ≤ a * Real.log (1+1/a) := mul_le_mul_of_nonneg_right hmean hlog
      _ ≤ a * (1/a) := mul_le_mul_of_nonneg_left hlog' ha.le
      _ = 1 := by field_simp
  have heq : -(∫ k : ℕ, (k : ℝ) ∂μ) * Real.log r =
      (∫ k : ℕ, (k : ℝ) ∂μ) * Real.log (1+1/a) := by rw [← hl]; ring
  linarith

lemma entropy_finite (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] :
    Integrable (atomInfo μ) μ ∧ discreteEntropy μ ≤ Real.log (Fintype.card α) := by
  let q := fun _ : α => (Fintype.card α : ℝ≥0∞)⁻¹
  have hc : Fintype.card α ≠ 0 := (Fintype.card_pos).ne'
  have hq : (∑' x, q x) = 1 := by
    simp only [q,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hc) (by finiteness)
  have hq0 : ∀ x, q x ≠ 0 := by intro x; simp [q]
  have hcost : (fun x => -Real.log (q x).toReal) = fun _ => Real.log (Fintype.card α) := by
    funext x
    simp [q,ENNReal.toReal_inv,Real.log_inv]
  refine ⟨integrable_atomInfo_of_comparison μ q hq0 (by rw [hq]; simp)
    (by rw [hcost]; exact integrable_const _), ?_⟩
  have hh := discreteEntropy_le_comparison μ q hq0 (by rw [hq]; simp)
    (by rw [hcost]; exact integrable_const _)
  simpa only [hcost,hq,integral_const,probReal_univ,smul_eq_mul,one_mul,ENNReal.toReal_one,
    add_sub_cancel_right] using hh

lemma entropyOf_pair_le {Ω α β : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β)
    (hX : Integrable (informationOf μ X) μ) (hY : Integrable (informationOf μ Y) μ) :
    entropyOf μ (fun ω => (X ω,Y ω)) ≤ entropyOf μ X + entropyOf μ Y := by
  rw [entropyOf_pair_chain μ X Y hX (integrable_conditionedInformation μ Y X hY)]
  exact add_le_add le_rfl (conditionedEntropy_le_entropyOf μ Y X hY)

lemma entropyOf_nat_moment {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℕ)
    (hi : Integrable (fun ω => (X ω : ℝ)) μ) (a : ℝ) (ha : 0 < a)
    (hmean : (∫ ω, (X ω : ℝ) ∂μ) ≤ a) :
    Integrable (informationOf μ X) μ ∧ entropyOf μ X ≤ 1+Real.log (a+1) := by
  have : IsProbabilityMeasure (μ.map X) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hi' : Integrable (fun n : ℕ => (n : ℝ)) (μ.map X) :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr hi
  have hmean' : (∫ n : ℕ, (n : ℝ) ∂μ.map X) ≤ a := by
    rwa [integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]
  have hh := entropy_nat_moment (μ.map X) hi' a ha hmean'
  exact ⟨(integrable_informationOf_iff μ X).mpr hh.1, (entropyOf_eq_discreteEntropy μ X) ▸ hh.2⟩

lemma entropyOf_finite {Ω α : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) :
    Integrable (informationOf μ X) μ ∧ entropyOf μ X ≤ Real.log (Fintype.card α) := by
  have : IsProbabilityMeasure (μ.map X) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hh := entropy_finite α (μ.map X)
  exact ⟨(integrable_informationOf_iff μ X).mpr hh.1, (entropyOf_eq_discreteEntropy μ X) ▸ hh.2⟩

lemma entropyOf_int_moment {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℤ)
    (hi : Integrable (fun ω => |(X ω : ℝ)|) μ) (a : ℝ) (ha : 0 < a)
    (hmean : (∫ ω, |(X ω : ℝ)| ∂μ) ≤ a) :
    Integrable (informationOf μ X) μ ∧ entropyOf μ X ≤ 1+Real.log 2+Real.log (a+1) := by
  let f : ℤ → ℕ × Bool := fun z => (z.natAbs,decide (z < 0))
  have hf : Function.Injective f := by
    intro x y h
    have h0 := (Prod.mk.inj h).1
    have h1 := (Prod.mk.inj h).2
    have hs : (x < 0) ↔ (y < 0) := by simpa using h1
    rcases Int.natAbs_eq_natAbs_iff.mp h0 with h0 | h0
    · exact h0
    · omega
  have habs : (fun ω => ((X ω).natAbs : ℝ)) = fun ω => |(X ω : ℝ)| := by
    funext ω
    simp
  have hN := entropyOf_nat_moment μ (fun ω => (X ω).natAbs) (habs ▸ hi) a ha (habs ▸ hmean)
  have hB := entropyOf_finite μ (fun ω => decide (X ω < 0))
  have he := informationOf_function μ X f hf
  have he' : entropyOf μ (f ∘ X) = entropyOf μ X := by simp only [entropyOf,he]
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact integrable_informationOf_pair μ _ _ hN.1 hB.1
  · have hh := entropyOf_pair_le μ _ _ hN.1 hB.1
    change entropyOf μ (f ∘ X) ≤ _ at hh
    rw [he'] at hh
    have hb : entropyOf μ (fun ω => decide (X ω < 0)) ≤ Real.log 2 := by simpa using hB.2
    linarith [hN.2]

lemma entropyOf_lattice_moment {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : ℕ) (X : Ω → Fin q → ℤ)
    (hi : ∀ i, Integrable (fun ω => |(X ω i : ℝ)|) μ) (a : ℝ) (ha : 0 < a)
    (hmean : ∀ i, (∫ ω, |(X ω i : ℝ)| ∂μ) ≤ a) :
    Integrable (informationOf μ X) μ ∧ entropyOf μ X ≤ q*(1+Real.log 2+Real.log (a+1)) := by
  induction q with
  | zero =>
    have he : informationOf μ X = 0 := by
      funext ω
      rw [informationOf_fiber]
      have hset : {ξ | X ξ = X ω} = Set.univ := by
        ext ξ
        simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
        funext i
        exact Fin.elim0 i
      simp [hset]
    constructor
    · rw [he]
      exact integrable_zero _ _ _
    · simp [entropyOf,he]
  | succ q ih =>
    let f : (Fin (q+1) → ℤ) → ℤ × (Fin q → ℤ) := fun v => (v 0,fun i => v i.succ)
    have hf : Function.Injective f := by
      intro v w h
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (Prod.mk.inj h).1
      · exact congrFun (Prod.mk.inj h).2 j
    have hh := entropyOf_int_moment μ (fun ω => X ω 0) (hi 0) a ha (hmean 0)
    have ht := ih (fun ω i => X ω i.succ) (fun i => hi i.succ) (fun i => hmean i.succ)
    have he := informationOf_function μ X f hf
    have he' : entropyOf μ (f ∘ X) = entropyOf μ X := by simp only [entropyOf,he]
    refine ⟨?_, ?_⟩
    · rw [← he]
      exact integrable_informationOf_pair μ _ _ hh.1 ht.1
    · have hb := entropyOf_pair_le μ _ _ hh.1 ht.1
      change entropyOf μ (f ∘ X) ≤ _ at hb
      rw [he'] at hb
      push_cast
      nlinarith [hh.2,ht.2]

end DirectionalZeroOne

end OAI
