import OAI.Probability.DirectionalWalk.PosteriorTails

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def atomInfo {α : Type*} [MeasurableSpace α] (μ : Measure α) (x : α) : ℝ :=
  -Real.log (μ.real {x})

noncomputable def discreteEntropy {α : Type*} [MeasurableSpace α] (μ : Measure α) : ℝ :=
  ∫ x, atomInfo μ x ∂μ

lemma atomInfo_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (x : α) : 0 ≤ atomInfo μ x := by
  exact neg_nonneg.mpr (Real.log_nonpos measureReal_nonneg measureReal_le_one)

lemma discreteEntropy_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : 0 ≤ discreteEntropy μ :=
  integral_nonneg (atomInfo_nonneg μ)

lemma ae_atom_real_pos {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] : ∀ᵐ x ∂μ, 0 < μ.real {x} := by
  filter_upwards [ae_atom_pos μ] with x hx
  exact ENNReal.toReal_pos hx (by finiteness)

lemma summable_integral_ratio {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (q : α → ℝ≥0∞) (_hq : (∑' x, q x) ≠ ∞) :
    (∫⁻ x, q x / μ {x} ∂μ) ≤ ∑' x, q x := by
  rw [lintegral_countable']
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : μ {x} = 0
  · simp [hx]
  · rw [ENNReal.div_mul_cancel hx (by finiteness)]

lemma integrable_atom_ratio {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (q : α → ℝ≥0∞) (hq : (∑' x, q x) ≠ ∞) :
    Integrable (fun x => (q x / μ {x}).toReal) μ := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_of_countable _).aemeasurable
  exact ne_of_lt ((summable_integral_ratio μ q hq).trans_lt (lt_top_iff_ne_top.mpr hq))

lemma integral_atom_ratio_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (q : α → ℝ≥0∞) (hq : (∑' x, q x) ≠ ∞) :
    (∫ x, (q x / μ {x}).toReal ∂μ) ≤ (∑' x, q x).toReal := by
  rw [integral_toReal]
  · exact ENNReal.toReal_mono hq (summable_integral_ratio μ q hq)
  · exact (measurable_of_countable _).aemeasurable
  · filter_upwards [ae_atom_pos μ] with x hx
    exact lt_top_iff_ne_top.mpr (ENNReal.div_ne_top (ne_of_lt ((ENNReal.le_tsum x).trans_lt (lt_top_iff_ne_top.mpr hq))) hx)

lemma atomInfo_le_comparison {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ≥0∞) (hq : ∀ x, q x ≠ 0 ∧ q x ≠ ∞) :
    ∀ᵐ x ∂μ, atomInfo μ x ≤ -Real.log (q x).toReal + (q x / μ {x}).toReal - 1 := by
  filter_upwards [ae_atom_real_pos μ] with x hx
  have hqx : 0 < (q x).toReal := ENNReal.toReal_pos (hq x).1 (hq x).2
  have hh := Real.log_le_sub_one_of_pos (div_pos hqx hx)
  rw [Real.log_div (ne_of_gt hqx) (ne_of_gt hx)] at hh
  simp only [atomInfo,ENNReal.toReal_div,measureReal_def] at *
  linarith

lemma integrable_atomInfo_of_comparison {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ≥0∞) (hq0 : ∀ x, q x ≠ 0) (hq : (∑' x, q x) ≠ ∞)
    (hcost : Integrable (fun x => -Real.log (q x).toReal) μ) : Integrable (atomInfo μ) μ := by
  have hqx x : q x ≠ 0 ∧ q x ≠ ∞ := ⟨hq0 x,
    ne_of_lt ((ENNReal.le_tsum x).trans_lt (lt_top_iff_ne_top.mpr hq))⟩
  apply ((hcost.add (integrable_atom_ratio μ q hq)).sub (integrable_const 1)).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [atomInfo_le_comparison μ q hqx] with x hx
  simpa only [Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (atomInfo_nonneg μ x)] using hx

lemma discreteEntropy_le_comparison {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ≥0∞) (hq0 : ∀ x, q x ≠ 0) (hq : (∑' x, q x) ≠ ∞)
    (hcost : Integrable (fun x => -Real.log (q x).toReal) μ) :
    discreteEntropy μ ≤ (∫ x, -Real.log (q x).toReal ∂μ) + (∑' x, q x).toReal - 1 := by
  have hqx x : q x ≠ 0 ∧ q x ≠ ∞ := ⟨hq0 x,
    ne_of_lt ((ENNReal.le_tsum x).trans_lt (lt_top_iff_ne_top.mpr hq))⟩
  have hi := integral_mono_ae (integrable_atomInfo_of_comparison μ q hq0 hq hcost)
    ((hcost.add (integrable_atom_ratio μ q hq)).sub (integrable_const 1))
    (atomInfo_le_comparison μ q hqx)
  simp only [Pi.sub_apply,Pi.add_apply] at hi
  have hsum : Integrable (fun x => -Real.log (q x).toReal + (q x / μ {x}).toReal) μ :=
    hcost.add (integrable_atom_ratio μ q hq)
  rw [integral_sub hsum (integrable_const 1),
    integral_add hcost (integrable_atom_ratio μ q hq)] at hi
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  exact hi.trans (by linarith [integral_atom_ratio_le μ q hq])

lemma rnDeriv_atom {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (x : α) (hx : ν {x} ≠ 0) : μ.rnDeriv ν x = μ {x} / ν {x} := by
  have h := Measure.setLIntegral_rnDeriv hμν ({x} : Set α)
  rw [lintegral_singleton] at h
  exact (ENNReal.eq_div_iff hx (by finiteness)).mpr (by simpa only [mul_comm] using h)

lemma llr_atom {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    llr μ ν =ᵐ[μ] fun x => Real.log (μ.real {x}) - Real.log (ν.real {x}) := by
  filter_upwards [ae_atom_pos μ,hμν (ae_atom_pos ν)] with x hx hy
  rw [llr,rnDeriv_atom μ ν hμν x hy,ENNReal.toReal_div,Real.log_div]
  · rfl
  · exact (ENNReal.toReal_pos hx (by finiteness)).ne'
  · exact (ENNReal.toReal_pos hy (by finiteness)).ne'

lemma absolutelyContinuous_of_atoms {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    (h : ∀ x, ν {x} = 0 → μ {x} = 0) : μ ≪ ν := by
  intro s hs
  rw [← Set.biUnion_of_singleton s]
  exact (measure_biUnion_null_iff (Set.to_countable s)).mpr fun x hx => h x
    (measure_mono_null (Set.singleton_subset_iff.mpr hx) hs)

lemma atom_logRatio_nonneg {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (hi : Integrable (fun x => Real.log (μ.real {x}) - Real.log (ν.real {x})) μ) :
    0 ≤ ∫ x, Real.log (μ.real {x}) - Real.log (ν.real {x}) ∂μ := by
  have hllr := llr_atom μ ν hμν
  have h := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hμν
    (hi.congr hllr.symm)
  simpa only [integral_congr_ae hllr,probReal_univ,add_sub_cancel_right] using h

lemma atom_klDiv_formula {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (hi : Integrable (fun x => Real.log (μ.real {x}) - Real.log (ν.real {x})) μ) :
    InformationTheory.klDiv μ ν = ENNReal.ofReal
      (∫ x, Real.log (μ.real {x}) - Real.log (ν.real {x}) ∂μ) := by
  have hllr := llr_atom μ ν hμν
  rw [InformationTheory.klDiv_of_ac_of_integrable hμν (hi.congr hllr.symm),
    integral_congr_ae hllr,probReal_univ,probReal_univ,add_sub_cancel_right]

noncomputable def conditionalInfo {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) (p : α × β) : ℝ :=
  -Real.log (ρ.real {p} / ρ.fst.real {p.1})

noncomputable def conditionalEntropy {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) : ℝ := ∫ p, conditionalInfo ρ p ∂ρ

lemma atom_le_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] (ρ : Measure (α × β)) (p : α × β) :
    ρ {p} ≤ ρ.fst {p.1} := by
  rw [Measure.fst_apply (measurableSet_singleton _)]
  exact measure_mono (by intro x hx; obtain rfl := Set.mem_singleton_iff.mp hx; rfl)

lemma conditionalInfo_nonneg {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (p : α × β) :
    0 ≤ conditionalInfo ρ p := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (div_nonneg measureReal_nonneg measureReal_nonneg)
  by_cases h : ρ.fst.real {p.1} = 0
  · simp [h]
  · apply (div_le_one (lt_of_le_of_ne measureReal_nonneg (Ne.symm h))).mpr
    exact ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p)

lemma conditionalInfo_log {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] :
    conditionalInfo ρ =ᵐ[ρ] fun p => -Real.log (ρ.real {p}) + Real.log (ρ.fst.real {p.1}) := by
  filter_upwards [ae_atom_real_pos ρ] with p hp
  have hfst : 0 < ρ.fst.real {p.1} := hp.trans_le (ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p))
  dsimp [conditionalInfo]
  rw [Real.log_div hp.ne' hfst.ne']
  ring

lemma compProd_atom {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] (p : α × β) :
    (μ ⊗ₘ κ) {p} = μ {p.1} * κ p.1 {p.2} := by
  have hset : ({p} : Set (α × β)) = {p.1} ×ˢ {p.2} := by ext x; simp [Prod.ext_iff]
  rw [hset,Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton,mul_comm]

lemma integrable_conditionalInfo {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : ρ ≪ ρ.fst ⊗ₘ κ)
    (hi : Integrable (fun p : α × β => atomInfo (κ p.1) p.2) ρ) :
    Integrable (conditionalInfo ρ) ρ := by
  let ν := ρ.fst ⊗ₘ κ
  have hsum : (∑' p, ν {p}) = 1 := by
    have hh := lintegral_countable' (μ := ν) (fun _ => (1 : ℝ≥0∞))
    simpa using hh.symm
  have hr := integrable_atom_ratio ρ (fun p => ν {p}) (by rw [hsum]; exact ENNReal.one_ne_top)
  apply ((hi.add hr).sub (integrable_const 1)).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [ae_atom_real_pos ρ,hac (ae_atom_real_pos ν),conditionalInfo_log ρ] with p hp hν he
  have hfst : 0 < ρ.fst.real {p.1} := hp.trans_le (ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p))
  have hn : ν.real {p} = ρ.fst.real {p.1} * (κ p.1).real {p.2} := by
    simp only [ν,measureReal_def,compProd_atom,ENNReal.toReal_mul]
  have hk : 0 < (κ p.1).real {p.2} := (mul_pos_iff_of_pos_left hfst).mp (hn ▸ hν)
  have hh := Real.log_le_sub_one_of_pos (div_pos hν hp)
  rw [Real.log_div hν.ne' hp.ne',hn,Real.log_mul hfst.ne' hk.ne'] at hh
  rw [Real.norm_eq_abs,abs_of_nonneg (conditionalInfo_nonneg ρ p)]
  simp only [Pi.sub_apply,Pi.add_apply,he,atomInfo,ENNReal.toReal_div,← measureReal_def,hn]
  linarith

lemma conditionalEntropy_le_crossEntropy {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : ρ ≪ ρ.fst ⊗ₘ κ)
    (hi : Integrable (fun p : α × β => atomInfo (κ p.1) p.2) ρ) :
    conditionalEntropy ρ ≤ ∫ p, atomInfo (κ p.1) p.2 ∂ρ := by
  have hc := integrable_conditionalInfo ρ κ hac hi
  have he : (fun p : α × β => atomInfo (κ p.1) p.2 - conditionalInfo ρ p) =ᵐ[ρ]
      fun p => Real.log (ρ.real {p}) - Real.log ((ρ.fst ⊗ₘ κ).real {p}) := by
    filter_upwards [ae_atom_real_pos ρ,hac (ae_atom_real_pos (ρ.fst ⊗ₘ κ)),conditionalInfo_log ρ] with p hp hν he
    have hfst : 0 < ρ.fst.real {p.1} := hp.trans_le (ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p))
    have hn : (ρ.fst ⊗ₘ κ).real {p} = ρ.fst.real {p.1} * (κ p.1).real {p.2} := by
      simp only [measureReal_def,compProd_atom,ENNReal.toReal_mul]
    have hk : 0 < (κ p.1).real {p.2} := (mul_pos_iff_of_pos_left hfst).mp (hn ▸ hν)
    rw [hn,Real.log_mul hfst.ne' hk.ne',he]
    dsimp [atomInfo]
    ring
  have hh := atom_logRatio_nonneg ρ (ρ.fst ⊗ₘ κ) hac ((hi.sub hc).congr he)
  rw [← integral_congr_ae he,integral_sub hi hc] at hh
  exact sub_nonneg.mp hh

lemma joint_ac_marginal_product {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] : ρ ≪ ρ.fst.prod ρ.snd := by
  apply absolutelyContinuous_of_atoms
  intro p hp
  have he : (ρ.fst.prod ρ.snd) {p} = ρ.fst {p.1} * ρ.snd {p.2} := by
    rw [← Set.singleton_prod_singleton,Measure.prod_prod]
  rw [he,mul_eq_zero] at hp
  rcases hp with hp | hp
  · exact le_antisymm ((atom_le_fst ρ p).trans hp.le) bot_le
  · have hh : ρ {p} ≤ ρ.snd {p.2} := by
      rw [Measure.snd_apply (measurableSet_singleton _)]
      exact measure_mono (by intro x hx; obtain rfl := Set.mem_singleton_iff.mp hx; rfl)
    exact le_antisymm (hh.trans hp.le) bot_le

lemma conditionalEntropy_le_entropy_snd {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (hi : Integrable (atomInfo ρ.snd) ρ.snd) : conditionalEntropy ρ ≤ discreteEntropy ρ.snd := by
  have hmap : MeasurePreserving Prod.snd ρ ρ.snd := ⟨measurable_snd,rfl⟩
  have hc : Integrable (fun p : α × β => atomInfo ρ.snd p.2) ρ := hmap.integrable_comp_of_integrable hi
  have hh := conditionalEntropy_le_crossEntropy ρ (Kernel.const α ρ.snd)
    (by simpa only [Measure.compProd_const] using joint_ac_marginal_product ρ) hc
  have he : (∫ p, atomInfo ρ.snd p.2 ∂ρ) = discreteEntropy ρ.snd := by
    dsimp [discreteEntropy,Measure.snd]
    rw [integral_map_of_stronglyMeasurable measurable_snd (measurable_of_countable _).stronglyMeasurable]
  exact hh.trans_eq he

end DirectionalZeroOne

end OAI
