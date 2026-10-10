import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

lemma finite_atomic_probability {ι : Type*} [Fintype ι] {d : ℕ}
    (y : ι → E d) (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1) :
    IsProbabilityMeasure (∑ i, w i • Measure.dirac (y i)) := by
  constructor
  simpa using hw

lemma finite_atomic_supported {ι : Type*} [Fintype ι] {d : ℕ}
    (y : ι → E d) (w : ι → ℝ≥0∞) {Y : Set (E d)}
    (hy : ∀ i, y i ∈ Y) :
    IsSupported (∑ i, w i • Measure.dirac (y i)) Y := by
  classical
  unfold IsSupported
  simp [Measure.finsetSum_apply, Measure.dirac_apply, hy]

lemma HasExactlyThreeAtoms.isProbabilityMeasure {d : ℕ}
    {μ : Measure (E d)} {Y : Set (E d)} (h : HasExactlyThreeAtoms μ Y) :
    IsProbabilityMeasure μ := by
  obtain ⟨y, _, _, w, _, hw, rfl⟩ := h
  exact finite_atomic_probability y w hw

lemma HasExactlyThreeAtoms.isSupported {d : ℕ}
    {μ : Measure (E d)} {Y : Set (E d)} (h : HasExactlyThreeAtoms μ Y) :
    IsSupported μ Y := by
  obtain ⟨y, _, hy, w, _, _, rfl⟩ := h
  exact finite_atomic_supported y w hy

lemma finite_atomic_singleton {ι : Type*} [Fintype ι] {d : ℕ}
    (y : ι → E d) (w : ι → ℝ≥0∞) (hy : Function.Injective y) (i : ι) :
    (∑ j, w j • Measure.dirac (y j)) {y i} = w i := by
  classical
  simp [Measure.finsetSum_apply, Pi.single_apply, hy.eq_iff]

lemma finite_atomic_singleton_of_not_mem {ι : Type*} [Fintype ι] {d : ℕ}
    (y : ι → E d) (w : ι → ℝ≥0∞) {x : E d}
    (hx : x ∉ Set.range y) :
    (∑ j, w j • Measure.dirac (y j)) {x} = 0 := by
  classical
  have hxy : ∀ j, y j ≠ x := by
    intro j hj
    exact hx ⟨j, hj⟩
  simp [Measure.finsetSum_apply, hxy]

lemma finite_atomic_ne_of_missing_atom {ι κ : Type*} [Fintype ι] [Fintype κ]
    {d : ℕ} (y : ι → E d) (z : κ → E d) (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞)
    (hy : Function.Injective y) (i : ι) (hwi : 0 < w i)
    (hi : y i ∉ Set.range z) :
    (∑ j, w j • Measure.dirac (y j)) ≠ ∑ j, v j • Measure.dirac (z j) := by
  intro h
  have he := congrArg (fun μ : Measure (E d) => μ {y i}) h
  rw [finite_atomic_singleton y w hy i,
    finite_atomic_singleton_of_not_mem z v hi] at he
  exact (ne_of_gt hwi) he

end Problem358

namespace Problem358

/-- The coupling which matches equally indexed atoms without splitting mass. -/
def atomicMatchingPlan {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) : Measure (E d × E d) :=
  ∑ i, w i • Measure.dirac (y i, z i)

theorem atomicMatchingPlan_isProbability {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    IsProbabilityMeasure (atomicMatchingPlan w y z) := by
  constructor
  simpa [atomicMatchingPlan, Measure.finsetSum_apply, Measure.smul_apply] using hw

theorem atomicMatchingPlan_fst {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    Measure.map Prod.fst (atomicMatchingPlan w y z) =
      ∑ i, w i • Measure.dirac (y i) := by
  unfold atomicMatchingPlan
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  simp only [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_dirac]

theorem atomicMatchingPlan_snd {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    Measure.map Prod.snd (atomicMatchingPlan w y z) =
      ∑ i, w i • Measure.dirac (z i) := by
  unfold atomicMatchingPlan
  rw [Measure.map_finset_sum measurable_snd.aemeasurable]
  simp only [Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_dirac]

theorem atomicMatchingPlan_isCoupling {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ i, w i • Measure.dirac (z i)) (atomicMatchingPlan w y z) := by
  exact ⟨atomicMatchingPlan_isProbability w y z hw,
    atomicMatchingPlan_fst w y z, atomicMatchingPlan_snd w y z⟩

theorem quadraticPlanCost_atomicMatchingPlan {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    quadraticPlanCost (atomicMatchingPlan w y z) =
      ∑ i, w i * ENNReal.ofReal (‖y i - z i‖ ^ 2) := by
  simp [quadraticPlanCost, atomicMatchingPlan,
    lintegral_smul_measure, lintegral_dirac]

theorem quadraticPlanCost_atomicMatchingPlan_ne_top {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    quadraticPlanCost (atomicMatchingPlan w y z) ≠ ∞ := by
  have hsum : (∑ i, w i) ≠ ∞ := by rw [hw]; exact ENNReal.one_ne_top
  rw [quadraticPlanCost_atomicMatchingPlan]
  exact ENNReal.sum_ne_top.mpr fun i hi =>
    ENNReal.mul_ne_top (ENNReal.sum_ne_top.mp hsum i hi) ENNReal.ofReal_ne_top

/-- Matching equally indexed atoms gives an explicit upper bound for the exact
Wasserstein quantity used in the challenge. -/
theorem wasserstein2_atomic_le {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    wasserstein2 (∑ i, w i • Measure.dirac (y i))
      (∑ i, w i • Measure.dirac (z i)) ≤
      Real.sqrt (∑ i, (w i).toReal * ‖y i - z i‖ ^ 2) := by
  have hcost := quadraticPlanCost_atomicMatchingPlan_ne_top w y z hw
  have hsum : (∑ i, w i) ≠ ∞ := by rw [hw]; exact ENNReal.one_ne_top
  have hfinite : ∀ i, w i * ENNReal.ofReal (‖y i - z i‖ ^ 2) ≠ ∞ :=
    fun i => ENNReal.mul_ne_top
      (ENNReal.sum_ne_top.mp hsum i (Finset.mem_univ i)) ENNReal.ofReal_ne_top
  have hreal : (quadraticPlanCost (atomicMatchingPlan w y z)).toReal =
      ∑ i, (w i).toReal * ‖y i - z i‖ ^ 2 := by
    rw [quadraticPlanCost_atomicMatchingPlan, ENNReal.toReal_sum (fun i _ => hfinite i)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [← hreal]
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono hcost
  exact sInf_le ⟨atomicMatchingPlan w y z, atomicMatchingPlan_isCoupling w y z hw, rfl⟩

end Problem358

namespace Problem358

/-- A measure concentrated on an injectively indexed finite set is the sum of
its point masses. -/
theorem eq_sum_dirac_of_ae_mem_range {X ι : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype ι] (μ : Measure X) (y : ι → X)
    (hy : Function.Injective y) (hμ : ∀ᵐ x ∂μ, x ∈ Set.range y) :
    μ = ∑ i, μ {y i} • Measure.dirac (y i) := by
  classical
  have hm : ∀ᵐ x ∂μ, x ∈ Finset.univ.image y := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hμ
  have heq := Measure.ae_mem_finset_iff.mp hm
  rw [Finset.sum_image] at heq
  · exact heq
  · intro a _ b _ hab
    exact hy hab

/-- Every weighted finite atomic measure is concentrated on its listed atoms. -/
theorem ae_mem_range_sum_dirac {X ι : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype ι] (w : ι → ℝ≥0∞) (y : ι → X) :
    ∀ᵐ x ∂(∑ i, w i • Measure.dirac (y i)), x ∈ Set.range y := by
  rw [ae_finsetSum_measure_iff]
  intro i _
  exact Measure.ae_smul_measure (by simp) _

/-- All mass of a coupling of finite atomic measures is carried by pairs of
listed atoms. -/
theorem IsCoupling.ae_mem_atomic_pairs {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π) :
    ∀ᵐ p ∂π, p ∈ Set.range (fun q : ι × κ => (y q.1, z q.2)) := by
  have hfst : ∀ᵐ p ∂π, p.1 ∈ Set.range y := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hπ.2.1]
    exact ae_mem_range_sum_dirac w y
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ Set.range z := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact ae_mem_range_sum_dirac v z
  filter_upwards [hfst, hsnd] with p hp hq
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  exact ⟨(i,j), Prod.ext hi hj⟩

/-- A coupling of injectively indexed atomic measures has the usual finite
matrix representation. -/
theorem IsCoupling.atomic_decomposition {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    π = ∑ q : ι × κ, π {(y q.1, z q.2)} • Measure.dirac (y q.1, z q.2) := by
  apply eq_sum_dirac_of_ae_mem_range
  · intro a b hab
    exact Prod.ext (hy (congrArg Prod.fst hab)) (hz (congrArg Prod.snd hab))
  · exact hπ.ae_mem_atomic_pairs

theorem finite_atomic_apply_atom {X ι : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype ι] (w : ι → ℝ≥0∞) (y : ι → X)
    (hy : Function.Injective y) (i : ι) :
    (∑ j, w j • Measure.dirac (y j)) {y i} = w i := by
  classical
  simp [Measure.finsetSum_apply, Measure.smul_apply, Pi.single_apply, hy.eq_iff]

theorem IsCoupling.atomic_row_sum {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (i : ι) :
    ∑ j, π {(y i, z j)} = w i := by
  classical
  have he := congrArg (fun μ : Measure (E d) => μ {y i}) hπ.2.1
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  rw [hd, atomicMatchingPlan_fst] at he
  simpa [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    Pi.single_apply, hy.eq_iff, Fintype.sum_prod_type] using he

theorem IsCoupling.atomic_col_sum {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (j : κ) :
    ∑ i, π {(y i, z j)} = v j := by
  classical
  have he := congrArg (fun μ : Measure (E d) => μ {z j}) hπ.2.2
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  rw [hd, atomicMatchingPlan_snd] at he
  simpa [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    Pi.single_apply, hz.eq_iff, Fintype.sum_prod_type] using he

theorem IsCoupling.atomic_cost {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    quadraticPlanCost π =
      ∑ q : ι × κ, π {(y q.1, z q.2)} * ENNReal.ofReal (‖y q.1 - z q.2‖ ^ 2) := by
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  conv_lhs => rw [hd, quadraticPlanCost_atomicMatchingPlan]

theorem atomicMatchingPlan_isCoupling_of_marginal_sums
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (p : ι × κ → ℝ≥0∞)
    (y : ι → E d) (z : κ → E d) (hw : ∑ i, w i = 1)
    (hrow : ∀ i, ∑ j, p (i,j) = w i) (hcol : ∀ j, ∑ i, p (i,j) = v j) :
    IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j))
      (atomicMatchingPlan p (fun q => y q.1) (fun q => z q.2)) := by
  have hp : ∑ q, p q = 1 := by
    rw [Fintype.sum_prod_type]
    simpa only [hrow] using hw
  refine ⟨atomicMatchingPlan_isProbability _ _ _ hp, ?_, ?_⟩
  · rw [atomicMatchingPlan_fst, Fintype.sum_prod_type]
    simp_rw [← Finset.sum_smul, hrow]
  · rw [atomicMatchingPlan_snd, Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_smul, hcol]

theorem IsCoupling.atomic_row_sum_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (i : ι) :
    ∑ j, (π {(y i, z j)}).toReal = (w i).toReal := by
  let : IsProbabilityMeasure π := hπ.1
  rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top π _)]
  exact congrArg ENNReal.toReal (hπ.atomic_row_sum hy hz i)

theorem IsCoupling.atomic_col_sum_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (j : κ) :
    ∑ i, (π {(y i, z j)}).toReal = (v j).toReal := by
  let : IsProbabilityMeasure π := hπ.1
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top π _)]
  exact congrArg ENNReal.toReal (hπ.atomic_col_sum hy hz j)

theorem IsCoupling.atomic_cost_ne_top {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    quadraticPlanCost π ≠ ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  rw [hπ.atomic_cost hy hz]
  exact ENNReal.sum_ne_top.mpr fun q _ =>
    ENNReal.mul_ne_top (measure_ne_top π _) ENNReal.ofReal_ne_top

theorem IsCoupling.atomic_cost_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    (quadraticPlanCost π).toReal =
      ∑ q : ι × κ, (π {(y q.1, z q.2)}).toReal * ‖y q.1 - z q.2‖ ^ 2 := by
  let : IsProbabilityMeasure π := hπ.1
  rw [hπ.atomic_cost hy hz, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro q _
    exact ENNReal.mul_ne_top (measure_ne_top π _) ENNReal.ofReal_ne_top

end Problem358

end

end OAI
