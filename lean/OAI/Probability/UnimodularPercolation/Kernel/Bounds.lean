import Mathlib
import OAI.Probability.UnimodularPercolation.Graph.Basic

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section PositiveColumn
attribute [local instance] Classical.propDecidable

 

theorem no_positive_lower_bound [Infinite V] (f : Hilbert V) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) : False := by
  have hs : Summable (fun x => ‖f x‖ ^ (2 : ℕ)) := by
    simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f).summable
  have hconst : Summable (fun _ : V => c ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg c)
      (fun x => pow_le_pow_left₀ hc.le (hf x) 2) hs
  have hz : c ^ 2 = 0 := (summable_const_iff _).mp hconst
  nlinarith

 

theorem not_operatorBounded_of_positive_column [Infinite V]
    (G : BondGraph V E) (p : unitInterval) (y : V) {c : ℝ}
    (hc : 0 < c) (hcol : ∀ x, c ≤ twoPoint G p x y) :
    ¬ OperatorBounded G p := by
  rintro ⟨A, hA⟩
  apply no_positive_lower_bound (A (lp.single 2 y (1 : ℂ))) hc
  intro x
  rw [hA x y, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (twoPoint_nonneg G p x y)]
  exact hcol x

@[simp] theorem not_operatorBounded_one [Infinite V] (G : BondGraph V E)
    (h : Connected G) : ¬ OperatorBounded G 1 := by
  apply not_operatorBounded_of_positive_column G 1 (Classical.arbitrary V)
    (c := 1) (by norm_num)
  intro x
  rw [twoPoint_one G h]

@[simp] theorem operatorNorm_one [Infinite V] (G : BondGraph V E)
    (h : Connected G) : operatorNorm G 1 = ⊤ :=
  (operatorNorm_eq_top_iff G 1).mpr (not_operatorBounded_one G h)

end PositiveColumn

section KernelLimits
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

 
noncomputable def finiteEmbedding : (V →₀ ℂ) →ₗ[ℂ] Hilbert V :=
  Finsupp.linearCombination ℂ (fun y => lp.single 2 y (1 : ℂ))

@[simp] theorem finiteEmbedding_single (y : V) (c : ℂ) :
    finiteEmbedding (Finsupp.single y c) = lp.single 2 y c := by
  simp [finiteEmbedding, ← lp.single_smul]

theorem finiteEmbedding_dense : DenseRange (finiteEmbedding (V := V)) := by
  intro f
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) f)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ y ∈ s, Finsupp.single y (f y), ?_⟩
  simp

 

theorem exists_operator_of_matrix_tendsto
    (A : ℕ → Hilbert V →L[ℂ] Hilbert V) (K : V → V → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ n, ‖A n‖ ≤ M)
    (hlim : ∀ x y, Tendsto (fun n => A n (lp.single 2 y (1 : ℂ)) x)
      atTop (𝓝 (K x y))) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V,
      ‖B‖ ≤ M ∧ ∀ x y, B (lp.single 2 y (1 : ℂ)) x = K x y := by
  have hn (n : ℕ) (f : Hilbert V) : ‖A n f‖ ≤ M * ‖f‖ :=
    (A n).le_opNorm f |>.trans (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _))
  have hcol (y : V) : Memℓp (fun x => K x y) 2 := by
    apply lp.memℓp_of_tendsto (l := atTop) (F := fun n => A n (lp.single 2 y (1 : ℂ)))
    · apply isBounded_iff_forall_norm_le.mpr
      refine ⟨M, ?_⟩
      rintro _ ⟨n, rfl⟩
      simpa [lp.norm_single] using hn n (lp.single 2 y (1 : ℂ))
    · exact tendsto_pi_nhds.mpr (fun x => hlim x y)
  let col (y : V) : Hilbert V := ⟨fun x => K x y, hcol y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hLlim (f : V →₀ ℂ) :
      Tendsto (fun n => (A n (finiteEmbedding f) : V → ℂ)) atTop
        (𝓝 (L f : V → ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    simp only [finiteEmbedding, L, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
    exact tendsto_finsetSum _ (fun y _ => (hlim x y).const_mul (f y))
  have hLn (f : V →₀ ℂ) : ‖L f‖ ≤ M * ‖finiteEmbedding f‖ := by
    exact lp.norm_le_of_tendsto (Eventually.of_forall (fun n => hn n _)) (hLlim f)
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense hM hLn, ?_⟩
  intro x y
  have h := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨M, hLn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at h
  rw [h]
  simp [L, col]

end KernelLimits

section Measurability

 

theorem measurableSet_conn [Countable V] [Countable E]
    (G : BondGraph V E) (x y : V) : MeasurableSet {ω | Conn G ω x y} := by
  classical
  have hedge (a b : V) : MeasurableSet {ω : Set E | ∃ e ∈ ω, G e = s(a, b)} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro e
    by_cases he : G e = s(a, b)
    · simpa [he] using (measurableSet_setOfPred.mpr (measurable_set_mem e))
    · simp [he]
  have hlist (l : List V) : MeasurableSet {ω : Set E |
      l.IsChain (fun a b => ∃ e ∈ ω, G e = s(a, b))} := by
    induction l with
    | nil => simp
    | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
        simpa only [List.isChain_cons_cons, Set.ofPred_and] using (hedge a b).inter ih
  have he : {ω | Conn G ω x y} = ⋃ l : List V,
      {ω | (x :: l).IsChain (fun a b => ∃ e ∈ ω, G e = s(a, b)) ∧
        (x :: l).getLast (by simp) = y} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨List.exists_isChain_cons_of_relationReflTransGen,
      fun ⟨l, hl, hy⟩ => List.relationReflTransGen_of_exists_isChain_cons l hl hy⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  by_cases hlast : (x :: l).getLast (by simp) = y
  · simpa [hlast] using hlist (x :: l)
  · simp [hlast]

end Measurability

section Coupling

instance labelLaw_isProbabilityMeasure :
    IsProbabilityMeasure (labelLaw : Measure (E → unitInterval)) := by
  dsimp [labelLaw]
  infer_instance

theorem measurable_threshold (p : unitInterval) :
    Measurable (fun t : unitInterval => t ≤ p) :=
  measurableSet_setOfPred.mp measurableSet_Iic

 
theorem map_threshold (p : unitInterval) :
    (volume : Measure unitInterval).map (fun t => t ≤ p) =
      unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Iic p) = _
    rw [unitInterval.volume_Iic, ← unitInterval.coe_toNNReal p,
      ENNReal.ofReal_coe_nnreal]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Ioi p) = _
    rw [unitInterval.volume_Ioi, ← unitInterval.coe_symm_eq,
      ← unitInterval.coe_toNNReal (unitInterval.symm p), ENNReal.ofReal_coe_nnreal]

 
theorem map_openEdges (p : unitInterval) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p) =
      law p := by
  unfold law
  rw [setBernoulli_eq_map]
  have hmeas : Measurable (fun labels : E → unitInterval => fun e => labels e ≤ p) :=
    Measurable.of_eval (fun e => (measurable_threshold p).comp (measurable_pi_apply e))
  have he : (fun labels : E → unitInterval => openEdges labels p) =
      (fun f : E → Prop => {e | f e}) ∘ (fun labels e => labels e ≤ p) := rfl
  rw [he, ← Measure.map_map measurable_setOfPred hmeas]
  unfold labelLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_threshold p)]
  simp only [map_threshold, Set.mem_univ, bernoulliMeasure_def]

end Coupling

section KernelDomination
attribute [local instance] Classical.propDecidable

@[simp] theorem finiteEmbedding_apply (f : V →₀ ℂ) (x : V) :
    finiteEmbedding f x = f x := by
  simp only [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    ← lp.single_smul, lp.coeFn_sum, lp.coeFn_single]
  rw [Finset.sum_apply, Finset.sum_pi_single]
  split_ifs with h
  · simp
  · exact (Finsupp.notMem_support_iff.mp h).symm

 
noncomputable def positivePart (f : Hilbert V) : Hilbert V :=
  ⟨fun x => (‖f x‖ : ℂ), (lp.memℓp f).mono' (by intro x; simp)⟩

@[simp] theorem positivePart_apply (f : Hilbert V) (x : V) :
    positivePart f x = (‖f x‖ : ℂ) := rfl

@[simp] theorem norm_positivePart (f : Hilbert V) : ‖positivePart f‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro x
    simp
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro x
    simp

 

theorem exists_operator_of_matrix_domination
    (U K : V → V → ℝ) (hU : ∀ x y, 0 ≤ U x y)
    (hKU : ∀ x y, |K x y| ≤ U x y)
    (B : Hilbert V →L[ℂ] Hilbert V)
    (hB : ∀ x y, B (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ)) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ ‖B‖ ∧
      ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (K x y : ℂ) := by
  have hcol (y : V) : Memℓp (fun x => (K x y : ℂ)) 2 := by
    apply (lp.memℓp (B (lp.single 2 y (1 : ℂ)))).mono'
    intro x
    simpa [hB x y, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU x y)]
      using hKU x y
  let col (y : V) : Hilbert V := ⟨fun x => (K x y : ℂ), hcol y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hLn (f : V →₀ ℂ) : ‖L f‖ ≤ ‖B‖ * ‖finiteEmbedding f‖ := by
    let g : V →₀ ℂ := f.mapRange (fun z => (‖z‖ : ℂ)) (by simp)
    have hg : finiteEmbedding g = positivePart (finiteEmbedding f) := by
      apply lp.ext
      funext x
      simp [g]
    have hpoint (x : V) : ‖L f x‖ ≤ ‖B (finiteEmbedding g) x‖ := by
      have hright : B (finiteEmbedding g) x =
          (∑ y ∈ f.support, ‖f y‖ * U x y : ℝ) := by
        simp only [finiteEmbedding, g, Finsupp.linearCombination_apply]
        rw [Finsupp.sum_mapRange_index (by simp)]
        simp only [Finsupp.sum, map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
          lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hB, Complex.ofReal_sum,
          Complex.ofReal_mul]
      have hnn : 0 ≤ ∑ y ∈ f.support, ‖f y‖ * U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (hU x y))
      rw [hright, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      simp only [L, Finsupp.linearCombination_apply, Finsupp.sum,
        lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      calc
        ‖∑ y ∈ f.support, f y * col y x‖ ≤
            ∑ y ∈ f.support, ‖f y * col y x‖ := norm_sum_le _ _
        _ ≤ ∑ y ∈ f.support, ‖f y‖ * U x y := by
          apply Finset.sum_le_sum
          intro y _
          simpa [col, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left (hKU x y) (norm_nonneg (f y))
    calc
      ‖L f‖ ≤ ‖B (finiteEmbedding g)‖ := lp.norm_mono (by norm_num) hpoint
      _ ≤ ‖B‖ * ‖finiteEmbedding g‖ := B.le_opNorm _
      _ = ‖B‖ * ‖finiteEmbedding f‖ := by rw [hg, norm_positivePart]
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense (norm_nonneg _) hLn, ?_⟩
  intro x y
  have h := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨‖B‖, hLn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at h
  rw [h]
  simp [L, col]

end KernelDomination

section CouplingOrder
variable [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
theorem measurable_openEdges (p : unitInterval) :
    Measurable (fun labels : E → unitInterval => openEdges labels p) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_threshold p).comp (measurable_pi_apply e)))

theorem twoPoint_eq_labelLaw (p : unitInterval) (x y : V) :
    twoPoint G p x y =
      (labelLaw {labels : E → unitInterval | Conn G (openEdges labels p) x y}).toReal := by
  unfold twoPoint
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p)
    (measurableSet_conn G x y)]
  rfl

omit [Countable E] in
theorem openEdges_mono (labels : E → unitInterval) : Monotone (openEdges labels) := by
  intro p q hpq e he
  exact he.trans hpq

theorem twoPoint_mono (x y : V) : Monotone (fun p => twoPoint G p x y) := by
  intro p q hpq
  change twoPoint G p x y ≤ twoPoint G q x y
  rw [twoPoint_eq_labelLaw, twoPoint_eq_labelLaw]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro labels h
  exact conn_mono G (openEdges_mono labels hpq) h

end CouplingOrder

section NormOrder
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E] (G : BondGraph V E)

theorem operatorBounded_of_le {p q : unitInterval} (hpq : p ≤ q)
    (hq : OperatorBounded G q) : OperatorBounded G p := by
  obtain ⟨B, hB⟩ := hq
  obtain ⟨A, _, hA⟩ := exists_operator_of_matrix_domination
    (twoPoint G q) (twoPoint G p) (twoPoint_nonneg G q)
    (fun x y => (abs_of_nonneg (twoPoint_nonneg G p x y)).le.trans
      (twoPoint_mono G x y hpq)) B hB
  exact ⟨A, hA⟩

theorem operatorNorm_mono : Monotone (operatorNorm G) := by
  intro p q hpq
  by_cases hq : OperatorBounded G q
  · obtain ⟨B, hB⟩ := hq
    obtain ⟨A, hnorm, hA⟩ := exists_operator_of_matrix_domination
      (twoPoint G q) (twoPoint G p) (twoPoint_nonneg G q)
      (fun x y => (abs_of_nonneg (twoPoint_nonneg G p x y)).le.trans
        (twoPoint_mono G x y hpq)) B hB
    rw [operatorNorm_of_hasKernel hA, operatorNorm_of_hasKernel hB]
    exact ENNReal.ofReal_le_ofReal hnorm
  · rw [(operatorNorm_eq_top_iff G q).mpr hq]
    exact le_top

end NormOrder

section CouplingLimits
open Filter Topology

theorem conn_iUnion_iff (G : BondGraph V E) (ω : ℕ → Set E) (hω : Monotone ω)
    (x y : V) : Conn G (⋃ n, ω n) x y ↔ ∃ n, Conn G (ω n) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, conn_refl G _ _⟩
    | @tail y z _ hyz ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨e, he, heq⟩ := hyz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
      exact ⟨max m n, (conn_mono G (hω (le_max_left _ _)) hm).tail
        ⟨e, hω (le_max_right _ _) hn, heq⟩⟩
  · rintro ⟨n, hn⟩
    exact conn_mono G (Set.subset_iUnion ω n) hn

 
theorem ae_labels_ne [Countable E] (q : unitInterval) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), ∀ e, labels e ≠ q := by
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  simp only [not_not]
  change labelLaw ((fun labels : E → unitInterval => labels e) ⁻¹' {q}) = 0
  rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton q)]
  change (Measure.infinitePi (fun _ : E => (volume : Measure unitInterval))).map
    (fun labels => labels e) {q} = 0
  rw [Measure.infinitePi_map_eval]
  simp

theorem openEdges_eq_iUnion_of_tendsto (labels : E → unitInterval)
    (q : unitInterval) (hneq : ∀ e, labels e ≠ q) (p : ℕ → unitInterval)
    (hle : ∀ n, p n ≤ q) (hlim : Tendsto p atTop (𝓝 q)) :
    openEdges labels q = ⋃ n, openEdges labels (p n) := by
  ext e
  constructor
  · intro he
    have hlt : labels e < q := lt_of_le_of_ne he (hneq e)
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).1 _ hlt).exists
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  · intro he
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
    exact hn.trans (hle n)

 

theorem twoPoint_tendsto_of_monotone [Countable V] [Countable E]
    (G : BondGraph V E) (p : ℕ → unitInterval) (hp : Monotone p)
    (q : unitInterval) (hle : ∀ n, p n ≤ q) (hlim : Tendsto p atTop (𝓝 q))
    (x y : V) : Tendsto (fun n => twoPoint G (p n) x y) atTop (𝓝 (twoPoint G q x y)) := by
  let s (n : ℕ) : Set (E → unitInterval) := {labels | Conn G (openEdges labels (p n)) x y}
  have hs : Monotone s := by
    intro m n hmn labels hl
    exact conn_mono G (openEdges_mono labels (hp hmn)) hl
  have he : {labels : E → unitInterval | Conn G (openEdges labels q) x y} =ᵐ[labelLaw]
      ⋃ n, s n := by
    filter_upwards [ae_labels_ne (E := E) q] with labels hlabels
    apply propext
    rw [openEdges_eq_iUnion_of_tendsto labels q hlabels p hle hlim, conn_iUnion_iff]
    · simp [s]
    · exact fun m n hmn => openEdges_mono labels (hp hmn)
  rw [twoPoint_eq_labelLaw G q x y, measure_congr he]
  have ht := (tendsto_measure_iUnion_atTop (μ := (labelLaw : Measure (E → unitInterval))) hs)
  have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  simpa only [Function.comp_def, s, ← twoPoint_eq_labelLaw] using hr

end CouplingLimits

section Endpoint
open Filter Topology
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E] (G : BondGraph V E)

 

theorem operatorNorm_eq_sup_below (q : unitInterval) (hq : 0 < q) :
    operatorNorm G q = sSup {r | ∃ p : unitInterval, p < q ∧ r = operatorNorm G p} := by
  let S : ℝ≥0∞ := sSup {r | ∃ p : unitInterval, p < q ∧ r = operatorNorm G p}
  change operatorNorm G q = S
  apply le_antisymm
  · by_cases hS : S = ⊤
    · rw [hS]
      exact le_top
    obtain ⟨p, hp, hpq, hlim⟩ := exists_seq_strictMono_tendsto' hq
    have hbound (n : ℕ) : operatorNorm G (p n) ≤ S :=
      le_sSup ⟨p n, (hpq n).2, rfl⟩
    have hbounded (n : ℕ) : OperatorBounded G (p n) :=
      (operatorNorm_lt_top_iff G (p n)).mp ((hbound n).trans_lt (lt_top_iff_ne_top.mpr hS))
    choose A hA using hbounded
    have hnorm (n : ℕ) : ‖A n‖ ≤ S.toReal := by
      apply (ENNReal.ofReal_le_iff_le_toReal hS).mp
      rw [← operatorNorm_of_hasKernel (hA n)]
      exact hbound n
    have hmatrix (x y : V) : Tendsto (fun n => A n (lp.single 2 y (1 : ℂ)) x)
        atTop (𝓝 (twoPoint G q x y : ℂ)) := by
      have ht := (Complex.continuous_ofReal.tendsto (twoPoint G q x y)).comp
        (twoPoint_tendsto_of_monotone G p hp.monotone q (fun n => (hpq n).2.le) hlim x y)
      convert ht using 1
      funext n
      exact hA n x y
    obtain ⟨B, hBn, hB⟩ := exists_operator_of_matrix_tendsto A
      (fun x y => (twoPoint G q x y : ℂ)) ENNReal.toReal_nonneg hnorm hmatrix
    rw [operatorNorm_of_hasKernel hB]
    exact (ENNReal.ofReal_le_iff_le_toReal hS).mpr hBn
  · apply sSup_le
    rintro r ⟨p, hp, rfl⟩
    exact operatorNorm_mono G hp.le

theorem operatorBounded_iff_uniform_below (q : unitInterval) (hq : 0 < q) :
    OperatorBounded G q ↔ ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ p < q, operatorNorm G p ≤ M := by
  rw [← operatorNorm_lt_top_iff]
  constructor
  · intro h
    exact ⟨operatorNorm G q, h, fun p hp => operatorNorm_mono G hp.le⟩
  · rintro ⟨M, hM, h⟩
    rw [operatorNorm_eq_sup_below G q hq]
    apply lt_of_le_of_lt ?_ hM
    apply sSup_le
    rintro r ⟨p, hp, rfl⟩
    exact h p hp

end Endpoint

end Percolation

end OAI
