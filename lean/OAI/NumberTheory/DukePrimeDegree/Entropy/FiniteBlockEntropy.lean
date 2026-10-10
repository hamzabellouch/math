import OAI.NumberTheory.PrimePackets.ConditionalOrbitEntropy
import OAI.NumberTheory.PrimePackets.EntropyMixtures
import OAI.NumberTheory.PrimePackets.RootSubgroups

namespace OAI

/-! # Entropy comparison at finite block scales -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem observationEntropyRate_le_of_refines
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hQ : ∀ a, MeasurableSet {y | Q y=a})
    (href : ∀ x y, Q x=Q y → P x=P y) :
    observationEntropyRate μ T P ≤ observationEntropyRate μ T Q := by
  apply le_of_tendsto_of_tendsto (tendsto_observationEntropyRate μ hT P hP)
    (tendsto_observationEntropyRate μ hT Q hQ)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply observationEntropy_le_of_refines μ _ _
    (orbitName_measurable_fiber hT.measurable hP N)
    (orbitName_measurable_fiber hT.measurable hQ N)
  intro x y hxy
  funext i
  exact href _ _ (congrFun hxy i)

theorem observationEntropyRate_comp_commuting {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T S : Y → Y) (hS : MeasurePreserving S μ μ)
    (hcomm : Function.Commute S T) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) (hT : Measurable T) :
    observationEntropyRate μ T (P ∘ S)=observationEntropyRate μ T P := by
  unfold observationEntropyRate
  congr 2
  funext N
  congr 1
  have he : orbitName T (P ∘ S) N = (orbitName T P N) ∘ S := by
    funext y i
    exact congrArg P (hcomm.iterate_right i.val y)
  rw [he]
  exact observationEntropy_comp_preserving μ (orbitName T P N)
    (orbitName_measurable_fiber hT hP N) hS

private def blockWordEquiv (α : Type*) (N q : ℕ) :
    (Fin N → Fin q → α) ≃ (Fin (N*q) → α) where
  toFun w l := w (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
  invFun w i j := w (finProdFinEquiv (i,j))
  left_inv w := by funext i j; simp
  right_inv w := by
    funext l
    change w (finProdFinEquiv (finProdFinEquiv.symm l))=w l
    rw [Equiv.apply_symm_apply]

private lemma orbitName_blocks {Y α : Type*}
    (T : Y → Y) (P : Y → α) (N q : ℕ) :
    orbitName T P (N*q) = fun y =>
      blockWordEquiv α N q (orbitName (T^[q]) (orbitName T P q) N y) := by
  funext y
  apply (blockWordEquiv α N q).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i j
  change P (T^[j.val+q*i.val] y)=P (T^[j.val] ((T^[q])^[i.val] y))
  rw [Function.iterate_add_apply,Function.iterate_mul]

theorem observationEntropyRate_blocks {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) {q : ℕ} (hq : 0 < q) :
    observationEntropyRate μ (T^[q]) (orbitName T P q) =
      (q : ℝ)*observationEntropyRate μ T P := by
  have hsub : Tendsto (fun N : ℕ => N*q) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    exact hN.trans (Nat.le_mul_of_pos_right _ hq)
  have H := (tendsto_observationEntropyRate μ hT P hP).comp hsub
  have hscaled : Tendsto (fun N : ℕ => (q : ℝ)*
      (observationEntropy μ (orbitName T P (N*q))/(N*q : ℕ))) atTop
      (𝓝 ((q : ℝ)*observationEntropyRate μ T P)) := tendsto_const_nhds.mul H
  have heq : (fun N : ℕ => (q : ℝ)*
      (observationEntropy μ (orbitName T P (N*q))/(N*q : ℕ))) =
      (fun N : ℕ => observationEntropy μ
        (orbitName (T^[q]) (orbitName T P q) N)/N) := by
    funext N
    rw [orbitName_blocks,observationEntropy_equiv]
    by_cases hN : N=0
    · subst N
      simp
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast
    field_simp [hNr,hqr]
  rw [heq] at hscaled
  exact tendsto_nhds_unique
    (tendsto_observationEntropyRate μ (hT.iterate q) (orbitName T P q)
      (orbitName_measurable_fiber hT.measurable hP q)) hscaled

/-- Observing a fixed finite window at every q-th step has at most q
times the entropy rate of the underlying observation. -/
theorem observationEntropyRate_sampled_window_le {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) {q : ℕ} (hq : 0 < q) (W : ℕ) :
    observationEntropyRate μ (T^[q]) (orbitName T P W) ≤
      (q : ℝ)*observationEntropyRate μ T P := by
  have hb (N : ℕ) : observationEntropy μ
      (orbitName (T^[q]) (orbitName T P W) N) ≤
      observationEntropy μ (orbitName T P (N*q))+
        observationEntropy μ (orbitName T P W) := by
    apply le_trans (b := observationEntropy μ (orbitName T P (N*q+W)))
    · apply observationEntropy_le_of_refines μ _ _
        (orbitName_measurable_fiber (hT.measurable.iterate q)
          (orbitName_measurable_fiber hT.measurable hP W) N)
        (orbitName_measurable_fiber hT.measurable hP (N*q+W))
      intro x y hxy
      funext i j
      have hindex : j.val+q*i.val < N*q+W := by
        have hi := i.isLt
        have hj := j.isLt
        nlinarith
      have h := congrFun hxy ⟨j.val+q*i.val,hindex⟩
      simpa only [orbitName,Function.iterate_add_apply,Function.iterate_mul] using h
    · exact orbitEntropy_subadditive μ hT P hP (N*q) W
  have hbound : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName (T^[q]) (orbitName T P W) N)/(N : ℝ) ≤
      (q : ℝ)*(observationEntropy μ (orbitName T P (N*q))/(N*q : ℕ))+
        observationEntropy μ (orbitName T P W)/(N : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have H := div_le_div_of_nonneg_right (hb N) (Nat.cast_nonneg N)
    convert H using 1
    push_cast
    field_simp [hn,hqr]
  have hsub : Tendsto (fun N : ℕ => N*q) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    exact hN.trans (Nat.le_mul_of_pos_right _ hq)
  have hmain : Tendsto (fun N : ℕ => (q : ℝ)*
      (observationEntropy μ (orbitName T P (N*q))/(N*q : ℕ))) atTop
      (𝓝 ((q : ℝ)*observationEntropyRate μ T P)) :=
    tendsto_const_nhds.mul ((tendsto_observationEntropyRate μ hT P hP).comp hsub)
  have herr : Tendsto
      (fun N : ℕ => observationEntropy μ (orbitName T P W)/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := hmain.add herr
  simp only [add_zero] at hlim
  exact le_of_tendsto_of_tendsto
    (tendsto_observationEntropyRate μ (hT.iterate q) (orbitName T P W)
      (orbitName_measurable_fiber hT.measurable hP W)) hlim hbound

/-- Sampling a finite observation every q steps costs at most q times
its original entropy rate. -/
theorem observationEntropyRate_iterate_le {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) {q : ℕ} (hq : 0 < q) :
    observationEntropyRate μ (T^[q]) P ≤ (q : ℝ)*observationEntropyRate μ T P := by
  have h := observationEntropyRate_le_of_refines μ (hT.iterate q) P (orbitName T P 1)
    hP (orbitName_measurable_fiber hT.measurable hP 1)
    (fun x y hxy => by
      have he := congrFun hxy (0 : Fin 1)
      simpa only [orbitName,Fin.val_zero,Function.iterate_zero_apply] using he)
  exact h.trans (observationEntropyRate_sampled_window_le μ hT P hP hq 1)

theorem observationEntropyRate_le_block_conditional
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hQ : ∀ a, MeasurableSet {y | Q y=a}) {q : ℕ} (hq : 0 < q) :
    observationEntropyRate μ T P ≤ observationEntropyRate μ T Q+
      conditionalObservationEntropy μ (orbitName T P q) Q/(q : ℝ) := by
  have H := observationEntropyRate_le_add_conditional μ (hT.iterate q)
    (orbitName T P q) Q (orbitName_measurable_fiber hT.measurable hP q) hQ
  rw [observationEntropyRate_blocks μ hT P hP hq] at H
  have H' := observationEntropyRate_iterate_le μ hT Q hQ hq
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  apply (mul_le_mul_iff_right₀ hqr).mp
  rw [mul_add,mul_div_cancel₀ _ hqr.ne']
  nlinarith [H.trans (add_le_add H' le_rfl)]

/-- A long block of the first observation can be conditioned on any
fixed window of the second observation. -/
theorem observationEntropyRate_le_window_conditional
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hQ : ∀ a, MeasurableSet {y | Q y=a}) {q : ℕ} (hq : 0 < q) (W : ℕ) :
    observationEntropyRate μ T P ≤ observationEntropyRate μ T Q+
      conditionalObservationEntropy μ (orbitName T P q) (orbitName T Q W)/(q : ℝ) := by
  have H := observationEntropyRate_le_add_conditional μ (hT.iterate q)
    (orbitName T P q) (orbitName T Q W)
    (orbitName_measurable_fiber hT.measurable hP q)
    (orbitName_measurable_fiber hT.measurable hQ W)
  rw [observationEntropyRate_blocks μ hT P hP hq] at H
  have H' := observationEntropyRate_sampled_window_le μ hT Q hQ hq W
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  apply (mul_le_mul_iff_right₀ hqr).mp
  rw [mul_add,mul_div_cancel₀ _ hqr.ne']
  nlinarith [H.trans (add_le_add H' le_rfl)]

end DukePrimeDegree

end

end OAI
