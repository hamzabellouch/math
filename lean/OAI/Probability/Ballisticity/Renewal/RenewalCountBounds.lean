import Mathlib
import OAI.Probability.Ballisticity.Estimates.OrderedTimes

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma renewalCount_eq_of_bounds (L : ℕ → ℕ) (hL : ∀ k, 0 < L k)
    {h k : ℕ} (hl : renewalSum L k ≤ h) (hu : h < renewalSum L (k+1)) :
    renewalCount L h = k := by
  have hm := renewalSum_strictMono L hL
  have hl' := renewalCount_lower L h
  have hu' := renewalCount_upper L hL h
  apply le_antisymm
  · by_contra! hh
    have := hm.monotone (show k+1 ≤ renewalCount L h by omega)
    omega
  · by_contra! hh
    have := hm.monotone (show renewalCount L h+1 ≤ k by omega)
    omega

lemma renewalCount_at_sum (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) (k : ℕ) :
    renewalCount L (renewalSum L k) = k :=
  renewalCount_eq_of_bounds L hL le_rfl ((renewalSum_strictMono L hL) (Nat.lt_succ_self k))

lemma measurable_renewalSum {Ω : Type*} [MeasurableSpace Ω]
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k)) (n : ℕ) :
    Measurable (fun ω => renewalSum (fun k => L k ω) n) :=
  Finset.measurable_fun_sum _ (fun k _ => hL k)

lemma integral_nat_event_indicator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω) [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    (∫ ω, if ω ∈ A then (1:ℝ) else 0 ∂μ) = μ.real A := by
  simpa only [Set.indicator_apply,smul_eq_mul,mul_one] using integral_indicator_const (1:ℝ) hA

lemma renewal_occupation_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ → Ω → ℕ)
    (hL : ∀ k, Measurable (L k)) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) (s H : ℕ) :
    (∑ k ∈ Finset.range H, μ.real {ω | renewalSum (fun j => L j ω) k = s}) ≤ 1 := by
  classical
  let A := fun k => {ω | renewalSum (fun j => L j ω) k = s}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurableSet_eq_fun (measurable_renewalSum L hL k) measurable_const
  have hi (k : ℕ) : Integrable (fun ω => if ω ∈ A k then (1:ℝ) else 0) μ :=
    by
      apply ((integrable_const (μ := μ) (1:ℝ)).indicator (hA k)).congr
      filter_upwards [] with ω
      simp only [Set.indicator_apply]
  have he : (∑ k ∈ Finset.range H, μ.real (A k)) =
      ∫ ω, ∑ k ∈ Finset.range H, if ω ∈ A k then (1:ℝ) else 0 ∂μ := by
    rw [integral_finsetSum _ (fun k _ => hi k)]
    exact Finset.sum_congr rfl (fun k _ => (integral_nat_event_indicator μ (A k) (hA k)).symm)
  rw [he]
  calc
    _ ≤ ∫ _ : Ω, (1:ℝ) ∂μ := by
      apply integral_mono_ae (integrable_finsetSum _ (fun k _ => hi k)) (integrable_const _)
      filter_upwards [hpos] with ω hω
      calc
        _ ≤ ∑ k ∈ Finset.range H, if k = renewalCount (fun j => L j ω) s then (1:ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk : ω ∈ A k
          · have he := renewalCount_at_sum (fun j => L j ω) hω k
            change renewalSum (fun j => L j ω) k = s at hk
            rw [hk] at he
            simp [show ω ∈ A k from hk,he]
          · simp only [ite_eq_right hk]
            split_ifs <;> norm_num
        _ ≤ 1 := by simp only [Finset.sum_ite_eq']; split_ifs <;> norm_num
    _ = 1 := by simp

lemma renewal_selected_event_bound {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Ω → α)
    (hW : ∀ k, Measurable (W k)) (hind : iIndepFun W μ)
    (hident : ∀ k, IdentDistrib (W k) (W 0) μ μ)
    (L : α → ℕ) (hL : Measurable L) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L (W k ω))
    (hI : Integrable (fun ω => (L (W 0 ω) : ℝ)) μ)
    (A : Set α) (hA : MeasurableSet A) (h : ℕ) :
    μ.real {ω | W (renewalCount (fun j => L (W j ω)) h) ω ∈ A} ≤
      ∫ ω, if W 0 ω ∈ A then (L (W 0 ω) : ℝ) else 0 ∂μ := by
  classical
  let S := fun k ω => renewalSum (fun j => L (W j ω)) k
  let B := fun s => {a | a ∈ A ∧ h-s < L a}
  let E := fun k s => {ω | S k ω = s ∧ W k ω ∈ B s}
  have hB (s : ℕ) : MeasurableSet (B s) := hA.inter (measurableSet_lt measurable_const hL)
  have hSm (k : ℕ) : Measurable (S k) := measurable_renewalSum _ (fun j => hL.comp (hW j)) k
  have hE (k s : ℕ) : MeasurableSet (E k s) :=
    (measurableSet_eq_fun (hSm k) measurable_const).inter ((hW k) (hB s))
  have hsub : {ω | W (renewalCount (fun j => L (W j ω)) h) ω ∈ A} ≤ᵐ[μ]
      ⋃ k ∈ Finset.range (h+1), ⋃ s ∈ Finset.range (h+1), E k s := by
    filter_upwards [hpos] with ω hω ha
    let k := renewalCount (fun j => L (W j ω)) h
    have hk := renewalCount_le (fun j => L (W j ω)) h
    have hs := renewalCount_lower (fun j => L (W j ω)) h
    have hs' := renewalCount_upper (fun j => L (W j ω)) hω h
    rw [renewalSum_succ] at hs'
    refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),
      Set.mem_iUnion.mpr ⟨S k ω,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by dsimp [S,k]; omega),
        rfl,ha,?_⟩⟩⟩⟩
    dsimp [S,k]
    omega
  have hfactor (k s : ℕ) : μ.real (E k s) =
      μ.real {ω | S k ω = s} * μ.real (W 0 ⁻¹' B s) := by
    let F := fun w : Fin k → α => ∑ j : Fin k, L (w j)
    have hF : Measurable F := Finset.measurable_fun_sum _ (fun j _ => hL.comp (measurable_pi_apply j))
    have hind' := (independent_past_current μ W hW hind k).comp hF measurable_id
    have he : (fun ω => F (fun j : Fin k => W j ω)) = S k := by
      funext ω
      dsimp [F,S,renewalSum]
      exact Fin.sum_univ_eq_sum_range (fun j => L (W j ω)) k
    change IndepFun (fun ω => F (fun j : Fin k => W j ω)) (W k) μ at hind'
    rw [he] at hind'
    have hh := hind'.measure_inter_preimage_eq_mul {s} (B s) (measurableSet_singleton s) (hB s)
    have hid := (hident k).measure_mem_eq (hB s)
    change μ (E k s) = μ {ω | S k ω = s} * μ (W k ⁻¹' B s) at hh
    rw [hid] at hh
    exact congrArg ENNReal.toReal hh |>.trans ENNReal.toReal_mul
  calc
    _ ≤ μ.real (⋃ k ∈ Finset.range (h+1), ⋃ s ∈ Finset.range (h+1), E k s) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ ∑ k ∈ Finset.range (h+1), ∑ s ∈ Finset.range (h+1), μ.real (E k s) := by
      exact (measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun k _ => measureReal_biUnion_finset_le _ _))
    _ = ∑ s ∈ Finset.range (h+1),
        (∑ k ∈ Finset.range (h+1), μ.real {ω | S k ω = s}) * μ.real (W 0 ⁻¹' B s) := by
      simp_rw [hfactor]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ s ∈ Finset.range (h+1), μ.real (W 0 ⁻¹' B s) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_of_le_one_left measureReal_nonneg
        (renewal_occupation_upper μ _ (fun k => hL.comp (hW k)) hpos s (h+1))
    _ = ∑ s ∈ Finset.range (h+1), μ.real {ω | W 0 ω ∈ A ∧ s < L (W 0 ω)} := by
      simpa only [Nat.add_sub_cancel,B,Set.preimage_ofPred_eq] using
        Finset.sum_range_reflect (fun s => μ.real {ω | W 0 ω ∈ A ∧ s < L (W 0 ω)}) (h+1)
    _ ≤ _ := by
      let C := fun s => {ω | W 0 ω ∈ A ∧ s < L (W 0 ω)}
      have hC (s : ℕ) : MeasurableSet (C s) := ((hW 0) hA).inter
        (measurableSet_lt measurable_const (hL.comp (hW 0)))
      have hCi (s : ℕ) : Integrable (fun ω => if ω ∈ C s then (1:ℝ) else 0) μ :=
        by
          apply ((integrable_const (μ := μ) (1:ℝ)).indicator (hC s)).congr
          filter_upwards [] with ω
          simp only [Set.indicator_apply]
      calc
        _ = ∫ ω, ∑ s ∈ Finset.range (h+1), if ω ∈ C s then (1:ℝ) else 0 ∂μ := by
          rw [integral_finsetSum _ (fun s _ => hCi s)]
          exact Finset.sum_congr rfl (fun s _ => (integral_nat_event_indicator μ (C s) (hC s)).symm)
        _ ≤ _ := by
          apply integral_mono (integrable_finsetSum _ (fun s _ => hCi s)) (by
            apply (hI.indicator ((hW 0) hA)).congr
            filter_upwards [] with ω
            simp only [Set.indicator_apply,Set.mem_preimage])
          intro ω
          by_cases hω : W 0 ω ∈ A
          · simp only [C,Set.mem_ofPred_eq,hω,true_and,ite_eq_left]
            calc
              _ ≤ ∑ s ∈ Finset.range (L (W 0 ω)), (1:ℝ) := by
                rw [← Finset.sum_filter]
                exact Finset.sum_le_sum_of_subset_of_nonneg
                  (fun s hs => Finset.mem_range.mpr (Finset.mem_filter.mp hs).2)
                  (fun _ _ _ => zero_le_one)
              _ = _ := by simp
          · simp [C,hω]

lemma width_mark_tail_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : Ω → ℕ) (hL : Measurable L)
    (hI : Integrable (fun ω => (L ω : ℝ)) μ) (R : Ω → ℝ) (hR : Measurable R)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) :
    Tendsto (fun i => ∫ ω, if b i ≤ |R ω| then (L ω : ℝ) else 0 ∂μ) atTop (𝓝 0) := by
  have hm (i : ℕ) : Measurable (fun ω => if b i ≤ |R ω| then (L ω : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const hR.abs)
      ((measurable_of_countable (fun j : ℕ => (j:ℝ))).comp hL) measurable_const
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun i ω => if b i ≤ |R ω| then (L ω : ℝ) else 0) (f := fun _ => (0:ℝ))
    (fun ω => (L ω : ℝ)) (fun i => (hm i).aestronglyMeasurable) hI
    (fun i => Eventually.of_forall fun ω => by
      split_ifs <;> simp [Nat.cast_nonneg])
    (Eventually.of_forall fun ω => by
      apply tendsto_const_nhds.congr'
      filter_upwards [hb.eventually (eventually_gt_atTop |R ω|)] with i hi
      simp only [ite_eq_right (not_le_of_gt hi)])
  simpa only [integral_zero] using ht

theorem renewal_selected_mark_small {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Ω → α)
    (hW : ∀ k, Measurable (W k)) (hind : iIndepFun W μ)
    (hident : ∀ k, IdentDistrib (W k) (W 0) μ μ)
    (L : α → ℕ) (hL : Measurable L) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L (W k ω))
    (hI : Integrable (fun ω => (L (W 0 ω) : ℝ)) μ)
    (R : α → ℝ) (hR : Measurable R) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (h : ℕ → ℕ) :
    TendstoInMeasure μ (fun i ω => R (W (renewalCount (fun j => L (W j ω)) (h i)) ω)/r i)
      atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs]
  have ht := width_mark_tail_tendsto μ (fun ω => L (W 0 ω)) (hL.comp (hW 0)) hI
    (fun ω => R (W 0 ω)) (hR.comp (hW 0)) (fun i => ε*r i) (hr.const_mul_atTop hε)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht
  filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ))] with i hri
  have he : {ω | ε ≤ |R (W (renewalCount (fun j => L (W j ω)) (h i)) ω)/r i|} =
      {ω | W (renewalCount (fun j => L (W j ω)) (h i)) ω ∈ {a | ε*r i ≤ |R a|}} := by
    ext ω
    simp only [Set.mem_ofPred_eq,abs_div,abs_of_pos hri,le_div_iff₀ hri]
  rw [he]
  exact renewal_selected_event_bound μ W hW hind hident L hL hpos hI
    {a | ε*r i ≤ |R a|} (measurableSet_le measurable_const hR.abs) (h i)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
