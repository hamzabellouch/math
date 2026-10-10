import Mathlib

namespace OAI

section

open Set Filter Metric

namespace CAT0Fillings.JointBV
universe u v
lemma totallyBounded_range_of_finite_coordinate_control {ι : Type*} {α : Type u}
    [PseudoMetricSpace α] {β : ℕ → Type v} [∀ i, PseudoMetricSpace (β i)]
    [∀ i, CompleteSpace (β i)] {f : ι → α} {g : ∀ i, ι → β i}
    (hg : ∀ i, TotallyBounded (range (g i)))
    (hcontrol : ∀ ε > 0, ∃ N : ℕ, ∃ δ > 0,
      ∀ a b, (∀ i : Fin N, dist (g i a) (g i b) < δ) → dist (f a) (f b) < ε) :
    TotallyBounded (range f) := by
  classical
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  obtain ⟨N,δ,hδ,hc⟩ := hcontrol ε hε
  let G (a : ι) (i : Fin N) := g i a
  have hG : TotallyBounded (range G) := by
    apply (isCompact_pi_infinite (fun i : Fin N => ((hg i).closure.isCompact_of_isClosed isClosed_closure))).totallyBounded.subset
    rintro _ ⟨a,rfl⟩ i
    exact subset_closure (mem_range_self a)
  obtain ⟨s,hs,hfin,hcover⟩ := Metric.finite_approx_of_totallyBounded hG (δ/2) (half_pos hδ)
  have : Fintype s := hfin.fintype
  have hnear (a : ι) : ∃ y : s, dist (G a) y < δ/2 := by
    have := hcover (mem_range_self a)
    simp only [mem_iUnion,mem_ball] at this
    obtain ⟨y,hy,hay⟩ := this
    exact ⟨⟨y,hy⟩,hay⟩
  choose c hc' using hnear
  let pick (x : range f) : ι := x.property.choose
  have hp (x : range f) : f (pick x) = x := x.property.choose_spec
  refine ⟨ULift.{u} (Fin (Fintype.card s)),inferInstance,fun x => ULift.up ((Fintype.equivFin s) (c (pick x))),?_⟩
  intro x y he
  have he : c (pick x) = c (pick y) := (Fintype.equivFin s).injective (congrArg ULift.down he)
  rw [←hp x,←hp y]
  apply hc
  intro i
  apply (dist_le_pi_dist (G (pick x)) (G (pick y)) i).trans_lt
  calc dist (G (pick x)) (G (pick y)) ≤
      dist (G (pick x)) (c (pick x)) + dist (G (pick y)) (c (pick x)) := dist_triangle_right _ _ _
    _ < δ/2+δ/2 := add_lt_add (hc' _) (by rw [he]; exact hc' _)
    _ = δ := add_halves _

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.JointBV
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (ρ : α → ℕ) (hρ : Measurable ρ)

def indexTail (N : ℕ) (x : α) : ℝ := if N ≤ ρ x then 1 else 0

include hρ
lemma measurable_indexTail (N : ℕ) : Measurable (indexTail ρ N) :=
  measurable_const.ite (measurableSet_le measurable_const hρ) measurable_const

omit hρ in
lemma indexTail_bound {α : Type*} [MeasurableSpace α] (ρ : α → ℕ)
    (N : ℕ) (x : α) : |indexTail ρ N x| ≤ 1 := by
  unfold indexTail; split_ifs <;> norm_num

lemma memLp_indexTail (N : ℕ) : MemLp (indexTail ρ N) 2 μ :=
  MemLp.of_bound (measurable_indexTail ρ hρ N).aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using indexTail_bound ρ N x)

omit hρ in
lemma lpNorm_indexTail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ : α → ℕ) (hρ : Measurable ρ) (N : ℕ) :
    lpNorm (indexTail ρ N) 2 μ = (μ.real {x | N ≤ ρ x}) ^ (1/(2:ℝ)) := by
  rw [←toReal_eLpNorm]
  have he : indexTail ρ N = {x | N ≤ ρ x}.indicator (fun _ => (1:ℝ)) := by
    ext x; simp only [indexTail,Set.indicator_apply,mem_ofPred_eq]
  rw [he, eLpNorm_indicator_const (s := {x | N ≤ ρ x})
    (measurableSet_le measurable_const hρ).nullMeasurableSet (by norm_num) (by norm_num)]
  simp [ENNReal.toReal_rpow,measureReal_def]

lemma tendsto_lpNorm_indexTail : Tendsto (fun N => lpNorm (indexTail ρ N) 2 μ) atTop (𝓝 0) := by
  have hsets : (⋂ N : ℕ, {x | N ≤ ρ x}) = ∅ := by
    ext x
    simp only [mem_iInter,mem_ofPred_eq,mem_empty_iff_false,iff_false]
    intro hx
    exact Nat.not_succ_le_self (ρ x) (hx (ρ x+1))
  have hm : Tendsto (fun N => μ {x | N ≤ ρ x}) atTop (𝓝 0) := by
    simpa only [Function.comp_def,hsets,measure_empty] using
      tendsto_measure_iInter_atTop (μ := μ) (fun N => (measurableSet_le measurable_const hρ).nullMeasurableSet)
        (show Antitone (fun N : ℕ => {x | N ≤ ρ x}) by intro N M hNM x hx; exact hNM.trans hx)
        ⟨0,measure_ne_top _ _⟩
  have hr : Tendsto (fun N => μ.real {x | N ≤ ρ x}) atTop (𝓝 0) := by
    simpa only [measureReal_def,ENNReal.toReal_zero,Function.comp_def] using (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp hm
  simpa only [lpNorm_indexTail μ ρ hρ,Real.zero_rpow (by norm_num : (1/(2:ℝ)) ≠ 0)] using
    (hr.rpow_const (by norm_num : (0:ℝ) ≠ 0 ∨ 0 ≤ 1/(2:ℝ)))

end CAT0Fillings.JointBV
end

end OAI
