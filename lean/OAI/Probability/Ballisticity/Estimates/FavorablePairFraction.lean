import Mathlib
import OAI.Probability.Ballisticity.Estimates.UniformSpreadSequences

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma favorable_pair_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B C : Set Ω)
    (_ : MeasurableSet A) (_ : MeasurableSet B) (_ : MeasurableSet C)
    {p ε : ℝ} (hp : p ≤ μ.real A)
    (hBbad : μ.real Bᶜ ≤ ε) (hCbad : μ.real Cᶜ ≤ ε) :
    p-2*ε ≤ μ.real (A ∩ B ∩ C) := by
  have hs : A ⊆ (A ∩ B ∩ C) ∪ (Bᶜ ∪ Cᶜ) := by
    intro ω hω
    by_cases hb : ω ∈ B
    · by_cases hc : ω ∈ C
      · exact Or.inl ⟨⟨hω,hb⟩,hc⟩
      · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hb)
  have hh := (measureReal_mono (μ := μ) hs).trans
    (measureReal_union_le (A ∩ B ∩ C) (Bᶜ ∪ Cᶜ))
  have hh' := measureReal_union_le (μ := μ) Bᶜ Cᶜ
  linarith

lemma favorable_fraction_probability {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    (μ : Measure Ω) (π : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (A : Ω → I → Prop) (hA : MeasurableSet {p : Ω × I | A p.1 p.2})
    {p : ℝ} (hp : 0 ≤ p) (hpoint : ∀ x, p ≤ μ.real {ω | A ω x}) :
    p/2 ≤ μ.real {ω | p/2 ≤ ∫ x, if A ω x then (1:ℝ) else 0 ∂π} := by
  let F := fun ω x => if A ω x then (1:ℝ) else 0
  have hm : Measurable (Function.uncurry F) := measurable_const.piecewise hA measurable_const
  have hFi : Integrable (Function.uncurry F) (μ.prod π) :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun z => by dsimp [Function.uncurry,F]; split_ifs <;> simp)
  have hmb : Measurable (fun ω => ∫ x, F ω x ∂π) := hm.stronglyMeasurable.integral_prod_right.measurable
  have hi : p ≤ ∫ ω, ∫ x, F ω x ∂π ∂μ := by
    rw [integral_integral_swap hFi]
    have hh : ∀ x, p ≤ ∫ ω, F ω x ∂μ := by
      intro x
      have hs : MeasurableSet {ω | A ω x} := hA.preimage (measurable_id.prodMk measurable_const)
      have he : (fun ω => F ω x) = ({ω | A ω x}).indicator (fun _ => (1:ℝ)) := by
        funext ω; simp [F,Set.indicator]
      rw [he,integral_indicator hs]
      simpa using hpoint x
    simpa using integral_mono (integrable_const p)
      (hFi.integral_prod_right) hh
  apply bounded_mean_probability_lower μ (fun ω => ∫ x, F ω x ∂π) hmb
    (fun ω => integral_nonneg fun x => by dsimp [F]; split_ifs <;> norm_num)
    (fun ω => ?_) hp hi
  have hf : Integrable (F ω) π := (integrable_const (1:ℝ)).mono'
    ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun x => by dsimp [F]; split_ifs <;> simp)
  simpa using integral_mono hf (integrable_const (1:ℝ))
    (fun x => by dsimp [F]; split_ifs <;> norm_num)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma integral_le_of_tail_domination {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α → ℝ) (g : β → ℝ)
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[ν] g) {C : ℝ} (hC : 0 ≤ C)
    (ht : ∀ t > 0, μ {x | t < f x} ≤ ENNReal.ofReal C * ν {y | t < g y}) :
    (∫ x, f x ∂μ) ≤ C * ∫ y, g y ∂ν := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg_of_ae hg0))).mp
  rw [ENNReal.ofReal_mul hC,ofReal_integral_eq_lintegral_ofReal hf hf0,
    ofReal_integral_eq_lintegral_ofReal hg hg0,
    lintegral_eq_lintegral_meas_lt μ hf0 hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν hg0 hg.aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
  exact setLIntegral_mono' measurableSet_Ioi (fun t ht' => ht t ht')

noncomputable def capExcessTest (a D : ℝ) : C(unitInterval,ℝ) :=
  ⟨fun x => max ((min (D*(x:ℝ)) 1)^2-a^2) 0,by fun_prop⟩

lemma capExcessTest_nonneg (a D : ℝ) (x : unitInterval) : 0 ≤ capExcessTest a D x :=
  le_max_right _ _

lemma capExcessTest_tail {a D t : ℝ} (hD : 0 < D) (ht : 0 < t)
    (_ : 0 ≤ a) (hsmall : Real.sqrt (t+a^2) < 1) :
    {x : unitInterval | t < capExcessTest a D x} =
      {x : unitInterval | Real.sqrt (t+a^2)/D < (x:ℝ)} := by
  ext x
  have hsq : 0 ≤ t+a^2 := by positivity
  have hm : 0 ≤ min (D*(x:ℝ)) 1 := le_min (mul_nonneg hD.le x.2.1) zero_le_one
  have hroot := Real.sq_sqrt hsq
  have hrt := Real.sqrt_nonneg (t+a^2)
  change t < max ((min (D*(x:ℝ)) 1)^2-a^2) 0 ↔ _
  rw [lt_max_iff]
  simp only [not_lt.mpr ht.le,or_false]
  change t < min (D*(x:ℝ)) 1 ^ 2 - a ^ 2 ↔ Real.sqrt (t+a^2)/D < (x:ℝ)
  rw [div_lt_iff₀ hD]
  constructor
  · intro h
    have hh : Real.sqrt (t+a^2) < min (D*(x:ℝ)) 1 := by nlinarith
    exact (hh.trans_le (min_le_left _ _)).trans_eq (mul_comm _ _)
  · intro h
    have hh : Real.sqrt (t+a^2) < min (D*(x:ℝ)) 1 := lt_min (by nlinarith) hsmall
    nlinarith

lemma capExcessTest_tail_empty {a D t : ℝ} (hD : 0 ≤ D) (ht : 0 < t)
    (hlarge : 1 ≤ Real.sqrt (t+a^2)) :
    {x : unitInterval | t < capExcessTest a D x} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hm0 : 0 ≤ min (D*(x:ℝ)) 1 := le_min (mul_nonneg hD x.2.1) zero_le_one
  have hm1 := min_le_right (D*(x:ℝ)) 1
  have hsq := Real.sq_sqrt (show 0 ≤ t+a^2 by positivity)
  change t < max ((min (D*(x:ℝ)) 1)^2-a^2) 0 at hx
  rcases lt_max_iff.mp hx with hx | hx <;> nlinarith

lemma capExcess_integral_comparison (μ ν : ProbabilityMeasure unitInterval)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (htail : ∀ u > 0, (μ : Measure unitInterval) {x | u < (x:ℝ)} ≤
      ENNReal.ofReal C * (ν : Measure unitInterval) {y | u/D < (y:ℝ)})
    (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, capExcessTest a 1 x ∂(μ : Measure unitInterval)) ≤
      C * ∫ y, capExcessTest a D y ∂(ν : Measure unitInterval) := by
  apply integral_le_of_tail_domination _ _ _ _
    ((capExcessTest a 1).continuous.integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace _))
    ((capExcessTest a D).continuous.integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace _))
    (ae_of_all _ (capExcessTest_nonneg a 1)) (ae_of_all _ (capExcessTest_nonneg a D)) hC
  intro t ht
  by_cases hh : Real.sqrt (t+a^2) < 1
  · rw [capExcessTest_tail (by norm_num : (0:ℝ)<1) ht ha hh,
      capExcessTest_tail hD ht ha hh,div_one]
    exact htail _ (Real.sqrt_pos.mpr (by positivity))
  · rw [capExcessTest_tail_empty (by norm_num : (0:ℝ)≤1) ht (le_of_not_gt hh)]
    simp

lemma capped_tail_le_excess (x : unitInterval) {A : ℝ} (hA : 0 < A) (_ : A ≤ 1) :
    (if A < (x:ℝ) then (x:ℝ)^2 else 0) ≤ 2 * capExcessTest (A/2) 1 x := by
  have hx0 := x.2.1
  have hx1 := x.2.2
  change _ ≤ 2 * max ((min (1*(x:ℝ)) 1)^2-(A/2)^2) 0
  rw [one_mul,min_eq_left hx1]
  split_ifs with h
  · have hm := le_max_left ((x:ℝ)^2-(A/2)^2) 0
    nlinarith
  · positivity

lemma capExcess_le_scaled_tail (y : unitInterval) {a D : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    capExcessTest a D y ≤ D^2 * (if a/D < (y:ℝ) then (y:ℝ)^2 else 0) := by
  have hy0 := y.2.1
  have hm0 : 0 ≤ min (D*(y:ℝ)) 1 := le_min (mul_nonneg hD.le hy0) zero_le_one
  have hmy := min_le_left (D*(y:ℝ)) 1
  change max ((min (D*(y:ℝ)) 1)^2-a^2) 0 ≤ _
  split_ifs with h
  · apply max_le <;> nlinarith [sq_nonneg a]
  · have hh : D*(y:ℝ) ≤ a := by
      have hh := (le_div_iff₀ hD).mp (le_of_not_gt h)
      nlinarith
    apply max_le <;> nlinarith [sq_nonneg a]

end DirectionalTransience

end

end

end OAI
