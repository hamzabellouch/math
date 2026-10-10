import Mathlib
import OAI.Probability.SKValue.Evolution.FiniteStepEvolution
import OAI.Probability.SKValue.Evolution.EvolutionShift

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma SmoothEvolution.progressive_control_from
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBm : ∀ s, StronglyMeasurable (B s))
    {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (ha : 0≤a) (hab : a<b) (hb : b≤T) (hd : b-a≤1)
    (hγ : ∀ t∈Icc (0 : ℝ) T, 0≤γ t) (hm : MonotoneOn γ (Icc (0 : ℝ) T))
    (hM : Measurable γ) (x : ℝ) :
    sSup {r | ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B hBm) α ∧ (∀ s ω, |α s ω|≤1) ∧
      r=∫ ω, V b (x+controlState B (fun s ↦ γ (a+s)) α 0 (b-a) ω)-
        (1/2 : ℝ)*controlAccum (fun s ↦ γ (a+s)) α 2 (b-a) ω ∂μ} = V a x := by
  have hmem (s : ℝ) (hs : s∈Icc (0 : ℝ) (b-a)) : a+s∈Icc (0 : ℝ) T := by
    constructor <;> linarith [hs.1,hs.2]
  obtain ⟨K,L,hstrip⟩ := ((h.time_shift ha hab.le hb).space_translate x).toValueStrip
    (sub_nonneg.mpr hab.le) (fun s hs ↦ hγ _ (hmem s hs))
    (fun s hs t ht hst ↦ hm (hmem s hs) (hmem t ht) (add_le_add le_rfl hst))
  have he := hstrip.progressive_control_value hB hBm (sub_pos.mpr hab) hd
    (hM.comp (measurable_const.add measurable_id))
  simpa only [add_sub_cancel,add_zero] using he

theorem SmoothTerminal.profile_control_from (W : BrownianSpace)
    {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {l : HeatProfile}
    (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) (hT : profileTime l=1)
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) (x : ℝ) :
    sSup {r | ∃ α : ℝ≥0 → W.Ω → ℝ, Admissible W t α ∧
      r=∫ ω, ψ (x+W.B 1 ω-W.B t.toNNReal ω+
        ∫ s in (0 : ℝ)..(1-t), profileCoeff l (t+s)*α s.toNNReal ω)-
        (1/2 : ℝ)*(∫ s in (0 : ℝ)..(1-t), profileCoeff l (t+s)*(α s.toNNReal ω)^2) ∂W.μ} =
      profileValue ψ l t x := by
  let B := fun s ω ↦ W.B (t.toNNReal+s) ω-W.B t.toNNReal ω
  have hm : ∀ s, StronglyMeasurable (B s) := fun s ↦ (W.measurable _).sub (W.measurable _)
  have he := (hψ.profile_evolution l).progressive_control_from
    (W.brownian.toIsPreBrownianReal.shift t.toNNReal) hm ht.1 ht.2 (by rw [hT])
    (by linarith [ht.1]) (fun s _ ↦ profileCoeff_nonneg l s) (profileCoeff_mono hl)
    (profileCoeff_measurable l) x
  have hend : t.toNNReal+(1-t).toNNReal=1 := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ ht.1,Real.coe_toNNReal _ (sub_nonneg.mpr ht.2.le),NNReal.coe_one]
    ring
  have hv : profileValue ψ l 1=ψ := hT ▸ profileValue_terminal ψ l
  change sSup {r | ∃ α, Admissible W t α ∧ r=_}= _
  convert he using 1
  congr 1
  ext r
  simp only [Admissible,shiftedFiltration,and_assoc,hv,controlState,controlAccum,pow_one,zero_add,
    sub_eq_add_neg,add_assoc]
  simp only [←sub_eq_add_neg,hend]

end SKValue

end

end OAI
