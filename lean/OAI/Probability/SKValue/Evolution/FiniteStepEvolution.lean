import Mathlib
import OAI.Probability.SKValue.Control.ControlValue
import OAI.Probability.SKValue.Evolution.EvolutionPatch
import OAI.Probability.SKValue.Evolution.EvolveStrips
import OAI.Probability.SKValue.Evolution.SmoothEvolution
import OAI.Probability.SKValue.Evolution.TimePatch

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

abbrev HeatProfile := List (ℝ≥0 × ℝ≥0)

noncomputable def profileTime : HeatProfile → ℝ
  | [] => 0
  | p::l => (p.1 : ℝ)+profileTime l

noncomputable def profileCoeff : HeatProfile → ℝ → ℝ
  | [] => fun _ ↦ 0
  | p::l => patchTime (p.1 : ℝ) (fun _ ↦ (p.2 : ℝ)) (profileCoeff l)

noncomputable def profileValue (ψ : ℝ → ℝ) : HeatProfile → ℝ → ℝ → ℝ
  | [] => fun _ ↦ ψ
  | p::l => patchTime (p.1 : ℝ)
    (fun t ↦ coleHopf (p.2 : ℝ) ((p.1 : ℝ)-t) (profileValue ψ l 0)) (profileValue ψ l)

lemma profileTime_nonneg (l : HeatProfile) : 0≤profileTime l := by
  induction l with
  | nil => exact le_rfl
  | cons p l ih => exact add_nonneg p.1.coe_nonneg ih

lemma profileCoeff_nonneg (l : HeatProfile) (t : ℝ) : 0≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact le_rfl
  | cons p l ih =>
    change 0≤patchTime _ _ _ t
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht]
      exact p.2.coe_nonneg
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _

lemma profileCoeff_integrable (l : HeatProfile) :
    IntervalIntegrable (profileCoeff l) volume 0 (profileTime l) := by
  induction l with
  | nil => exact intervalIntegrable_const
  | cons p l ih =>
    exact patchTime_intervalIntegrable p.1.coe_nonneg (profileTime_nonneg l) intervalIntegrable_const ih

lemma profileCoeff_measurable (l : HeatProfile) : Measurable (profileCoeff l) := by
  induction l with
  | nil => exact measurable_const
  | cons p l ih =>
    unfold profileCoeff patchTime
    exact Measurable.ite measurableSet_Iic measurable_const (ih.comp (measurable_id.sub measurable_const))

lemma SmoothTerminal.zero_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) :
    SmoothEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) := by
  refine ⟨fun _ _ ↦ hψ,fun _ ↦ continuousOn_const,fun _ _ ↦ continuousOn_const,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    exact ⟨C,hC,fun _ _ ↦ hb⟩
  · intro n
    exact ⟨0,le_rfl,by intros; simp⟩
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp

lemma SmoothTerminal.profile_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (l : HeatProfile) :
    SmoothEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) := by
  induction l with
  | nil => exact hψ.zero_evolution
  | cons p l ih =>
    have hv : SmoothTerminal (profileValue ψ l 0) := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hc := hv.constant_evolution p.2.coe_nonneg (p.1 : ℝ)
    apply hc.patch p.1.coe_nonneg (profileTime_nonneg l) ih intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,coleHopf_zero]

lemma patchTime_end {E : Type*} {a b : ℝ} (hb : 0≤b) {f g : ℝ → E} (hfg : f a=g 0) :
    patchTime a f g (a+b)=g b := by
  rcases hb.eq_or_lt with rfl | hb
  · simpa only [add_zero,patchTime_left f g le_rfl] using hfg
  · rw [patchTime_right f g (lt_add_of_pos_right a hb)]
    congr 1
    ring

lemma profileValue_terminal (ψ : ℝ → ℝ) (l : HeatProfile) :
    profileValue ψ l (profileTime l)=ψ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change patchTime _ _ _ ((p.1 : ℝ)+profileTime l)=ψ
    rw [patchTime_end (profileTime_nonneg l)]
    · exact ih
    · funext x
      simp only [sub_self,coleHopf_zero]

lemma profileCoeff_lower {l : HeatProfile} {c : ℝ}
    (hc : ∀ p∈l, c≤(p.2 : ℝ)) {t : ℝ} (ht : t∈Ioc (0 : ℝ) (profileTime l)) :
    c≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact (not_lt_of_ge ht.2 ht.1).elim
  | cons p l ih =>
    change c≤patchTime (p.1 : ℝ) _ _ t
    by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hta]
      exact hc p (by simp)
    · rw [patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih (fun q hq ↦ hc q (by simp [hq]))
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩

lemma profileCoeff_mono {l : HeatProfile} (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) :
    MonotoneOn (profileCoeff l) (Icc (0 : ℝ) (profileTime l)) := by
  induction l with
  | nil => intro s hs t ht hst; exact le_rfl
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp hl
    intro s hs t ht hst
    change patchTime (p.1 : ℝ) _ _ s≤patchTime (p.1 : ℝ) _ _ t
    by_cases hsa : s≤(p.1 : ℝ) <;> by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hsa,patchTime_left _ _ hta]
    · rw [patchTime_left _ _ hsa,patchTime_right _ _ (lt_of_not_ge hta)]
      apply profileCoeff_lower (fun q hq ↦ by exact_mod_cast hp q hq)
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
    · exact (hsa (hst.trans hta)).elim
    · rw [patchTime_right _ _ (lt_of_not_ge hsa),patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih hl
      · exact ⟨by linarith,by have hsu : s≤(p.1 : ℝ)+profileTime l := hs.2; linarith⟩
      · exact ⟨by linarith,by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
      · linarith

theorem SmoothTerminal.profile_control_value
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBm : ∀ t, StronglyMeasurable (B t))
    {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {l : HeatProfile}
    (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) (hT : 0<profileTime l) (hT1 : profileTime l≤1) :
    sSup {r | ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B hBm) α ∧ (∀ s ω, |α s ω|≤1) ∧
      r=∫ ω, ψ (controlState B (profileCoeff l) α 0 (profileTime l) ω)-
        (1/2 : ℝ)*controlAccum (profileCoeff l) α 2 (profileTime l) ω ∂μ} =
      profileValue ψ l 0 0 := by
  obtain ⟨K,L,hstrip⟩ := (hψ.profile_evolution l).toValueStrip hT.le
    (fun t _ ↦ profileCoeff_nonneg l t) (profileCoeff_mono hl)
  have he := hstrip.progressive_control_value hB hBm hT hT1 (profileCoeff_measurable l)
  simpa only [profileValue_terminal] using he

end SKValue

end

end OAI
