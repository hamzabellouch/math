import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevGaugeTransform
import OAI.Analysis.Conductivity.Sobolev.SobolevOuterTests

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem weighted_gauge_DN (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (c C : ℝ) (hc : 0<c) (hC : 0≤C)
    (hab : ∀ᵐ x ∂ballMeasure, c≤a x ∧ a x≤C)
    (w : H1) (hw0 : w∈H10) (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2)
    (r : ℝ) (hr : 0<r) (hr3 : r<3)
    (hsupp : ∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0)
    (hweighted : ∀ u : H1, Harmonic a u →
      (∃ M : ℝ, ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M) →
      ∃ d : ℝ, WeightedAnnihilation a w u d) :
    ∃ Λ : DNOperator, IsDirichletToNeumann a Λ ∧
      IsDirichletToNeumann (gaugeCoefficient a w) Λ := by
  have habs : ∀ᵐ x ∂ballMeasure, |a x|≤C := hab.mono
    (fun x hx => by rw [abs_of_nonneg (hc.le.trans hx.1)]; exact hx.2)
  obtain ⟨Λ₀,hΛ₀⟩ := exists_DirichletToNeumann a ha C hC habs c hc
    (hab.mono (fun _ hx => hx.1))
  have hbb := gaugeCoefficient_bounds hc hab hw
  have hbabs : ∀ᵐ x ∂ballMeasure, |gaugeCoefficient a w x|≤9*C/4 := hbb.mono
    (fun x hx => by rw [abs_of_nonneg ((div_pos hc (by norm_num)).le.trans hx.1)]; exact hx.2)
  obtain ⟨Λ₁,hΛ₁⟩ := exists_DirichletToNeumann _ (gaugeCoefficient_aeStronglyMeasurable a ha w)
    (9*C/4) (by positivity) hbabs (c/4) (by positivity) (hbb.mono (fun _ hx => hx.1))
  have heq : Λ₀=Λ₁ := by
    apply DN_eq_of_smooth_pairings
    intro f g hf hg
    obtain ⟨u,ht,hu,_,_⟩ := hΛ₀ (trace (smoothH1 f hf))
    obtain ⟨M,hM,hfM⟩ := smoothH1_bounded f hf
    have huM := harmonic_bounded_of_trace_bounded a ha C hC habs
      (hab.mono (fun _ hx => hc.trans_le hx.1)) hu ht hM hfM
    obtain ⟨d,hd⟩ := hweighted u hu ⟨M,huM⟩
    obtain ⟨u₁,ht₁,_,hflux⟩ := exists_gauge_transform huM hw hw0 d
    have hflux' : ∀ᵐ x ∂ballMeasure,
        gaugeCoefficient a w x • weakGradient u₁ x=
        ((1+weakValue w x)*a x) • weakGradient u x-
          ((weakValue u x-d)*a x) • weakGradient w x := hflux.mono (fun x hx => hx (a x))
    have hu₁ := gauge_harmonic_of_weighted a ha C hC habs huM hw hu d hd hflux'
    obtain ⟨N,_,hgN⟩ := smoothH1_bounded g hg
    obtain ⟨V,hV,hVg⟩ := exists_outer_test hgN hr hr3
    have he : energy a u V=energy (gaugeCoefficient a w) u₁ V := by
      apply integral_congr_ae
      filter_upwards [hflux',hsupp,hVg] with x hx hy hz
      by_cases hh : ‖x‖≤r
      · simp only [hz hh, inner_zero_right, mul_zero]
      · obtain ⟨hv,hg⟩ := hy (lt_of_not_ge hh)
        simp only [←real_inner_smul_left]
        rw [hx,hv,hg,smul_zero,sub_zero,add_zero,one_mul]
    calc
      Λ₀ (trace (smoothH1 f hf)) (trace (smoothH1 g hg)) = Λ₀ (trace u) (trace V) := by rw [ht,hV]
      _ = energy a u V := hΛ₀.pairing hu V
      _ = energy (gaugeCoefficient a w) u₁ V := he
      _ = Λ₁ (trace u₁) (trace V) := (hΛ₁.pairing hu₁ V).symm
      _ = Λ₁ (trace (smoothH1 f hf)) (trace (smoothH1 g hg)) := by rw [ht₁,ht,hV]
  exact ⟨Λ₀,hΛ₀,heq.symm ▸ hΛ₁⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma weakValue_measurable (w : H1) : Measurable (weakValue w) :=
  jetValue.continuous.measurable.comp (Lp.stronglyMeasurable w.val).measurable

lemma gaugeCoefficient_measurable {a : R3 → ℝ} (ha : Measurable a) (w : H1) :
    Measurable (gaugeCoefficient a w) :=
  ha.mul ((measurable_const.add (weakValue_measurable w)).pow_const 2)

lemma gaugeCoefficient_ne_ae_iff {a : R3 → ℝ} {w : H1}
    (ha : ∀ᵐ x ∂ballMeasure, 0<a x)
    (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2) :
    ∀ᵐ x ∂ballMeasure, a x≠gaugeCoefficient a w x ↔ weakValue w x≠0 := by
  filter_upwards [ha,hw] with x ha hw
  apply not_congr
  change a x=a x*(1+weakValue w x)^2 ↔ weakValue w x=0
  constructor
  · intro h
    have hs : (1+weakValue w x)^2=1 := by
      apply mul_left_cancel₀ ha.ne'
      simpa only [mul_one] using h.symm
    have hm : weakValue w x*(2+weakValue w x)=0 := by nlinarith
    have hp : 0<2+weakValue w x := by have := (abs_le.mp hw).1; linarith
    exact (mul_eq_zero.mp hm).resolve_right hp.ne'
  · intro h; simp [h]

lemma gaugeCoefficient_equalOneNearBoundary {a : R3 → ℝ} {w : H1}
    (ha : EqualOneNearBoundary a) {r : ℝ} (hr : 0<r) (hr3 : r<3)
    (hsupp : ∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0) :
    EqualOneNearBoundary (gaugeCoefficient a w) := by
  obtain ⟨q,_,hq3,hqa⟩ := ha
  refine ⟨max q r,lt_of_lt_of_le hr (le_max_right _ _),max_lt hq3 hr3,?_⟩
  filter_upwards [hsupp,hqa] with x hx hy
  intro hn
  have hwr := hx (lt_of_le_of_lt (le_max_right _ _) hn)
  have har := hy (lt_of_le_of_lt (le_max_left _ _) hn)
  simp only [gaugeCoefficient,hwr,har,add_zero,one_pow,mul_one]

theorem MainStatement_of_weighted_source
    (a : R3 → ℝ) (ha : Measurable a) (c C : ℝ) (hc : 0<c) (hcC : c<C)
    (hab : ∀ᵐ x ∂ballMeasure, c≤a x ∧ a x≤C) (hnear : EqualOneNearBoundary a)
    (w : H1) (hw0 : w∈H10) (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2)
    (hwne : 0<ballMeasure {x | weakValue w x≠0})
    (r : ℝ) (hr : 0<r) (hr3 : r<3)
    (hsupp : ∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0)
    (hweighted : ∀ u : H1, Harmonic a u →
      (∃ M : ℝ, ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M) →
      ∃ d : ℝ, WeightedAnnihilation a w u d) : MainStatement := by
  have hC : 0<C := hc.trans hcC
  have habs : ∀ᵐ x ∂ballMeasure, |a x|≤C := hab.mono
    (fun x hx => by rw [abs_of_nonneg (hc.le.trans hx.1)]; exact hx.2)
  have hbb := gaugeCoefficient_bounds hc hab hw
  have hbabs : ∀ᵐ x ∂ballMeasure, |gaugeCoefficient a w x|≤9*C/4 := hbb.mono
    (fun x hx => by rw [abs_of_nonneg ((div_pos hc (by norm_num)).le.trans hx.1)]; exact hx.2)
  have ham : MemLp a ∞ ballMeasure := MemLp.of_bound ha.aestronglyMeasurable C
    (by simpa only [Real.norm_eq_abs] using habs)
  have hbm : MemLp (gaugeCoefficient a w) ∞ ballMeasure :=
    MemLp.of_bound (gaugeCoefficient_aeStronglyMeasurable a ha.aestronglyMeasurable w) (9*C/4)
      (by simpa only [Real.norm_eq_abs] using hbabs)
  obtain ⟨Λ,hΛ₀,hΛ₁⟩ := weighted_gauge_DN a ha.aestronglyMeasurable c C hc hC.le hab
    w hw0 hw r hr hr3 hsupp hweighted
  refine ⟨a,gaugeCoefficient a w,c/4,9*C/4+1,Λ,by positivity,by linarith,
    ha,gaugeCoefficient_measurable ha w,ham,hbm,?_,?_,hnear,?_,?_,hΛ₀,hΛ₁⟩
  · filter_upwards [hab] with x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · filter_upwards [hbb] with x hx
    exact ⟨hx.1,by linarith [hx.2]⟩
  · exact gaugeCoefficient_equalOneNearBoundary hnear hr hr3
      (hsupp.mono (fun _ hx h => (hx h).1))
  · have he := gaugeCoefficient_ne_ae_iff (hab.mono (fun _ hx => hc.trans_le hx.1)) hw
    have hm : ballMeasure {x | a x≠gaugeCoefficient a w x}=ballMeasure {x | weakValue w x≠0} :=
      measure_congr (he.mono (fun _ hx => propext hx))
    rw [hm]; exact hwne

end ScalarConductivity

end
end

end OAI
