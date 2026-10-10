import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeNormalizedEnergy

namespace OAI

/-! Both discarded logarithmic mass tails of the actual amplitude
levels have the manuscript's Q exp(-L/8) bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitudeLevel_discarded_sum (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (hf1 : Integrable (fun x => ‖f x‖) mu) (I : Finset ℤ) (M0 Q L : ℝ)
    (hM0 : 0<M0) (hQ : 0≤Q) (hinfty : ∀ x, ‖f x‖≤Q)
    (hL1 : (∫ x, ‖f x‖ ∂mu)≤Q*M0)
    (hpos : ∀ i∈I, 0<mu.real (amplitudeLevel f i))
    (hdiscard : ∀ i∈I, L/4 < |Real.log (mu.real (amplitudeLevel f i)/M0)|) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤
      (8+2*(2/(1-(Real.sqrt 2)⁻¹)))*Q*Real.exp (-L/8) := by
  classical
  let eps := Real.exp (-L/4)
  let P := fun i : ℤ => mu.real (amplitudeLevel f i)≤eps*M0
  have heps : 0<eps := Real.exp_pos _
  have hs := amplitudeLevel_small_tail mu f (I.filter P) M0 Q eps hM0 hQ heps.le hinfty
    (fun i hi => hpos i (Finset.mem_filter.mp hi).1)
    (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hl := amplitudeLevel_large_tail mu f hf hm hf1 (I.filter (fun i => ¬P i))
    M0 Q eps hM0 hQ heps hL1 (fun i hi => ?_)
  · have he : Real.sqrt eps=Real.exp (-L/8) := by
      rw [show eps=Real.exp (-L/4) from rfl,←Real.exp_half]
      congr 1
      ring
    calc
      _=(∑ i∈I.filter P, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))+
          ∑ i∈I.filter (fun i => ¬P i), (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0) :=
        (Finset.sum_filter_add_sum_filter_not I P _).symm
      _≤8*Q*Real.sqrt eps+2*(2/(1-(Real.sqrt 2)⁻¹))*Q*Real.sqrt eps := add_le_add hs hl
      _=_ := by rw [he]; ring
  · obtain ⟨hiI,hiP⟩ := Finset.mem_filter.mp hi
    have hratio : 0<mu.real (amplitudeLevel f i)/M0 := div_pos (hpos i hiI) hM0
    have hlow : -L/4<Real.log (mu.real (amplitudeLevel f i)/M0) := by
      apply Real.exp_lt_exp.mp
      rw [Real.exp_log hratio]
      exact (lt_div_iff₀ hM0).mpr (lt_of_not_ge hiP)
    have hhigh : L/4<Real.log (mu.real (amplitudeLevel f i)/M0) := by
      by_contra hh
      have habs := abs_le.mpr ⟨by linarith,le_of_not_gt hh⟩
      exact (not_le_of_gt (hdiscard i hiI)) habs
    have hr : Real.exp (L/4)*M0≤mu.real (amplitudeLevel f i) := by
      apply (le_div_iff₀ hM0).mp
      exact (Real.exp_lt_exp.mpr hhigh).le.trans_eq (Real.exp_log hratio)
    have hcancel : eps*Real.exp (L/4)=1 := by
      dsimp only [eps]
      rw [←Real.exp_add]
      rw [show (-L/4)+(L/4)=0 by ring,Real.exp_zero]
    calc
      M0=eps*(Real.exp (L/4)*M0) := by rw [←mul_assoc,hcancel,one_mul]
      _≤eps*mu.real (amplitudeLevel f i) := mul_le_mul_of_nonneg_left hr heps.le

end LipschitzHilbert

end

end OAI
