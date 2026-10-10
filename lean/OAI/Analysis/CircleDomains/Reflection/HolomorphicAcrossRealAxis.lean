import Mathlib.Analysis.Complex.HasPrimitives

namespace OAI

/-! A continuous complex function holomorphic off the real axis is
holomorphic across it. Rectangles are split at the axis and their
common horizontal integrals cancel. This is the gluing step needed
for Schwarz reflection, proved directly from Cauchy--Goursat. -/
open Set Complex MeasureTheory
open scoped Interval Topology
noncomputable section
namespace CircleDomainRigidity

private def rectangleFlux (f : ℂ → ℂ) (a b u v : ℝ) : ℂ :=
  (∫ x in a..b, f (x+u*I)) - (∫ x in a..b, f (x+v*I)) +
    I • (∫ y in u..v, f (b+y*I)) - I • (∫ y in u..v, f (a+y*I))

private lemma rectangleFlux_one_side {f : ℂ → ℂ} {a b u v : ℝ}
    (hc : ContinuousOn f (uIcc a b ×ℂ uIcc u v))
    (hd : ∀ z ∈ uIcc a b ×ℂ uIcc u v, z.im≠0 → DifferentiableAt ℂ f z)
    (hs : (0≤u ∧ 0≤v) ∨ (u≤0 ∧ v≤0)) : rectangleFlux f a b u v=0 := by
  apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (⟨a,u⟩ : ℂ) (⟨b,v⟩ : ℂ) hc
  intro z hz
  have hz' : z ∈ uIcc a b ×ℂ uIcc u v :=
    ⟨⟨hz.1.1.le,hz.1.2.le⟩,⟨hz.2.1.le,hz.2.2.le⟩⟩
  apply (hd z hz' ?_).differentiableWithinAt
  rcases hs with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · exact ne_of_gt (lt_of_le_of_lt (le_min hu hv) hz.2.1)
  · exact ne_of_lt (lt_of_lt_of_le hz.2.2 (max_le hu hv))

private lemma vertical_integrable {f : ℂ → ℂ} {a b u v x : ℝ}
    (hc : ContinuousOn f (uIcc a b ×ℂ uIcc u v)) (hx : x∈uIcc a b) :
    IntervalIntegrable (fun y : ℝ => f (x+y*I)) volume u v := by
  apply ContinuousOn.intervalIntegrable
  apply hc.comp (by fun_prop)
  intro y hy
  simpa only [mem_reProdIm,add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,
    I_im,zero_mul,sub_zero,add_zero,add_im,mul_im,mul_one,zero_add] using And.intro hx hy

private lemma rectangleFlux_split {f : ℂ → ℂ} {a b u v t : ℝ}
    (hc : ContinuousOn f (uIcc a b ×ℂ uIcc u v)) (ht : t∈uIcc u v) :
    rectangleFlux f a b u v=rectangleFlux f a b u t+rectangleFlux f a b t v := by
  have hc₁ : ContinuousOn f (uIcc a b ×ℂ uIcc u t) :=
    hc.mono (fun _ hz => ⟨hz.1,uIcc_subset_uIcc_left ht hz.2⟩)
  have hc₂ : ContinuousOn f (uIcc a b ×ℂ uIcc t v) :=
    hc.mono (fun _ hz => ⟨hz.1,uIcc_subset_uIcc_right ht hz.2⟩)
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (vertical_integrable hc₁ (left_mem_uIcc : a∈uIcc a b))
    (vertical_integrable hc₂ (left_mem_uIcc : a∈uIcc a b))
  have hb := intervalIntegral.integral_add_adjacent_intervals
    (vertical_integrable hc₁ (right_mem_uIcc : b∈uIcc a b))
    (vertical_integrable hc₂ (right_mem_uIcc : b∈uIcc a b))
  dsimp only [rectangleFlux]
  rw [←ha,←hb,smul_add,smul_add]
  abel

private lemma rectangleFlux_off_real {f : ℂ → ℂ} {a b u v : ℝ}
    (hc : ContinuousOn f (uIcc a b ×ℂ uIcc u v))
    (hd : ∀z∈uIcc a b ×ℂ uIcc u v,z.im≠0 → DifferentiableAt ℂ f z) :
    rectangleFlux f a b u v=0 := by
  have hsplit (ht : 0∈uIcc u v)
      (hs₁ : (0≤u ∧ 0≤(0:ℝ)) ∨ (u≤0 ∧ (0:ℝ)≤0))
      (hs₂ : ((0:ℝ)≤0 ∧ 0≤v) ∨ ((0:ℝ)≤0 ∧ v≤0)) :
      rectangleFlux f a b u v=0 := by
    have hsub₁ : uIcc a b ×ℂ uIcc u 0 ⊆ uIcc a b ×ℂ uIcc u v :=
      fun _ hz => ⟨hz.1,uIcc_subset_uIcc_left ht hz.2⟩
    have hsub₂ : uIcc a b ×ℂ uIcc 0 v ⊆ uIcc a b ×ℂ uIcc u v :=
      fun _ hz => ⟨hz.1,uIcc_subset_uIcc_right ht hz.2⟩
    rw [rectangleFlux_split hc ht,
      rectangleFlux_one_side (hc.mono hsub₁) (fun z hz => hd z (hsub₁ hz)) hs₁,
      rectangleFlux_one_side (hc.mono hsub₂) (fun z hz => hd z (hsub₂ hz)) hs₂,add_zero]
  rcases le_total u 0 with hu|hu <;> rcases le_total 0 v with hv|hv
  · exact hsplit (mem_uIcc_of_le hu hv) (Or.inr ⟨hu,le_rfl⟩) (Or.inl ⟨le_rfl,hv⟩)
  · exact rectangleFlux_one_side hc hd (Or.inr ⟨hu,hv⟩)
  · exact rectangleFlux_one_side hc hd (Or.inl ⟨hu,hv⟩)
  · exact hsplit (mem_uIcc_of_ge hv hu) (Or.inl ⟨hu,le_rfl⟩) (Or.inr ⟨le_rfl,hv⟩)

lemma differentiableOn_of_continuousOn_off_real {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hc : ContinuousOn f U)
    (hd : ∀z∈U,z.im≠0 → DifferentiableAt ℂ f z) : DifferentiableOn ℂ f U := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_,hc⟩
  intro z w hrect
  rw [←add_eq_zero_iff_eq_neg,Complex.wedgeIntegral_add_wedgeIntegral_eq]
  exact rectangleFlux_off_real (hc.mono hrect) (fun p hp => hd p (hrect hp))

end CircleDomainRigidity

end

end OAI
