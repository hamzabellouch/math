import Mathlib
import OAI.Probability.SKSupport.Foundations.Equation

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat

def SpatialRightContinuous (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ t x, ContinuousWithinAt (fun s => iteratedDeriv n (F s) x) (Ici t) t

lemma SpatialRightContinuous.deriv {F : ℝ → ℝ → ℝ} (hF : SpatialRightContinuous F) :
    SpatialRightContinuous (fun t => deriv (F t)) := by
  intro n t x
  simpa only [iteratedDeriv_succ'] using hF (n+1) t x

lemma SpatialRightContinuous.add {F G : ℝ → ℝ → ℝ}
    (hf : BoundedSmoothFamily F) (hg : BoundedSmoothFamily G)
    (hF : SpatialRightContinuous F) (hG : SpatialRightContinuous G) :
    SpatialRightContinuous (fun t x => F t x+G t x) := by
  intro n t x
  have he (s : ℝ) : iteratedDeriv n (fun x => F s x+G s x) x =
      iteratedDeriv n (F s) x+iteratedDeriv n (G s) x :=
    iteratedDeriv_fun_add ((hf.regular s).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      ((hg.regular s).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
  simp_rw [he]
  exact (hF n t x).add (hG n t x)

lemma SpatialRightContinuous.const_mul {F : ℝ → ℝ → ℝ}
    (hf : BoundedSmoothFamily F) (hF : SpatialRightContinuous F) (c : ℝ) :
    SpatialRightContinuous (fun t x => c*F t x) := by
  intro n t x
  simp_rw [iteratedDeriv_const_mul c ((hf.regular _).smooth.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
  exact continuousWithinAt_const.mul (hF n t x)

lemma SpatialRightContinuous.mul {F G : ℝ → ℝ → ℝ}
    (hf : BoundedSmoothFamily F) (hg : BoundedSmoothFamily G)
    (hF : SpatialRightContinuous F) (hG : SpatialRightContinuous G) :
    SpatialRightContinuous (fun t x => F t x*G t x) := by
  intro n t x
  have he (s : ℝ) : iteratedDeriv n (fun x => F s x*G s x) x =
      ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*iteratedDeriv j (F s) x*iteratedDeriv (n-j) (G s) x :=
    iteratedDeriv_fun_mul ((hf.regular s).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      ((hg.regular s).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
  simp_rw [he]
  exact tendsto_finsetSum _ (fun j _ =>
    (continuousWithinAt_const.mul (hF j t x)).mul (hG (n-j) t x))

lemma SpatialRightContinuous.timeConst {c : ℝ → ℝ}
    (hc : ∀ t, ContinuousWithinAt c (Ici t) t) :
    SpatialRightContinuous (fun t (_x : ℝ) => c t) := by
  intro n t x
  cases n with
  | zero => exact hc t
  | succ n => simpa only [iteratedDeriv_const,Nat.succ_ne_zero,ite_false] using
      (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (0:ℝ)) (Ici t) t)

lemma compactCoeff_rightContinuous (γ : OrderParameter) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℝ) : ContinuousWithinAt (compactCoeff γ T) (Ici t) t := by
  let g : ℝ → Time := fun s => ⟨stripClamp T s,⟨(stripClamp_mem hT0 s).1,
    (stripClamp_mem hT0 s).2.trans_lt hT1⟩⟩
  have hg : Continuous g := (continuous_stripClamp T).subtype_mk _
  have hm : MapsTo g (Ici t) (Ici (g t)) := by
    intro s hs
    change stripClamp T t ≤ stripClamp T s
    exact max_le_max_left _ (min_le_min_left _ hs)
  have hh := (γ.right_continuous (g t)).comp hg.continuousAt.continuousWithinAt hm
  have he : compactCoeff γ T = fun s => γ.val (g s) := by
    funext s
    exact extend_coe γ.val (g s)
  rw [he]
  exact hh

variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactGradient_rightSmooth (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : SpatialRightContinuous (compactGradient W γ T) := by
  intro n t x
  have hc := value_derivative_continuousOn W γ hT0 hT1 (n+1)
  have hh : Continuous (fun s => iteratedDeriv (n+1) (value W γ (stripClamp T s)) x) := by
    have hg : ContinuousOn (fun s : ℝ => (stripClamp T s,x)) univ :=
      ((continuous_stripClamp T).prodMk continuous_const).continuousOn
    have hm : MapsTo (fun s : ℝ => (stripClamp T s,x)) univ (Icc (0:ℝ) T ×ˢ (univ : Set ℝ)) :=
      fun s _ => ⟨stripClamp_mem hT0 s,mem_univ _⟩
    have he : ContinuousOn
        ((fun p : ℝ × ℝ => iteratedDeriv (n+1) (value W γ p.1) p.2) ∘
          (fun s : ℝ => (stripClamp T s,x))) univ :=
      ContinuousOn.comp (f := fun s : ℝ => (stripClamp T s,x))
        (g := fun p : ℝ × ℝ => iteratedDeriv (n+1) (value W γ p.1) p.2) hc hg hm
    exact continuousOn_univ.mp he
  change ContinuousWithinAt (fun s => iteratedDeriv n (deriv (value W γ (stripClamp T s))) x) (Ici t) t
  simpa only [iteratedDeriv_succ'] using hh.continuousAt.continuousWithinAt

lemma compactValueRate_rightSmooth (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : SpatialRightContinuous (compactValueRate W γ T) := by
  have hu := compactGradient_family W γ hT0 hT1
  have hur := compactGradient_rightSmooth W γ hT0 hT1
  have hc : BoundedSmoothFamily (fun t (_x : ℝ) => compactCoeff γ T t) := by
    apply BoundedSmoothFamily.timeConst (C := ⟨γ.val ⟨T,⟨hT0,hT1⟩⟩,γ.nonneg _⟩) (compactCoeff_measurable γ T)
    intro t
    rw [abs_of_nonneg (compactCoeff_bounds γ hT0 hT1 t).1]
    exact (compactCoeff_bounds γ hT0 hT1 t).2
  have hcr := SpatialRightContinuous.timeConst (compactCoeff_rightContinuous γ hT0 hT1)
  have hh := SpatialRightContinuous.add (hu.deriv.const_mul (-(1/2:ℝ)))
    ((hc.mul (hu.mul hu)).const_mul (-(1/2:ℝ)))
    (SpatialRightContinuous.const_mul hu.deriv hur.deriv (-(1/2:ℝ)))
    (SpatialRightContinuous.const_mul (hc.mul (hu.mul hu))
      (SpatialRightContinuous.mul hc (hu.mul hu) hcr (SpatialRightContinuous.mul hu hu hur hur)) (-(1/2:ℝ)))
  convert hh using 1
  funext t x
  unfold compactValueRate valueRate compactGradient curvature gradient compactCoeff
  ring

theorem value_derivative_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    {T t : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ht0 : 0 ≤ t) (htT : t < T)
    (m : ℕ) (x : ℝ) :
    HasDerivWithinAt (fun s => iteratedDeriv m (value W γ s) x)
      (iteratedDeriv m (compactValueRate W γ T t) x) (Ioi t) t := by
  have hD := (compactValueRate_family W γ hT0 hT1).iteratedDeriv m
  have hi := intervalIntegral.integral_hasDerivWithinAt_right
    (a := t) (b := t) (s := Ici t) (t := Ioi t)
    (hD.intervalIntegrable x t t)
    ((hD.measurable.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.stronglyMeasurableAtFilter)
    ((compactValueRate_rightSmooth W γ hT0 hT1 m t x).mono Ioi_subset_Ici_self)
  have hh := (hi.mono Ioi_subset_Ici_self).const_add (iteratedDeriv m (value W γ t) x)
  apply hh.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
    rw [compactRate_integral_derivative W γ hT0 hT1 ht0 hs.le hsT.le m x]
    ring
  · simp

end ZeroTemperatureSK

end
end

end OAI
