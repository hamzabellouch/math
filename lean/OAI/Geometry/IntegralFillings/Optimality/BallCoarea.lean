import Mathlib
import OAI.Geometry.IntegralFillings.Slicing.RectifiableCoarea
import OAI.Geometry.IntegralFillings.Slicing.ProfileIntegral
import OAI.Geometry.IntegralFillings.Currents.Negation
import OAI.Geometry.IntegralFillings.Slicing.BoundaryTests
import OAI.Geometry.IntegralFillings.Optimality.BallStokes

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open SmoothCutoff Slicing BorelCoefficients BorelRestriction MassMeasure

noncomputable def innerBallCurrent (d : ℕ) (t : ℝ) : Functional (UnitBall d) d :=
  restrictCurrent (ballChart d).action_isMetricCurrent {x | t < radiusFunction d x}

lemma innerBallCurrent_metric (d : ℕ) (t : ℝ) : IsMetricCurrent (innerBallCurrent d t) :=
  restrictCurrent_isMetricCurrent (ballChart d).action_isMetricCurrent
    (measurableSet_lt measurable_const (radiusFunction_lipschitz d).continuous.measurable)

lemma innerBallCurrent_rectifiable (d : ℕ) (t : ℝ) : IntegerRectifiable (innerBallCurrent d t) :=
  integerRectifiable_restrict (ballChart d).action_isMetricCurrent
    (chart_integerRectifiable _) (measurableSet_lt measurable_const
      (radiusFunction_lipschitz d).continuous.measurable)

lemma ball_boundary_profile_coarea {k : ℕ} {S : ℝ → Functional (UnitBall (k+1)) k}
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      (ballChart (k+1)).action b (Matrix.vecCons (radiusFunction (k+1)) π) =
        ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ,
      BoundedLip (φ ∘ radiusFunction (k+1)) →
      ∀ᵐ t : ℝ, S t (fun x => φ (radiusFunction (k+1) x)*b x) π = φ t * S t b π)
    {a : ℝ≥0} {t : ℝ} (ht : -1 < t) (ha : 1 < (a:ℝ)*(-t))
    {b : UnitBall (k+1) → ℝ} {π : Fin k → UnitBall (k+1) → ℝ} (hab : Admissible b π) :
    boundarySucc (weightedCurrent (currentMassMeasure (ballChart (k+1)).action_isMetricCurrent)
      (ballChart (k+1)).action_isMetricCurrent (profile a t ∘ radiusFunction (k+1))) b π =
      -(∫ s : ℝ, dprofile a t s * S s b π) := by
  let C := ballChart (k+1)
  have hT := C.action_isMetricCurrent
  have hI := chart_integerRectifiable C
  have hu := radiusFunction_boundedLip (k+1)
  have hprof := profile_comp_boundedLip hu a t
  have hcons := Foundations.admissible_vecCons (BoundedLip.const 1) hab.1.1 hab.2
  simp only [boundarySucc, ite_eq_left hab, weightedCurrent, ite_eq_left hcons, mul_one]
  rw [borelAction_eq _ hT (currentMassMeasure_controls hT)
    (Foundations.admissible_vecCons hprof hab.1.1 hab.2)]
  rw [ballChart_local_stokes ht ha hab]
  congr 1
  have hπ' := (Foundations.admissible_vecCons hab.1 hu.1 hab.2).2
  have hchain := Foundations.IntegerRectifiable.apply_update_comp hI hab.1 hu
    (profile_hasDerivAt a t) (profile_comp_boundedLip hu a t)
    (dprofile_comp_boundedLip hu a t) (Matrix.vecCons (radiusFunction (k+1)) π) hπ' 0
  simp only [vecCons_update_head] at hchain
  rw [hchain]
  have heq : (fun x => b x*dprofile a t (radiusFunction (k+1) x)) =
      (fun x => dprofile a t (radiusFunction (k+1) x)*b x) := by funext x; ring
  rw [heq]
  trans ∫ s : ℝ, S s (fun x => dprofile a t (radiusFunction (k+1) x)*b x) π
  · exact (hact _ π ⟨(dprofile_comp_boundedLip hu a t).mul hab.1, hab.2⟩).2
  exact integral_congr_ae (hweight b π hab (dprofile a t) (dprofile_comp_boundedLip hu a t))

lemma eventually_profile_smooth (t : ℝ) (ht : t < 0) :
    ∀ᶠ n : ℕ in atTop, 1 < ((n:ℝ)+1)*(-t) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/(-t))
  have ht' : 0 < -t := neg_pos.mpr ht
  have hN' := (div_lt_iff₀ ht').mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_le_mul_of_nonneg_right hn' ht'.le]

theorem innerBall_ae_integral (k : ℕ) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ omega (k+1) ∧
      ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0),
        IsIntegral (k+1) (innerBallCurrent (k+1) t) ∧
        mass (boundarySucc (innerBallCurrent (k+1) t)) ≤ G t := by
  let C := ballChart (k+1)
  have hT := C.action_isMetricCurrent
  have hI := chart_integerRectifiable C
  have hu := radiusFunction_boundedLip (k+1)
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea
    hT hI (unitBall_CAT0 (k+1)) (radiusFunction_lipschitz (k+1))
  have hs : ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0),
      IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t :=
    hS.filter_mono (ae_mono Measure.restrict_le_self)
  have htest (b : UnitBall (k+1) → ℝ) (π : Fin k → UnitBall (k+1) → ℝ)
      (hab : Admissible b π) :
      ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0),
        boundarySucc (innerBallCurrent (k+1) t) b π = (-S t) b π := by
    have hh := (ae_tendsto_dprofile_integral (hact b π hab).1).filter_mono
      (ae_mono (Measure.restrict_le_self (s := Ioo (-1:ℝ) 0)))
    filter_upwards [hh, ae_restrict_mem measurableSet_Ioo] with t ht hti
    have hl := profile_boundary_tendsto hT hu t b π hab
    have he : ∀ᶠ n : ℕ in atTop,
        boundarySucc (weightedCurrent (currentMassMeasure hT) hT
          (profile ((n:ℝ≥0)+1) t ∘ radiusFunction (k+1))) b π =
          -(∫ s : ℝ, dprofile ((n:ℝ≥0)+1) t s * S s b π) := by
      filter_upwards [eventually_profile_smooth t hti.2] with n hn
      apply ball_boundary_profile_coarea hact hweight hti.1 _ hab
      simpa only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using hn
    exact tendsto_nhds_unique (hl.congr' he) ht.neg
  have heq : ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0),
      boundarySucc (innerBallCurrent (k+1) t) = -S t :=
    Foundations.ae_boundary_eq_of_ae_test_eq _
      (Eventually.of_forall fun t => innerBallCurrent_metric _ t)
      (hs.mono fun t ht => ht.1.neg) htest
  refine ⟨G, hG, hG0, ?_, ?_⟩
  · have hg : (∫ t : ℝ, G t) ≤ mass C.action := by simpa using hGI
    exact hg.trans (ballChart_mass_le (k+1))
  · filter_upwards [hs,heq] with t ht he
    refine ⟨⟨innerBallCurrent_metric _ t, innerBallCurrent_rectifiable _ t,
      he.symm ▸ ht.1.neg, he.symm ▸ ht.2.1.neg⟩, ?_⟩
    rw [he, mass_neg]
    exact ht.2.2

end SharpIntegralFillings.Optimality

end

end OAI
