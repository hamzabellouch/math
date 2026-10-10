import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingNumericalBudget
import OAI.Analysis.IrrationalRotation.Analysis.TestedKernelUnifiedMoments
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingTestVariation
import OAI.Analysis.IrrationalRotation.Analysis.TestedTriangularVariation

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductSamplingPhaseMoments
open Invariant233.ScalarSampling

def testedKernel (m : ℕ) (selected endpoint : Bool) (a b c d : ℝ) : ℝ → ℝ → ℝ :=
  if endpoint then
    if selected then TestedTriangular.secondKernel (Ico a b) (Ico c d)
    else TestedSampling.secondKernel m (Ico a b) (Ico c d)
  else
    if selected then TestedTriangular.firstKernel (Ico a b) (Ico c d)
    else TestedSampling.firstKernel m (Ico a b) (Ico c d)

@[fun_prop] theorem testedKernel_measurable (m : ℕ) (selected endpoint : Bool)
    (a b c d : ℝ) : Measurable (Function.uncurry (testedKernel m selected endpoint a b c d)) := by
  have hfirst : Measurable (Function.uncurry (TestedSampling.firstKernel m (Ico a b) (Ico c d))) :=
    ((measurable_circleKernel _ _).mul
      ((measurable_const.indicator measurableSet_Ico).comp measurable_fst)).mul
      ((measurable_const.indicator measurableSet_Ico).comp
        (measurable_fract.comp (measurable_fst.add measurable_snd)))
  have hsecond : Measurable (Function.uncurry (TestedSampling.secondKernel m (Ico a b) (Ico c d))) :=
    ((measurable_circleEndpoint_pair _ _).mul
      ((measurable_const.indicator measurableSet_Ico).comp
        (measurable_fract.comp (measurable_fst.sub measurable_snd)))).mul
      ((measurable_const.indicator measurableSet_Ico).comp measurable_fst)
  cases selected <;> cases endpoint <;> simp only [testedKernel, Bool.false_eq_true, ite_false, ite_true]
  · exact hfirst
  · exact hsecond
  · exact TestedTriangular.firstKernel_measurable measurableSet_Ico measurableSet_Ico
  · exact TestedTriangular.secondKernel_measurable measurableSet_Ico measurableSet_Ico

theorem testedKernel_bounds {m : ℕ} (hm : 200 ≤ m) (selected endpoint : Bool)
    (a b c d s t : ℝ) :
    0 ≤ testedKernel m selected endpoint a b c d s t ∧
      |testedKernel m selected endpoint a b c d s t| ≤ (m : ℝ)^(13 / 5 : ℝ) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hheight : 1 ≤ (m : ℝ)^(13 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have hb (s t : ℝ) : 0 ≤ manuscriptKernel m s t ∧
      manuscriptKernel m s t ≤ (m : ℝ)^(13 / 5 : ℝ) := by
    simpa only [manuscript_reciprocal_height hm, manuscriptKernel, circleKernel] using
      (rawKernel_height hh hα : 0 ≤ manuscriptKernel m s t ∧
        manuscriptKernel m s t ≤ ((m : ℝ)^(-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹)
  cases selected <;> cases endpoint <;> simp only [testedKernel, Bool.false_eq_true, ite_false, ite_true]
  · by_cases hs : s ∈ Ico a b <;> by_cases ht : Int.fract (s+t) ∈ Ico c d <;>
      simp [TestedSampling.firstKernel, hs, ht, (hb s t).1, abs_of_nonneg (hb s t).1,
        (hb s t).2, hheight.trans' zero_le_one]
  · by_cases hs : Int.fract (s-t) ∈ Ico a b <;> by_cases ht : s ∈ Ico c d <;>
      simp [TestedSampling.secondKernel, manuscriptEndpointKernel, hs, ht, (hb (s-t) t).1,
        abs_of_nonneg (hb (s-t) t).1, (hb (s-t) t).2, hheight.trans' zero_le_one]
  · have h := TestedTriangular.firstKernel_bounds (Ico a b) (Ico c d) s t
    exact ⟨h.1, by rw [abs_of_nonneg h.1]; exact h.2.trans ((TestedTriangular.triangularKernel_bounds s t).2.trans hheight)⟩
  · have h := TestedTriangular.secondKernel_bounds (Ico a b) (Ico c d) s t
    exact ⟨h.1, by rw [abs_of_nonneg h.1]; exact h.2.trans ((TestedTriangular.triangularKernel_bounds (Int.fract (s-t)) t).2.trans hheight)⟩

theorem realBVSize_le_of_global {f : ℝ → ℝ} {C V : ℝ}
    (hf : ∀ t, |f t| ≤ C)
    (hsize : sSup (Set.range (fun t => |f t|)) +
      (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤ V) : realBVSize f ≤ V := by
  have hsup : sSup ((fun t => |f t|) '' Icc (0 : ℝ) 1) ≤
      sSup (Set.range (fun t => |f t|)) := by
    apply csSup_le ((nonempty_Icc.mpr zero_le_one).image _)
    rintro _ ⟨t, _, rfl⟩
    exact le_csSup ⟨C, by rintro _ ⟨t, rfl⟩; exact hf t⟩ ⟨t, rfl⟩
  dsimp only [realBVSize]
  linarith

theorem testedKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) (selected endpoint : Bool)
    (a b c d : ℝ) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    BoundedVariationOn (testedKernel m selected endpoint a b c d s) (Icc (0 : ℝ) 1) ∧
      realBVSize (testedKernel m selected endpoint a b c d s) ≤ 16 * (m : ℝ)^10 := by
  have hbound := fun t => (testedKernel_bounds hm selected endpoint a b c d s t).2
  have hheight : 1 ≤ (m : ℝ)^10 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ m by omega))
  cases selected
  · have h := tested_manuscript_oriented_BV_bound_ten hm hs endpoint a b c d
    have heq : testedKernel m false endpoint a b c d s =
        fun t => if endpoint then manuscriptEndpointKernel m s t *
          (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) *
          (Ico c d).indicator (fun _ => 1) s
        else manuscriptKernel m s t * (Ico a b).indicator (fun _ => 1) s *
          (Ico c d).indicator (fun _ => 1) (Int.fract (s+t)) := by
      cases endpoint <;> rfl
    rw [heq]
    refine ⟨h.1, ?_⟩
    apply (realBVSize_le_of_global (by simpa only [heq] using hbound) h.2).trans
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 10]
  · cases endpoint
    · have h := TestedTriangular.firstKernel_interval_BV_bound (Ico a b) c d hs
      refine ⟨h.1, ?_⟩
      exact (realBVSize_le_of_global hbound h.2).trans (by nlinarith)
    · have h := TestedTriangular.secondKernel_interval_BV_bound (Ico c d) a b hs
      refine ⟨h.1, ?_⟩
      exact (realBVSize_le_of_global hbound h.2).trans (by nlinarith)

theorem testedKernel_momentBounds {m : ℕ} (hm : 200 ≤ m) (selected endpoint : Bool)
    (a b c d : ℝ) : TestedSampling.MomentBounds m (testedKernel m selected endpoint a b c d) := by
  cases selected <;> cases endpoint <;> simp only [testedKernel, Bool.false_eq_true, ite_false, ite_true]
  · exact TestedSampling.firstKernel_moment_bounds hm measurableSet_Ico measurableSet_Ico
  · exact TestedSampling.secondKernel_moment_bounds hm measurableSet_Ico measurableSet_Ico
  · exact TestedSampling.firstTriangular_moment_bounds hm measurableSet_Ico measurableSet_Ico
  · exact TestedSampling.secondTriangular_moment_bounds hm measurableSet_Ico measurableSet_Ico

theorem testedKernel_square_moment_bound {m : ℕ} (hm : 200 ≤ m)
    (selected endpoint : Bool) (a b c d : ℝ) :
    (∫ s, ∫ t, (testedKernel m selected endpoint a b c d s t)^2
        ∂unitInterval ∂unitInterval) ≤
      (2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) := by
  have hi : IntegrableOn (fun p : ℝ × ℝ =>
      (testedKernel m selected endpoint a b c d p.1 p.2)^2)
      (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
    apply integrableOn_unitSquare_of_bound
      (F := fun s t => (testedKernel m selected endpoint a b c d s t)^2)
      (C := ((m : ℝ)^(13 / 5 : ℝ))^2)
      ((testedKernel_measurable m selected endpoint a b c d).pow_const 2)
    intro s t
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (testedKernel_bounds hm selected endpoint a b c d s t).2 2
  simp_rw [integral_unitInterval]
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun s t => (testedKernel m selected endpoint a b c d s t)^2) hi]
  exact (testedKernel_momentBounds hm selected endpoint a b c d).2.2.2.2.2

theorem tested_expected_average_error_le {κ : Type*} [Fintype κ]
    {p : ProductScaleData} (hp : ProductScaleLaws p) {j : ℕ} (hm : 200 ≤ p.m j)
    (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i) (hNle : ∀ i, N₀ i ≤ p.N j)
    (powers : Finset ℕ) (hs : ProductSamplingPowersAt p j powers)
    (selected : κ → Bool) (endpoint : Bool) (a b c d : κ → ℝ) :
    let u := fun i => testedKernel (p.m j) (selected i) endpoint (a i) (b i) (c i) (d i)
    (∫ θ, ∫ x, ((powers.card : ℝ)⁻¹ *
        (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * θ i))) -
        ∏ i, mean (u i) (x i))^2
      ∂Measure.pi (fun _ : κ => unitInterval)
      ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))) ≤
      (8 * (p.m j : ℝ)^(3 / 5 : ℝ) * Real.log (p.m j))^Fintype.card κ /
          (powers.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * (p.m j : ℝ)^(-50 : ℝ) *
          (1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
            (p.m j : ℝ)^(-50 : ℝ))^(Fintype.card κ - 1)) := by
  dsimp only
  let u := fun i => testedKernel (p.m j) (selected i) endpoint (a i) (b i) (c i) (d i)
  have h := expected_average_error_le_source_scale hp hm N₀ hN hNle powers hs u
    (fun _ => (p.m j : ℝ)^(13 / 5 : ℝ))
    (fun i => testedKernel_measurable _ _ _ _ _ _ _)
    (fun i s t => (testedKernel_bounds hm _ _ _ _ _ _ s t).2)
    (fun i s t => (testedKernel_bounds hm _ _ _ _ _ _ s t).1)
    (fun i s => by
      simpa only [mean, integral_unitInterval] using
        ((testedKernel_momentBounds hm (selected i) endpoint (a i) (b i) (c i) (d i)).2.2.1 s).2)
    (fun i s hs => (testedKernel_BV_bound hm _ _ _ _ _ _ hs).1)
    (fun i s hs => (testedKernel_BV_bound hm _ _ _ _ _ _ hs).2)
    (fun i => by
      simpa only [mean, integral_unitInterval] using
        (testedKernel_momentBounds hm (selected i) endpoint (a i) (b i) (c i) (d i)).2.2.2.1.2)
    (fun i => testedKernel_square_moment_bound hm (selected i) endpoint (a i) (b i) (c i) (d i))
  apply h.trans
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg powers.card)
  apply pow_le_pow_left₀ _ (ScalarSampling.twice_kernel_square_mass_le hm)
  have hraw := TestedSampling.half_le_common_square_bound hm
  linarith

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
