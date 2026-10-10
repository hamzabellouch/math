import OAI.Analysis.CircleDomains.Modulus.RayIndexOscillation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! The local oscillation of the averaged index is bounded by the
probability that the sampled arc hits the projected point. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem meanGeometricIndex_oscillation_le_hit
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      |meanGeometricIndex hsch K hKS η p.1 - meanGeometricIndex hsch K hKS η p.2| <
        (η : Measure K).real {γ | diskRayProjection z.val ∈ range γ.val} + ε := by
  classical
  let H : Set K := {γ | diskRayProjection z.val ∈ range γ.val}
  have hH : MeasurableSet H := (isClosed_paths_hitting (diskRayProjection z.val)).measurableSet.preimage
    measurable_subtype_coe
  let I : K → ℝ := H.indicator 1
  let n : ClosedUpperHalfPlane → K → ℝ := fun w γ =>
    geometricRayIndex hsch γ.val (hKS γ.property) w.val
  let E : ClosedUpperHalfPlane × ClosedUpperHalfPlane → K → ℝ := fun p γ =>
    max (|n p.1 γ - n p.2 γ| - I γ) 0
  have hI : Integrable I (η : Measure K) := (integrable_const 1).indicator hH
  have hInon (γ : K) : 0 ≤ I γ := by by_cases h : γ ∈ H <;> simp [I, h]
  have hn (w : ClosedUpperHalfPlane) : Integrable (n w) (η : Measure K) :=
    integrable_geometricRayIndex hsch hsep K hK hKS η w
  have hE (p : ClosedUpperHalfPlane × ClosedUpperHalfPlane) : Integrable (E p) (η : Measure K) :=
    (((hn p.1).sub (hn p.2)).abs.sub hI).sup (integrable_const 0)
  have hlim : ∀ᵐ γ : K ∂(η : Measure K),
      Tendsto (fun p => E p γ) (𝓝 (z, z)) (𝓝 0) := by
    apply Eventually.of_forall
    intro γ
    have hb := eventually_geometricRayIndex_pair_difference hsch hsep γ.val (hKS γ.property) z hz
    have he : ∀ᶠ p in 𝓝 (z, z), E p γ = 0 := by
      filter_upwards [hb] with p hp
      dsimp [E, n]
      apply max_eq_right
      have hi : I γ = if diskRayProjection z.val ∈ range γ.val then 1 else 0 := by
        rfl
      rw [hi]
      linarith
    exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; linarith
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS X Y hX hY
  have hnear : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z,
      |w.val.re| ≤ X ∧ w.val.im ≤ Y := by
    have h₁ := ((Complex.continuous_re.comp continuous_subtype_val).abs.continuousAt
      (x := z)).eventually (isOpen_Iio.mem_nhds (show |z.val.re| < X by dsimp [X]; linarith))
    have h₂ := (Complex.continuous_im.comp continuous_subtype_val).continuousAt
      (x := z) |>.eventually (isOpen_Iio.mem_nhds (show z.val.im < Y by dsimp [Y]; linarith))
    filter_upwards [h₁, h₂] with w hw₁ hw₂
    exact ⟨hw₁.le, hw₂.le⟩
  have hbound : ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      ∀ᵐ γ : K ∂(η : Measure K), ‖E p γ‖ ≤ 2 * |M| := by
    filter_upwards [(continuous_fst.tendsto (z, z)).eventually hnear,
      (continuous_snd.tendsto (z, z)).eventually hnear] with p hp hq
    apply Eventually.of_forall
    intro γ
    have h₁ : |n p.1 γ| ≤ M := by
      simpa only [n, Complex.re_add_im] using hM γ p.1.val.re p.1.val.im hp.1 p.1.property hp.2
    have h₂ : |n p.2 γ| ≤ M := by
      simpa only [n, Complex.re_add_im] using hM γ p.2.val.re p.2.val.im hq.1 p.2.property hq.2
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have ht := abs_sub (n p.1 γ) (n p.2 γ)
      linarith [hInon γ, le_abs_self M]
    · positivity
  have hconv := tendsto_integral_filter_of_dominated_convergence (fun _ : K => 2 * |M|)
    (Eventually.of_forall fun p => (hE p).aestronglyMeasurable) hbound
    (integrable_const _) hlim
  have hconv' : Tendsto (fun p => ∫ γ, E p γ ∂(η : Measure K)) (𝓝 (z, z)) (𝓝 0) := by
    simpa only [integral_zero] using hconv
  have hevent : ∀ᶠ p in 𝓝 (z, z), (∫ γ, E p γ ∂(η : Measure K)) < ε :=
    hconv'.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [hevent] with p hp
  have hcomp : |meanGeometricIndex hsch K hKS η p.1 - meanGeometricIndex hsch K hKS η p.2| ≤
      (∫ γ, I γ ∂(η : Measure K)) + ∫ γ, E p γ ∂(η : Measure K) := by
    change |(∫ γ, n p.1 γ ∂(η : Measure K)) - (∫ γ, n p.2 γ ∂(η : Measure K))| ≤ _
    rw [← integral_sub (hn p.1) (hn p.2), ← integral_add hI (hE p)]
    apply abs_integral_le_integral_abs.trans
    apply integral_mono ((hn p.1).sub (hn p.2)).abs (hI.add (hE p))
    intro γ
    dsimp [E]
    linarith [le_max_left (|n p.1 γ - n p.2 γ| - I γ) 0]
  have hmass : (∫ γ, I γ ∂(η : Measure K)) = (η : Measure K).real H :=
    integral_indicator_one hH
  rw [hmass] at hcomp
  change _ < (η : Measure K).real H + ε
  linarith

end CircleDomainRigidity

end

end OAI
