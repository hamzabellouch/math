import OAI.GroupTheory.PolycyclicRecognition.Geometry.HorizontalFlowDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! # Differentiating compactly supported pairings along horizontal flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology NNReal

theorem eventually_compact_right_flow_mem
    {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K Ω : Set G} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {Exp : V → G} (hExp : Continuous Exp) (hzero : Exp 0 = 1) (v : V) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ g ∈ K, g * Exp (t • v) ∈ Ω := by
  apply hK.eventually_forall_of_forall_eventually
  intro g hg
  have hc : Continuous (fun z : ℝ × G => z.2 * Exp (z.1 • v)) := by fun_prop
  exact hc.continuousAt.eventually (hΩ.mem_nhds (by simpa [hzero] using hKΩ hg))

variable {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [T2Space G] in
theorem hasDerivAt_integral_right_flow
    (μ : Measure G) [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f : G → W) (hf : Continuous f) (Ω : Set G) (hΩ : IsOpen Ω)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω})
    (φ : G → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    HasDerivAt (fun t : ℝ => ∫ g, φ g • f (g * Exp (t • v)) ∂μ)
      (∫ g, φ g • flowDeriv f Exp v g ∂μ) 0 := by
  obtain ⟨s, hs, hstay⟩ := Filter.eventually_iff_exists_mem.mp
    (eventually_compact_right_flow_mem hcφ hΩ hsφ hExp hzero v)
  apply (hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun (t : ℝ) (g : G) => φ g • f (g * Exp (t • v)))
    (F' := fun g => φ g • flowDeriv f Exp v g)
    (bound := fun g => ‖φ g‖ * (C : ℝ)) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall (fun t => (hφ.smul (by fun_prop)).aestronglyMeasurable)
  · simp only [zero_smul, hzero, mul_one]
    have hc : Continuous (fun g : G => φ g • f g) := hφ.smul hf
    have hk : HasCompactSupport (fun g : G => φ g • f g) := hcφ.smul_right
    exact hc.integrable_of_hasCompactSupport hk
  · exact hφ.aestronglyMeasurable.smul
      (stronglyMeasurable_flowDeriv f hf Exp hExp v).aestronglyMeasurable
  · filter_upwards with g
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    by_cases hg : φ g = 0
    · simp [hg]
    · have hgK : g ∈ tsupport φ := subset_tsupport φ hg
      have hd := (hlip g).dist_le_mul t (hstay t ht g hgK) u (hstay u hu g hgK)
      rw [dist_eq_norm, ← smul_sub, norm_smul]
      simp only [Real.coe_nnabs, abs_mul, abs_norm, abs_of_nonneg C.coe_nonneg]
      calc
        ‖φ g‖ * ‖f (g * Exp (t • v)) - f (g * Exp (u • v))‖
          ≤ ‖φ g‖ * ((C : ℝ) * dist t u) := by
            gcongr
            simpa only [dist_eq_norm] using hd
        _ = ‖φ g‖ * (C : ℝ) * dist t u := (mul_assoc _ _ _).symm
  · exact (hφ.norm.integrable_of_hasCompactSupport hcφ.norm).mul_const C
  · filter_upwards [ae_hasDerivAt_flowDeriv μ Exp hExp hadd v f hf Ω hΩ C hlip]
      with g hg
    by_cases hz : φ g = 0
    · simpa [hz] using (hasDerivAt_const (0 : ℝ) (0 : W))
    · exact (hg (hsφ (subset_tsupport φ hz))).const_smul (φ g)

end PolycyclicRecognition

end

end OAI
