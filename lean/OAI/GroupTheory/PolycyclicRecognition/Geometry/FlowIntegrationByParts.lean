import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactFlowTest

namespace OAI

/-! # Haar invariance identifies the weak horizontal derivative -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped NNReal

theorem integral_flowDeriv_smul_eq
    {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (μ : Measure G) [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f : G → W) (hf : Continuous f) (Ω : Set G) (hΩ : IsOpen Ω)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω})
    (φ : G → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω)
    (dφ : ℝ → G → ℝ) (hdφ : Continuous dφ.uncurry)
    (hderiv : ∀ t g, HasDerivAt (fun s : ℝ => φ (g * Exp ((-s) • v))) (dφ t g) t) :
    (∫ g, φ g • flowDeriv f Exp v g ∂μ) = ∫ g, dφ 0 g • f g ∂μ := by
  have hleft := hasDerivAt_integral_right_flow μ Exp hExp hzero hadd v f hf Ω hΩ C hlip
    φ hφ hcφ hsφ
  have hright := hasDerivAt_integral_translated_test μ
    (fun t : ℝ => Exp ((-t) • v)) (by fun_prop) (by simpa using hzero)
    (fun s t => by simpa only [neg_add] using hadd v (-s) (-t))
    φ hφ hcφ dφ hdφ hderiv f hf
  apply hleft.unique
  convert hright using 1
  funext t
  rw [← integral_mul_right_eq_self (μ := μ)
    (fun g => φ g • f (g * Exp (t • v))) (Exp ((-t) • v))]
  apply integral_congr_ae
  filter_upwards with g
  simp only [mul_assoc, ← hadd, neg_add_cancel, zero_smul, hzero, mul_one]

end PolycyclicRecognition

end

end OAI
