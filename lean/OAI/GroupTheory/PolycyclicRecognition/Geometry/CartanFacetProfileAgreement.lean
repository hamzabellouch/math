import OAI.GroupTheory.PolycyclicRecognition.Geometry.FacetRootSwitch
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SublinearSheetLimits

namespace OAI

/-! # Actual neighboring profiles agree on the contact facet

The source bridge is proved from the root distortion estimate, with the
original deterministic generator step. No equality of affine labels or
offsets is assumed here.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology NNReal

variable {EG G W Z : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem affine_profiles_agree_on_contact_facet
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) (scale RH R η : ℕ → ℝ) (s : ℝ)
    (hs : Tendsto scale atTop atTop) (hscale : ∀ n, 0 < scale n)
    (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n))
    (x k : ℕ → G) (t : ℕ → ℝ)
    (ht : ∀ n, |t n| ≤ R n * Real.exp ((s + η n) * scale n))
    (chart : ℕ → Z → G) (h : ℕ → Z → H) (F : Set Z)
    (hchart : ∀ n, ∀ z ∈ F, chart n z = Exp (h n z))
    (hh : ∀ n, ∀ z ∈ F, ‖(finBasis ℝ H).equivFun (h n z)‖ ≤ RH n)
    (hfacet : ∀ n, ∀ z ∈ F, χ (h n z) = s * scale n)
    (q : Z → W) (A C : W →ₗ[ℝ] W) (b₁ b₂ : W)
    (hf : ∀ z ∈ F, Tendsto (fun n => rescaledMapProfile (J n) (x n) (k n)
      (Real.log (scale n)) (chart n) z) atTop (𝓝 (A (q z) + b₁)))
    (hg : ∀ z ∈ F, Tendsto (fun n => rescaledMapProfile (J n) (x n)
      (k n * Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      (Real.log (scale n)) (chart n) z) atTop (𝓝 (C (q z) + b₂))) :
    ∀ z ∈ F, A (q z) + b₁ = C (q z) + b₂ := by
  intro z hz
  apply rescaled_profile_limits_eq_of_sublinear_sheet_distance J hJ scale hscale
    x k (fun n => k n * Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    chart (fun _ => z) _ _ (hf z hz) (hg z hz)
  intro ε hε
  filter_upwards [facet_root_switch_sublinear T H χ hχ Exp hExp realize v
    scale RH R η s hs (fun n => (hscale n).le) hRH0 hR0 hRH hR hη ε hε] with n hn
  rw [hchart n z hz]
  simpa only [mul_assoc] using hn (x n * k n) (h n z) (t n)
    (hh n z hz) (hfacet n z hz) (ht n)

end PolycyclicRecognition

end

end OAI
