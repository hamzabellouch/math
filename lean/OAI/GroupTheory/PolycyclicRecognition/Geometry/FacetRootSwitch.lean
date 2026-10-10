import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceRootSwitch
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequenceVanishingRate

namespace OAI

/-! # Co-location of neighboring sheets at a contact facet -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Vanishing enlargement of the allowed generator amplitude is absorbed
at the exact facet height. The estimate is uniform in every initial sheet. -/
theorem facet_root_switch_sublinear
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) (scale RH R η : ℕ → ℝ) (q : ℝ)
    (hs : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 ≤ scale n)
    (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ (x : G) (h : H) (t : ℝ),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n → χ h = q * scale n →
        |t| ≤ R n * Real.exp ((q + η n) * scale n) →
        dist (x * Exp h)
          (x * Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h) ≤ ε * scale n := by
  let Rc := fun n => R n * Real.exp (η n * scale n)
  have hRc0 : ∀ n, 0 ≤ Rc n := fun n => mul_nonneg (hR0 n) (Real.exp_pos _).le
  have hRc : HasSubexponentialUpperBoundSeq scale Rc :=
    hR.mul (sequence_subexponential_exp_of_vanishing_rate hscale0 hη)
      (Eventually.of_forall hR0)
  intro ε hε
  filter_upwards [sublinear_root_switch_sequence T H χ hχ Exp hExp realize v
    scale RH Rc hs hRH0 hRc0 hRH hRc ε hε] with n hn
  intro x h t hh hfacet ht
  apply hn x h t hh
  calc
    |t| * Real.exp (-χ h) ≤
        (R n * Real.exp ((q + η n) * scale n)) * Real.exp (-χ h) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = Rc n := by
      rw [mul_assoc, ← Real.exp_add, hfacet]
      congr 2
      ring

end PolycyclicRecognition

end

end OAI
