import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSheetAgreement
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction

namespace OAI

/-! # Interior sheet agreement needs the source identity only on sampled points -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set MeasureTheory
open scoped Manifold Topology NNReal

variable {EG G I W A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Fintype I] [DecidableEq I]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace A]

include T in
theorem supported_switch_profiles_agree_on
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) (words : Finset (FreeMagma I)) (β : WordBasisSelections X words)
    (z : Fin (finrank ℝ H) → ℝ) (i : Fin M.letterCount)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (t : ℕ → ℝ) {B s : ℝ} (hB : 0 ≤ B)
    (ht : ∀ᶠ n in atTop, |t n| ≤ B * Real.exp (scale n * (s + ε n)))
    (hslack : s < M.weight i ((WordBasisSelections.basis X words β).equivFun.symm z))
    {L : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith L (J n))
    (x : ℕ → G) (k : ℕ → A → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace (S × S)] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (samples : ℕ → ProbabilityMeasure A) (pair : ℕ → A → S × S)
    (hp : ∀ n, Measurable (pair n)) (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (pair n)) atTop (𝓝 ν))
    (C : Set A) (hC : MeasurableSet C)
    (hfull : ∀ n, ∀ᵐ a ∂(samples n : Measure A), a ∈ C)
    (hfirst : ∀ n a, a ∈ C → ∀ w, (pair n a).1.val w =
      rescaledMapProfile (J n) (x n) (k n a) (max (Real.log (scale n)) 0)
        (fun v => Exp (wordChartPivot X words β (scale n) v : H)) w)
    (hsecond : ∀ n a, a ∈ C → ∀ w, (pair n a).2.val w =
      rescaledMapProfile (J n) (x n)
        (k n a * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (max (Real.log (scale n)) 0)
        (fun v => Exp (wordChartPivot X words β (scale n) v : H)) w)
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    f.1.val z = f.2.val z := by
  let restricted := fun n => supportedProbabilityRestriction (samples n) C hC (hfull n)
  have hlim : Tendsto (fun n => ProbabilityMeasure.map (restricted n)
      (fun a : C => pair n a.val)) atTop (𝓝 ν) := by
    simpa only [restricted, map_supportedProbabilityRestriction _ _ _ _ _ (hp _)] using hν
  exact M.supported_switch_profiles_agree T Exp hExp realize X words β z i scale hscale
    ε hε t hB ht hslack J hJ x (fun n (a : C) => k n a.val) S restricted
    (fun n (a : C) => pair n a.val) (fun n => (hp n).comp measurable_subtype_coe)
    ν hlim (fun n a w => hfirst n a.val a.property w)
    (fun n a w => hsecond n a.val a.property w) hf

end PolycyclicRecognition.CartanWordModel

end

end OAI
