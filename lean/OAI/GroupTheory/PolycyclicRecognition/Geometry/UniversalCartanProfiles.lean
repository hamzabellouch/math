import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDependentProfileCompactness

namespace OAI

/-! # A compact profile family uniform in maps, centers, and bounded suffixes -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology NNReal

variable {EG G I W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [Fintype I] [DecidableEq I]

include T in
/-- This compact set is chosen before any map, basepoint, suffix radius,
or smaller box enlargement. Only the normalized metric bound is fixed. -/
theorem exists_universal_compact_cartan_profiles
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hs0 : ∀ n, 0 ≤ scale n) (K : ℝ≥0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ S : Set C((Fin (finrank ℝ H) → ℝ), W), IsCompact S ∧
      ∀ n (J : G → W), LipschitzWith K J → ∀ x k : G,
      dist 1 k / Real.exp (scale n) ≤ B → ∃ f ∈ S, ∀ z,
        f z = rescaledMapProfile J x k (scale n)
          (fun z => F.inclusionD (F.ExpD (F.D.equiv
            ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
              (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
              (scale n)).equivFun.symm z)))) z := by
  let A := fun n => {p : (G → W) × G × G |
    LipschitzWith K p.1 ∧ dist 1 p.2.2 / Real.exp (scale n) ≤ B}
  have hzero : LipschitzWith K (fun _ : G => (0 : W)) :=
    LipschitzWith.of_dist_le_mul (fun _ _ => by
      simp only [dist_self]
      exact mul_nonneg K.coe_nonneg dist_nonneg)
  let : ∀ n, Nonempty (A n) := fun n => ⟨⟨(fun _ => 0, 1, 1),
    hzero, by simpa only [dist_self, zero_div] using hB⟩⟩
  obtain ⟨S, hS, hm⟩ := exists_compact_dependent_cartan_profiles T F hExp realize
    haarD dynkinD X hDnil hletters bD₀ βD hβD scale hscale hs0
    (fun n (p : A n) => p.val.1) (fun n (p : A n) => p.property.1)
    (fun n (p : A n) => p.val.2.1) (fun n (p : A n) => p.val.2.2) B
    (fun n (p : A n) => p.property.2)
  refine ⟨S, hS, ?_⟩
  intro n J hJ x k hk
  exact hm n ⟨(J, x, k), hJ, hk⟩

end PolycyclicRecognition

end

end OAI
