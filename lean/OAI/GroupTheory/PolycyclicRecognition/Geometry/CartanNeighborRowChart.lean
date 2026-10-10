import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSampledProbeFrames
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowProfile

namespace OAI

/-! # The exact group chart for an original neighboring-row profile -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

local notation "profile" => D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
  haarN chartN hchartN pivot shrink B δ S

/-- At scales at least one, the glued original profile is precisely the
chart profile required by the polar source comparison. -/
theorem AffineNeighborRow.gluedProfile_chart
    (hs : ∀ n, 1 ≤ D.scale n) :
    (∀ n, Measurable (profile n)) ∧
    (∀ n q, q ∈ (fun v => v * D.base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 ∪
      (fun v => v * D.base n * D.step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((D.pair n).val.1 g)).toAdd) (D.center n) (F.inclusionN q)
        (max (Real.log (D.scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (D.scale n)) 0))) z) ∧
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (D.scale n) (D.base n))
      (fun q => (profile n q, profile n (q * D.step n)))) atTop (𝓝 D.law) := by
  obtain ⟨hmeas, hactual, hlaw⟩ := D.gluedProfile_properties T M F hunimod eW π b₀
    cell βcell X βD haarN chartN hchartN pivot shrink B δ S
  refine ⟨hmeas, ?_, hlaw⟩
  intro n q hq z
  have hq' : q ∈ (fun v => v * D.base n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 ∪
      (fun v => v * D.step n) '' ((fun v => v * D.base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1) := by
    rcases hq with hq | ⟨v, hv, rfl⟩
    · exact Or.inl hq
    · exact Or.inr ⟨v * D.base n, ⟨v, hv, rfl⟩, rfl⟩
  have hlog : max (Real.log (D.scale n)) 0 = Real.log (D.scale n) :=
    max_eq_left (Real.log_nonneg (hs n))
  have h := hactual n q hq' z
  have hc (b : Basis (Fin (finrank ℝ H)) ℝ H) :
      F.profileChart b = fun z => ExpG (b.equivFun.symm z) := by
    funext z
    exact F.compatibleD _
  rw [hlog, hc]
  exact h

omit [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier] in
/-- Restrict two identically labelled affine profiles to the common inner
height domain, retaining their respective original offsets. -/
theorem AffineNeighborRow.common_affine_on
    {V : Set W} (hV : V ⊆ (fun w => (1 - shrink * δ) • w) '' interior cell)
    (hlabels : D.label₂ = D.label₁) :
    ∀ (s : Bool) z,
      eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
      (if s then D.point.2 else D.point.1).val z = D.label₁.val
        (eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G))) + (if s then D.offset₂ else D.offset₁) := by
  intro s z hz
  cases s with
  | false => exact D.affine₁ z (hV hz)
  | true => simpa [hlabels] using D.affine₂ z (hV hz)

end PolycyclicRecognition.CartanWordModel

end

end OAI
