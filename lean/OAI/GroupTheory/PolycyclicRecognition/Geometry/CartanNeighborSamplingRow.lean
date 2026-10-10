import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowChart

namespace OAI

/-! # Original neighboring samples before their affine limit is identified -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [Fintype I] [DecidableEq I]
  (π : G →* Multiplicative W)
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (β : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (c B δ : ℝ)
  (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
  {Λ : ℝ≥0}

/-- Actual samples, root step and weak law, with no affine-limit premise. -/
structure NeighborSamplingRow where
  scale : ℕ → ℝ
  grows : Tendsto scale atTop atTop
  strict_mono : StrictMono scale
  scale_ge_one : ∀ n, 1 ≤ scale n
  pair : ℕ → NormalizedPair G Λ
  center : ℕ → G
  radius : ℕ → ℝ
  radius_nonneg : ∀ n, 0 ≤ radius n
  radius_subexponential : HasSubexponentialUpperBoundSeq scale radius
  base : ℕ → F.N.carrier
  step : ℕ → F.N.carrier
  base_mem : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' cell) β (scale n) (radius n)
  step_mem : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' cell) β (scale n) (radius n)
  mode : Fin M.letterCount
  time : ℕ → ℝ
  time_bound : ∀ n, |time n| ≤ radius n * Real.exp
    ((M.weight mode (pivot mode) + δ * B) * scale n)
  root_step : ∀ n, F.inclusionN (step n) =
    Exp (time n • (M.letter mode : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  profile : ℕ → F.N.carrier → Profiles
  measurable_profile : ∀ n, Measurable (profile n)
  actual : ∀ n q, q ∈ (fun v => v * base n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell β (scale n) 1 ∪
    (fun v => v * base n * step n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell β (scale n) 1 → ∀ z,
    (profile n q).val z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
      (max (Real.log (scale n)) 0)
      (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0))) z
  law : ProbabilityMeasure (Profiles × Profiles)
  converges : Tendsto (fun n => ProbabilityMeasure.map
    (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
      cell β (scale n) (base n)) (fun q => (profile n q, profile n (q * step n))))
      atTop (𝓝 law)
  point : Profiles × Profiles
  supported : point ∈ (law : Measure (Profiles × Profiles)).support

variable (D : NeighborSamplingRow T M F hunimod eW π bN cell β X βD
  haarN chartN hchartN pivot B δ Profiles (Λ := Λ))

/-- Insert a proved common affine description into the exact original row.
This changes neither its weak law nor either sampled profile. -/
def NeighborSamplingRow.withAffinity
    (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W)
    (haffine : ∀ z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior cell →
      D.point.1.val z = A.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
      D.point.2.val z = A.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂) :
    AffineNeighborRow T M F hunimod eW π bN cell β X βD
      haarN chartN hchartN pivot c B δ Profiles (Λ := Λ) where
  scale := D.scale
  grows := D.grows
  pair := D.pair
  center := D.center
  radius := D.radius
  radius_nonneg := D.radius_nonneg
  radius_subexponential := D.radius_subexponential
  base := D.base
  step := D.step
  basis := fun _ => β
  base_mem := D.base_mem
  step_mem := D.step_mem
  mode := D.mode
  time := D.time
  time_bound := D.time_bound
  root_step := D.root_step
  profile := fun n q => (D.profile n q, D.profile n (q * D.step n))
  measurable_profile := fun n => (D.measurable_profile n).prodMk
    ((D.measurable_profile n).comp (measurable_id.mul_const _))
  actual := by
    intro n q hq z
    have hlog : max (Real.log (D.scale n)) 0 = Real.log (D.scale n) :=
      max_eq_left (Real.log_nonneg (D.scale_ge_one n))
    have hc (b : Basis (Fin (finrank ℝ H)) ℝ H) :
        F.profileChart b = fun z => Exp (b.equivFun.symm z) := by
      funext z
      exact F.compatibleD _
    constructor
    · simpa only [hlog, hc] using D.actual n q (Or.inl hq) z
    · have hqs : q * D.step n ∈ (fun v => v * D.base n * D.step n) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell β (D.scale n) 1 := by
        rcases hq with ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
      simpa only [hlog, hc] using D.actual n (q * D.step n) (Or.inr hqs) z
  law := D.law
  converges := D.converges
  point := D.point
  supported := D.supported
  label₁ := A
  label₂ := A
  offset₁ := b₁
  offset₂ := b₂
  affine₁ := fun z hz => (haffine z hz).1
  affine₂ := fun z hz => (haffine z hz).2

end PolycyclicRecognition.CartanWordModel

end

end OAI
