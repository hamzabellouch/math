import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NeighborProfileGluing

namespace OAI

/-! # One actual profile map for both cells of an affine neighboring row -/

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

/-- Restricting to a cofinal subsequence keeps the original neighboring
law, affine profiles and offsets. -/
def AffineNeighborRow.reindex (u : ℕ → ℕ) (hu : StrictMono u) :
    AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S (Λ := Λ) where
  scale := D.scale ∘ u
  grows := D.grows.comp hu.tendsto_atTop
  pair := D.pair ∘ u
  center := D.center ∘ u
  radius := D.radius ∘ u
  radius_nonneg := fun n => D.radius_nonneg (u n)
  radius_subexponential := fun ε hε => hu.tendsto_atTop.eventually (D.radius_subexponential ε hε)
  base := D.base ∘ u
  step := D.step ∘ u
  basis := D.basis ∘ u
  base_mem := fun n => D.base_mem (u n)
  step_mem := fun n => D.step_mem (u n)
  mode := D.mode
  time := D.time ∘ u
  time_bound := fun n => D.time_bound (u n)
  root_step := fun n => D.root_step (u n)
  profile := D.profile ∘ u
  measurable_profile := fun n => D.measurable_profile (u n)
  actual := fun n => D.actual (u n)
  law := D.law
  converges := D.converges.comp hu.tendsto_atTop
  point := D.point
  supported := D.supported
  label₁ := D.label₁
  label₂ := D.label₂
  offset₁ := D.offset₁
  offset₂ := D.offset₂
  affine₁ := D.affine₁
  affine₂ := D.affine₂

local notation "Q" => fun n => (fun y => y * D.base n) ''
  M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1

/-- Glue the row's two actual profiles using their agreement on overlap. -/
def AffineNeighborRow.gluedProfile (n : ℕ) : F.N.carrier → S :=
  glueNeighborProfile (Q n) (D.step n) (D.profile n)

/-- Gluing preserves the joint law and the actual rescaled formula on both
translated cells. In particular it introduces no new profile hypothesis. -/
theorem AffineNeighborRow.gluedProfile_properties :
    (∀ n, Measurable (D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S n)) ∧
    (∀ n q, q ∈ Q n ∪ (fun y => y * D.step n) '' Q n → ∀ z,
      (D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S n q).val z =
      rescaledMapProfile (fun g => (π ((D.pair n).val.1 g)).toAdd)
        (D.center n) (F.inclusionN q) (Real.log (D.scale n))
        (fun z => ExpG ((exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (Real.log (D.scale n))).equivFun.symm z)) z) ∧
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (D.scale n) (D.base n))
      (fun q => (D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S n q,
        D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
          haarN chartN hchartN pivot shrink B δ S n (q * D.step n))))
      atTop (𝓝 D.law) := by
  let value : S → ((Fin (finrank ℝ H) → ℝ) → W) := fun f => f.val
  have hv : Function.Injective value := by
    intro f g h
    apply Subtype.ext
    exact ContinuousMap.ext (congrFun h)
  let actual := fun n q z => rescaledMapProfile
    (fun g => (π ((D.pair n).val.1 g)).toAdd) (D.center n) (F.inclusionN q)
    (Real.log (D.scale n)) (fun z => ExpG ((exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
      (Real.log (D.scale n))).equivFun.symm z)) z
  have hg (n) := glueNeighborProfile_actual (D.step n) (D.profile n) value hv (actual n)
    (fun q hq => funext fun z => (D.actual n q hq z).1)
    (fun q hq => funext fun z => (D.actual n q hq z).2)
  have hmeas (n) := (M.translated_groupBox_cell_properties T F hunimod eW
    haarN chartN hchartN b₀ cell βcell (D.scale n) (D.base n)).1
  refine ⟨fun n => measurable_glueNeighborProfile (hmeas n) (D.step n)
    (D.measurable_profile n), ?_, ?_⟩
  · intro n q hq z
    exact congrFun ((hg n).2 q hq) z
  · apply D.converges.congr'
    filter_upwards [] with n
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.map_congr
    have hprops := M.translated_groupBox_cell_properties T F hunimod eW
      haarN chartN hchartN b₀ cell βcell (D.scale n) (D.base n)
    filter_upwards [ae_mem_cellProbabilityMeasure
      (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
      (Q n) hprops.1 hprops.2.1 hprops.2.2] with q hq
    exact ((hg n).1 q hq).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
