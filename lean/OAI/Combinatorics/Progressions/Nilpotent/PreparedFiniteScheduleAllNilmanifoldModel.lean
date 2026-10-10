import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteScheduleUniversalDegreeModel

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable (N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
variable {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hbox : (integerBox N).Nonempty)
variable (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U → FiniteProbabilityWeights Path)
variable (hweight : ∀ z, Measurable (fun center => (law center).weight z))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "Sites" => integerBox sides

theorem preparedFiniteScheduleDegreeModelsAtLaw_allNilmanifold_actualData
    (physical : Path → integerBox (Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S)) → integerBox N)
    (degree : ℕ) (u p cap sliceLog testLog budget E : ℝ)
    (hModel : PreparedFiniteScheduleDegreeModelsAtLaw B U b S N Pdetect μ poly hbox law hweight
      physical degree u p cap sliceLog testLog budget E)
    (hSliceLog : 0 ≤ sliceLog)
    (hDetectorBudget : 2 ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)
    (hnum : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)
    {Forecast : Type} [Nonempty Forecast] {Pnative massLog capLog Edata : ℝ}
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (hNative : 0 ≤ Pnative)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hCap : Real.exp capLog ≤ cap)
    (hPrecision : actualForecastDataModelRequired budget Pnative massLog u p ≤ E)
    {Branch : Type} [Fintype Branch]
    (input : Branch → integerBox N → ℂ)
    (hinput : ∀ branch v, ‖input branch v‖ ≤ Real.exp p) :
    let Packet := UniversalLocalMajorSliceTest sides degree sliceLog (Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)
    let commonBudget := max budget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : Fin nX → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : (integerBox N → ℂ) → ℝ :=
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical
        (fun _ (j : Packet) => j.slice.subtypeSites)
        (fun _ (j : Packet) t => j.weight t.val)
    let selectedLocal : (integerBox N → ℂ) →
      (CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) → Prop :=
      fun err errLocal => ∀ center z, ∃ j : Packet, errLocal (center, z) =
        𝔼 t ∈ j.slice.subtypeSites, err (physical z t) * j.weight t.val
    ∃ models : Branch → CenteredForecastModel (integerBox N),
      ∀ branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        native (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) (fun f => (data f).target)
        localSeminorm selectedLocal (input branch) (Real.exp (Qmodel + 2))
        (Real.exp (-u)) (Real.exp (2 * Qmodel + 2 * u + 4 * p + 34)) (models branch) := by
  classical
  intro Packet commonBudget Qmodel native localSeminorm selectedLocal
  have hSides (i : LayerSamplerVariables G I n B) : 0 < sides i := by
    cases i with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U b S j
  let : Nonempty Packet := UniversalLocalMajorSliceTest.nonempty sides hSides degree sliceLog
    (Pdetect.eval₂ (Nat.castRingHom ℝ) testLog) hSliceLog hDetectorBudget
  have hmodels := preparedFiniteScheduleDegreeModelsAtLaw_actualData
    (B := B) (U := U) (b := b) (S := S)
    N Pdetect μ poly hbox law hweight physical degree u p cap sliceLog testLog budget E hModel
    (Tests := fun _ => Packet) (Ldetect := fun _ j => j.nativeModel.L)
    (dims := fun _ j => j.nativeModel.dim)
    (fun _ j => j.nativeModel.model) (fun _ j => j.nativeModel.test) (fun _ j => j.slice.subtypeSites)
    (fun _ j i => (j.slice.start i : ℤ)) (fun _ j => j.stride) (fun _ j => j.slice.length)
    (fun _ j => j.stride_pos)
    (fun _ j => j.slice.subtypeSites_image_val.trans j.slice.integerPoints_eq_commonStrideBox)
    (fun _ j => j.slice.subtypeSites_dense j.dense) hnum
    (fun _ j => j.nativeModel.complexity) (fun _ j => by exact_mod_cast j.nativeModel.norm)
    data hNative hAccuracy hCap hPrecision input hinput
  simpa only [localSeminorm, selectedLocal, UniversalLocalMajorSliceTest.weight_eq_native_eval] using hmodels

end Erdos3.VectorPolynomial

end

end OAI
