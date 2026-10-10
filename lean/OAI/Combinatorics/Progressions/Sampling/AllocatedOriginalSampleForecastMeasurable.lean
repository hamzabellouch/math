import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastAtom

namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

theorem canonicalZeroSpatialJointDensity_measurable
    {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z]
    (s : Empty ↪ Z) (root : Z → ℤ) (D : Matrix Empty Z ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) :
    Measurable (canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL) := by
  have hd : Measurable (canonicalSpatialKernelDensity s root D hp W L hW hL) := by
    apply pivotOutputDensity_measurable
    exact (smoothSplitProfile_contDiff _ _).continuous.measurable
  unfold canonicalZeroSpatialJointDensity sigmaAxisWeight tensorCutoffWeight
  simp_rw [canonicalSpatialSiteDensity_eq_kernel]
  apply Finset.measurable_prod
  intro x _
  apply hd.comp
  exact (measurable_pi_apply x).comp
    (sigmaAxisCoordinates (fun _ : X => Unit ⊕ Empty)).continuous.measurable

theorem binaryDensity_measurable_family
    {Ω Y V : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace V]
    (f : Y → ℝ) (g : Ω → V → ℝ) (hf : Measurable f)
    (hg : Measurable (fun p : Ω × V => g p.1 p.2)) :
    Measurable (fun p : Ω × (Y × V) => binaryDensity f (g p.1) p.2) := by
  exact (hf.comp (measurable_fst.comp measurable_snd)).mul
    (hg.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

namespace VectorPolynomial

section FixedPath

variable {m : ℕ} {G Ω : Type*} [Fintype G] [MeasurableSpace Ω]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P] (R σ : Fin m → ℝ)

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathPrincipal_measurable_family
    (g : Ω → ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ)
    (hg : Measurable g) (a : {a : LayerSamplerAxis I n // ¬P a}) (b : B a.val) :
    Measurable (fun p => allocatedFixedPathPrincipal B P R σ (g p) a b) := by
  have he (p : Ω) := allocatedAxisProfilePolynomial_principal_coeff B R σ a.val
    (fun e => g p ⟨a, e⟩) b
  simp only [allocatedFixedPathPrincipal, he]
  exact (measurable_const.add (measurable_const.mul
    ((measurable_pi_apply ⟨a, principalCoefficientSlot (layerSamplerDegree I n) a.val b⟩).comp hg))).div_const _

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathShift_measurable_family
    (g : Ω → ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ)
    (hg : Measurable g) (a : {a : LayerSamplerAxis I n // ¬P a}) :
    Measurable (fun p => allocatedFixedPathShift B P R σ (g p) a) := by
  have he (p : Ω) := allocatedAxisProfilePolynomial_constant_coeff B R σ a.val
    (fun e => g p ⟨a, e⟩)
  simp only [allocatedFixedPathShift, he]
  exact (measurable_const.mul
    ((measurable_pi_apply ⟨a, constantCoefficientSlot _ _⟩).comp hg)).div_const _

theorem allocatedFixedPathLiftDensity_measurable_family
    (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (g : Ω → ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ)
    (hg : Measurable g) :
    Measurable (fun p : Ω × ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ) =>
      allocatedFixedPathLiftDensity B P R σ hB lower width (g p.1) p.2) := by
  exact jointSlicedPrincipalDensity_measurable_family
    (D := {a : LayerSamplerAxis I n // ¬P a})
    (B := fun a => B a.val) (F := fun a => Fin (layerSamplerDegree I n a.val)) (P := Ω)
    hB (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (fun p => allocatedFixedPathPrincipal B P R σ (g p))
    (fun _ => lower) (fun _ => width) (fun p => allocatedFixedPathShift B P R σ (g p))
    (allocatedFixedPathPrincipal_measurable_family B P R σ g hg)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    (allocatedFixedPathShift_measurable_family B P R σ g hg)

theorem allocatedFixedPathForecastDensity_measurable_family
    {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (g : Ω → ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ)
    (hg : Measurable g) :
    Measurable (fun p : Ω × (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
        ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ)) =>
      allocatedFixedPathForecastDensity (X := X) B P R σ s root D hp hW hL
        hB lower width (g p.1) p.2) := by
  exact binaryDensity_measurable_family
    (canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL)
    (fun p => allocatedFixedPathLiftDensity B P R σ hB lower width (g p))
    (canonicalZeroSpatialJointDensity_measurable (X := X) s root D hp hW hL)
    (allocatedFixedPathLiftDensity_measurable_family B P R σ hB lower width g hg)

end FixedPath

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (hB : ∀ a : {a : LayerSamplerAxis I n //
    ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n //
    ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleLiftDensity_measurable :
    Measurable (fun p : Sample × (Output → ℝ) =>
      allocatedFixedPathLiftDensity B short R σ hB lower width (noise p.1) p.2) := by
  exact allocatedFixedPathLiftDensity_measurable_family B short R σ hB lower width
    noise (allocatedSampleRestrictedProfileNoise_measurable B U basis S short)

variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

theorem allocatedOriginalSampleForecastDensity_measurable :
    Measurable (fun p : Sample × Domain =>
      allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s root D hp hW hL hB lower width p.1 p.2) := by
  exact allocatedFixedPathForecastDensity_measurable_family
    (G := G) (Ω := Sample) (X := X) (I := I) (n := n)
    B short R σ s root D hp hW hL hB lower width
    noise (allocatedSampleRestrictedProfileNoise_measurable B U basis S short)

theorem allocatedOriginalSampleNormalizedForecast_measurable
    {δ : ℝ} (hδ : 0 < δ) :
    Measurable (fun p : Sample × Domain =>
      allocatedOriginalSampleNormalizedForecast (X := X)
        B U basis S s root D hp hW hL hB lower width hδ p.1 p.2) := by
  exact (Complex.measurable_ofReal.comp
    (allocatedOriginalSampleForecastDensity_measurable B U basis S hB lower width
      s root D hp hW hL)).div_const _

end VectorPolynomial
end Erdos3

end

end OAI
