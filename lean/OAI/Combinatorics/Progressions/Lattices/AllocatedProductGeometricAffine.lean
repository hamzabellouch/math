import OAI.Combinatorics.Progressions.Dynamics.AllocatedActualCoarseBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedUniformCommonCover
import OAI.Combinatorics.Progressions.Lattices.AllocatedCommonPrimitiveAffine

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

section Data

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "hLayer" => layerSamplerDegree I n

def AllocatedUniformAccurateAffineData (p P E : ℝ) (hP : 0 ≤ P) (A T : ℝ≥0)
    (A₀ T₀ Kproj Kideal Ksite : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P ((E + 1) + 1 + 4)
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * P
  let gainLog := allocatedProfileGainLog m D P w
  let ε := physicalIdealErrorShare target gainLog
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) hLayer A T target gainLog
  let eTail := physicalIdealTailLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) G (G × Option (Fin dim)) hLayer A T m target gainLog
  let t := booleanMassPerturbationScale (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
    (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
    A T m 1 (ε / 2)
  0 ≤ e ∧ 0 ≤ eTail ∧ 0 < t ∧ t ≤ 1 ∧ t⁻¹ ≤ Real.exp eTail ∧
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      AllocatedCommonAccurateAffineAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p P E e t hP δ A₀ T₀ Kproj Kideal Ksite

theorem allocatedUniformCommonCover_accurate_affine
    {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    {A T : ℝ≥0} {A₀ T₀ Kproj Kideal Ksite : ℕ}
    (hcover : AllocatedUniformCommonCoverData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P (E + 1) hP A T A₀ T₀ Kproj Kideal Ksite) :
    AllocatedUniformAccurateAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T A₀ T₀ Kproj Kideal Ksite := by
  unfold AllocatedUniformAccurateAffineData
  intro D target w gainLog ε e eTail t
  obtain ⟨he, heTail, ht, ht1, hti, δ, hδ, hδ1, hδeq, hδe, hraw, hgenuine⟩ := hcover
  refine ⟨he, heTail, ht, ht1, hti, δ, hδ, hδ1, hδeq, hδe, ?_⟩
  exact allocatedCommonGenuineKernelAt_accurate_affine B hp hP hE he hvars
    (allocatedCommonGenuineCoverAt_kernel B hP hgenuine)

end Data

theorem exists_uniform_accurate_affine :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ m dim : ℕ, ∃ A₀ T₀ Kproj Kideal Ksite : ℕ,
      2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧ 2 ≤ Kideal ∧ 2 ≤ Ksite ∧
      ∀ {G : Type uG} [Fintype G] [DecidableEq G]
        {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {p P E : ℝ}, 0 ≤ p → ∀ hP : 0 ≤ P, 0 ≤ E →
        dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → p ≤ P →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) →
        AllocatedUniformAccurateAffineData.{uG,uI,uB,uJ,uQ,uX}
          (G := G) (dim := dim) B p P E hP A scalarSourceTransitionBound A₀ T₀ Kproj Kideal Ksite := by
  obtain ⟨A, hA, hfixed⟩ := exists_uniform_common_cover.{uG,uI,uB,uJ,uQ,uX}
  refine ⟨A, hA, ?_⟩
  intro m dim
  obtain ⟨A₀, T₀, Kproj, Kideal, Ksite, hA₀, hT₀, hKproj, hKideal, hKsite, hfixed⟩ := hfixed m dim
  refine ⟨A₀, T₀, Kproj, Kideal, Ksite, hA₀, hT₀, hKproj, hKideal, hKsite, ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hpP hvars hI hn hBlocks
  exact allocatedUniformCommonCover_accurate_affine B hp hP hE hvars
    (hfixed B hp hP (show 0 ≤ E + 1 by linarith) hdim hmP hpP hvars hI hn hBlocks)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

section Data

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "hLayer" => layerSamplerDegree I n

def AllocatedUniformNormalizedAffineData (p P E : ℝ) (hP : 0 ≤ P) (A T : ℝ≥0)
    (A₀ T₀ Kproj Kideal Ksite : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P ((E + 1) + 1 + 4)
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * P
  let gainLog := allocatedProfileGainLog m D P w
  let ε := physicalIdealErrorShare target gainLog
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) hLayer A T target gainLog
  let eTail := physicalIdealTailLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) G (G × Option (Fin dim)) hLayer A T m target gainLog
  let t := booleanMassPerturbationScale (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
    (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
    A T m 1 (ε / 2)
  0 ≤ e ∧ 0 ≤ eTail ∧ 0 < t ∧ t ≤ 1 ∧ t⁻¹ ≤ Real.exp eTail ∧
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      AllocatedCommonNormalizedAffineAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p P E e t hP δ A₀ T₀ Kproj Kideal Ksite

theorem allocatedUniformAccurateAffine_normalized
    {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    {A T : ℝ≥0} {A₀ T₀ Kproj Kideal Ksite Knorm : ℕ}
    (hT : 1 ≤ T₀) (hKsite : 1 ≤ Ksite) (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (hcover : AllocatedUniformAccurateAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T A₀ T₀ Kproj Kideal Ksite) :
    AllocatedUniformNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T A₀ T₀ Kproj Kideal (max Ksite Knorm) := by
  unfold AllocatedUniformNormalizedAffineData
  intro D target w gainLog ε e eTail t
  obtain ⟨he, heTail, ht, ht1, hti, δ, hδ, hδ1, hδeq, hδe, hcommon⟩ := hcover
  refine ⟨he, heTail, ht, ht1, hti, δ, hδ, hδ1, hδeq, hδe, ?_⟩
  exact allocatedCommonAccurateAffineAt_normalized B hp hP hE he hdim hmP hpP hvars hI hn
    hT hKsite hKnorm hnorm hcommon

end Data

theorem exists_uniform_normalized_affine :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ m dim : ℕ, ∃ A₀ T₀ Kproj Kideal Ksite : ℕ,
      2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧ 2 ≤ Kideal ∧ 2 ≤ Ksite ∧
      ∀ {G : Type uG} [Fintype G] [DecidableEq G]
        {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {p P E : ℝ}, 0 ≤ p → ∀ hP : 0 ≤ P, 0 ≤ E →
        dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → p ≤ P →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) →
        AllocatedUniformNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
          (G := G) (dim := dim) B p P E hP A scalarSourceTransitionBound A₀ T₀ Kproj Kideal Ksite := by
  obtain ⟨A, hA, hfixed⟩ := exists_uniform_accurate_affine.{uG,uI,uB,uJ,uQ,uX}
  refine ⟨A, hA, ?_⟩
  intro m dim
  obtain ⟨A₀, T₀, Kproj, Kideal, Ksite, hA₀, hT₀, hKproj, hKideal, hKsite, hfixed⟩ := hfixed m dim
  obtain ⟨Knorm, hKnorm, hnorm⟩ := exists_allocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m
  refine ⟨A₀, T₀, Kproj, Kideal, max Ksite Knorm, hA₀, hT₀, hKproj, hKideal,
    hKsite.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hpP hvars hI hn hBlocks
  exact allocatedUniformAccurateAffine_normalized B hp hP hE hdim hmP hpP hvars hI hn
    (by omega) (by omega) (by omega) hnorm
    (hfixed B hp hP hE hdim hmP hpP hvars hI hn hBlocks)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

section Data

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

theorem allocatedCommonNormalizedAffineAt_mono_width
    {p P E e s t : ℝ} {hP : 0 ≤ P} {δ : ℝ≥0} {A T Kproj Kideal Ksite : ℕ}
    (hst : s ≤ t)
    (hsource : AllocatedCommonNormalizedAffineAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite) :
    AllocatedCommonNormalizedAffineAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e s hP δ A T Kproj Kideal Ksite := by
  unfold AllocatedCommonNormalizedAffineAt
  intro Epoint c hc J _ U b R σ hR hσ hσs hR1 hRi hσi
  exact hsource hc U b hR hσ (fun j => (hσs j).trans hst) hR1 hRi hσi

def AllocatedGeometricNormalizedAffineData (p g P E : ℝ) (hP : 0 ≤ P) (A T : ℝ≥0)
    (A₀ T₀ Kproj Kideal Ksite : ℕ) : Prop :=
  let e := allocatedCommonSmoothingLog B dim A T p P E
  let c := allocatedCommonGeometryLog (G := G) B dim A T p g P E
  let r := allocatedCommonRadius m p g
  let σ := allocatedCommonWidth (G := G) B dim A T p P E
  0 ≤ c ∧ g ≤ c ∧ 0 < r ∧ r ≤ 1 ∧ 0 < σ ∧ σ ≤ 1 ∧
    r⁻¹ ≤ Real.exp c ∧ σ⁻¹ ≤ Real.exp c ∧
    (∀ (C : Fin m → ℝ), (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp g) → ∀ j,
      r ≤ allocatedBufferedPhysicalChartRadius (G := G) B (Fin dim) C j ∧
      r ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) C 1 j ∧
      r ≤ allocatedIdealCoverRadius (G := G) B
        (fun j => boundedBooleanJetRows (Fin dim) (j.val + 1)) C j) ∧
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      AllocatedCommonNormalizedAffineAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p P E e σ hP δ A₀ T₀ Kproj Kideal Ksite

theorem allocatedUniformNormalizedAffine_geometric
    {p g P E : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    {A T : ℝ≥0} {A₀ T₀ Kproj Kideal Ksite : ℕ}
    (hsource : AllocatedUniformNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T A₀ T₀ Kproj Kideal Ksite) :
    AllocatedGeometricNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p g P E hP A T A₀ T₀ Kproj Kideal Ksite := by
  obtain ⟨_, _, ht, _, hti, δ, hδ, hδ1, _, hδe, hcommon⟩ := hsource
  have hwidth := allocatedCommonWidth_le (G := G) B dim A T ht hti
  obtain ⟨hc, hgc, _, _, hri, hσi⟩ := allocatedCommonGeometryLog_bounds (G := G) B dim A T hp hg hP hE
  obtain ⟨hr, hr1, _⟩ := allocatedCommonRadius_bounds m hp hg
  obtain ⟨hσ, hσ1, _⟩ := allocatedCommonWidth_bounds (G := G) B dim A T hp hP hE
  refine ⟨hc, hgc, hr, hr1, hσ, hσ1, hri, hσi, ?_, δ, hδ, hδ1, hδe, ?_⟩
  · intro C hC hCg j
    exact allocatedCommonRadius_admissible B (fun j => boundedBooleanJetRows (Fin dim) (j.val + 1))
      hp hg (by simpa only [Fintype.card_fin] using hdim) hvars hI hn C hC hCg j
  · exact allocatedCommonNormalizedAffineAt_mono_width B hwidth hcommon

end Data

theorem exists_uniform_geometric_normalized_affine :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ m dim : ℕ, ∃ A₀ T₀ Kproj Kideal Ksite a : ℕ,
      2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧ 2 ≤ Kideal ∧ 2 ≤ Ksite ∧ 2 ≤ a ∧
      ∀ {G : Type uG} [Fintype G] [DecidableEq G]
        {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type uB) [∀ i, Fintype (B i)]
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → ∀ hP : 0 ≤ P, 0 ≤ E →
        dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → p ≤ P →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) →
        AllocatedGeometricNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
          (G := G) (dim := dim) B p g P E hP A scalarSourceTransitionBound A₀ T₀ Kproj Kideal Ksite ∧
        (allocatedCommonCoverParameter (G := G) B dim A₀ (max T₀ (max Kproj Kideal)) p
            (allocatedCommonGeometryLog (G := G) B dim A scalarSourceTransitionBound p g P E) P
            (allocatedCommonSmoothingLog B dim A scalarSourceTransitionBound p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + g + P + E + a) ^ a := by
  obtain ⟨A, hA, hfixed⟩ := exists_uniform_normalized_affine.{uG,uI,uB,uJ,uQ,uX}
  refine ⟨A, hA, ?_⟩
  intro m dim
  obtain ⟨A₀, T₀, Kproj, Kideal, Ksite, hA₀, hT₀, hKproj, hKideal, hKsite, hfixed⟩ := hfixed m dim
  obtain ⟨a, ha, hbound⟩ := exists_fixedGeometricCommonCoverThreshold_bound
    m dim A₀ (max T₀ (max Kproj Kideal)) Ksite A scalarSourceTransitionBound
  refine ⟨A₀, T₀, Kproj, Kideal, Ksite, a, hA₀, hT₀, hKproj, hKideal, hKsite, ha, ?_⟩
  intro G _ _ I _ n B _ p g P E hp hg hP hE hdim hmP hpP hvars hI hn hBlocks
  exact ⟨allocatedUniformNormalizedAffine_geometric B hp hg hP hE hdim hvars hI hn
    (hfixed B hp hP hE hdim hmP hpP hvars hI hn hBlocks),
    hbound B hp hg hP hE hdim hvars hI hn⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

section Data

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "hLayer" => layerSamplerDegree I n

def AllocatedUniformPrimitiveAffineData (p P E : ℝ) (hP : 0 ≤ P) (A T : ℝ≥0)
    (A₀ Ksize : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P ((E + 1) + 1 + 4)
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * P
  let gainLog := allocatedProfileGainLog m D P w
  let ε := physicalIdealErrorShare target gainLog
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) hLayer A T target gainLog
  let eTail := physicalIdealTailLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) G (G × Option (Fin dim)) hLayer A T m target gainLog
  let t := booleanMassPerturbationScale (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
    (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
    A T m 1 (ε / 2)
  0 ≤ e ∧ 0 ≤ eTail ∧ 0 < t ∧ t ≤ 1 ∧ t⁻¹ ≤ Real.exp eTail ∧
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      AllocatedCommonPrimitiveAffineAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p P E e t hP δ A₀ Ksize

theorem allocatedUniformNormalizedAffine_primitive
    {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    {A T : ℝ≥0} {A₀ T₀ Kproj Kideal Ksite Ksize : ℕ}
    (hsize : ∀ {c : ℝ}, 0 ≤ c →
      (allocatedCommonCoverParameter (G := G) B dim A₀ (max T₀ (max Kproj Kideal)) p c P
        (allocatedCommonSmoothingLog B dim A T p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + c + P + E + Ksize) ^ Ksize)
    (hsource : AllocatedUniformNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T A₀ T₀ Kproj Kideal Ksite) :
    AllocatedUniformPrimitiveAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T A₀ Ksize := by
  unfold AllocatedUniformPrimitiveAffineData
  intro D target w gainLog ε e eTail t
  obtain ⟨he, heTail, ht, ht1, hti, δ, hδ, hδ1, hδeq, hδe, hcommon⟩ := hsource
  refine ⟨he, heTail, ht, ht1, hti, δ, hδ, hδ1, hδeq, hδe, ?_⟩
  exact allocatedCommonNormalizedAffineAt_primitive B hp hP hvars hI hn hsize hcommon

end Data

theorem exists_uniform_primitive_affine :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ m dim : ℕ, ∃ A₀ Ksize : ℕ, 2 ≤ A₀ ∧ 2 ≤ Ksize ∧
      ∀ {G : Type uG} [Fintype G] [DecidableEq G]
        {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {p P E : ℝ}, 0 ≤ p → ∀ hP : 0 ≤ P, 0 ≤ E →
        dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → p ≤ P →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) →
        AllocatedUniformPrimitiveAffineData.{uG,uI,uB,uJ,uQ,uX}
          (G := G) (dim := dim) B p P E hP A scalarSourceTransitionBound A₀ Ksize := by
  obtain ⟨A, hA, hfixed⟩ := exists_uniform_normalized_affine.{uG,uI,uB,uJ,uQ,uX}
  refine ⟨A, hA, ?_⟩
  intro m dim
  obtain ⟨A₀, T₀, Kproj, Kideal, Ksite, hA₀, _, _, _, _, hfixed⟩ := hfixed m dim
  obtain ⟨Ksize, hKsize, hsize⟩ := exists_fixedRegularizedCommonCoverThreshold_bound
    m dim A₀ (max T₀ (max Kproj Kideal)) Ksite A scalarSourceTransitionBound
  refine ⟨A₀, Ksize, hA₀, hKsize, ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hpP hvars hI hn hBlocks
  apply allocatedUniformNormalizedAffine_primitive B hp hP hvars hI hn
    (Ksite := Ksite) (Kideal := Kideal) (Kproj := Kproj) (T₀ := T₀)
  · intro c hc
    exact hsize B hp hc hP hE hdim hvars hI hn
  · exact hfixed B hp hP hE hdim hmP hpP hvars hI hn hBlocks

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

section Data

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

def AllocatedProductGeometricNormalizedAffineData (p g P E : ℝ) (hP : 0 ≤ P) (A T : ℝ≥0)
    (A₀ T₀ Kproj Kideal Ksite : ℕ) : Prop :=
  let e := allocatedCommonSmoothingLog B dim A T p P E
  let c := allocatedProductGeometryLog (G := G) B dim A T p g P E
  let r := allocatedCommonProductRadius m p g
  let σ := allocatedCommonWidth (G := G) B dim A T p P E
  0 ≤ c ∧ g ≤ c ∧ 0 < r ∧ r ≤ 1 ∧ 0 < σ ∧ σ ≤ 1 ∧
    r⁻¹ ≤ Real.exp c ∧ σ⁻¹ ≤ Real.exp c ∧
    (∀ (C : Fin m → ℝ), (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp g) → ∀ j,
      r ≤ allocatedBufferedPhysicalChartRadius (G := G) B (Fin dim) C j ∧
      r ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) C 1 j ∧
      r ≤ allocatedIdealCoverRadius (G := G) B
        (fun j => boundedBooleanJetRows (Fin dim) (j.val + 1)) C j ∧
      r ≤ allocatedProductGridRadius (G := G) B
        (fun j => boundedBooleanJetRows (Fin dim) (j.val + 1)) C j) ∧
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      AllocatedCommonNormalizedAffineAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p P E e σ hP δ A₀ T₀ Kproj Kideal Ksite

theorem allocatedUniformNormalizedAffine_product_geometric
    {p g P E : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    {A T : ℝ≥0} {A₀ T₀ Kproj Kideal Ksite : ℕ}
    (hsource : AllocatedUniformNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T A₀ T₀ Kproj Kideal Ksite) :
    AllocatedProductGeometricNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p g P E hP A T A₀ T₀ Kproj Kideal Ksite := by
  obtain ⟨_, _, ht, _, hti, δ, hδ, hδ1, _, hδe, hcommon⟩ := hsource
  have hwidth := allocatedCommonWidth_le (G := G) B dim A T ht hti
  obtain ⟨hc, hgc, _, _, hri, hσi⟩ := allocatedProductGeometryLog_bounds (G := G) B dim A T hp hg hP hE
  obtain ⟨_, hr, hr1, _, _, _, _⟩ := allocatedCommonProductRadius_bounds m hp hg
  obtain ⟨hσ, hσ1, _⟩ := allocatedCommonWidth_bounds (G := G) B dim A T hp hP hE
  refine ⟨hc, hgc, hr, hr1, hσ, hσ1, hri, hσi, ?_, δ, hδ, hδ1, hδe, ?_⟩
  · intro C hC hCg j
    exact allocatedCommonProductRadius_admissible B (fun j => boundedBooleanJetRows (Fin dim) (j.val + 1))
      hp hg (by simpa only [Fintype.card_fin] using hdim) hvars hI hn C hC hCg j
  · exact allocatedCommonNormalizedAffineAt_mono_width B hwidth hcommon

end Data

theorem exists_uniform_product_geometric_normalized_affine :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ m dim : ℕ, ∃ A₀ T₀ Kproj Kideal Ksite a : ℕ,
      2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧ 2 ≤ Kideal ∧ 2 ≤ Ksite ∧ 2 ≤ a ∧
      ∀ {G : Type uG} [Fintype G] [DecidableEq G]
        {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type uB) [∀ i, Fintype (B i)]
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → ∀ hP : 0 ≤ P, 0 ≤ E →
        dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → p ≤ P →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) →
        AllocatedProductGeometricNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
          (G := G) (dim := dim) B p g P E hP A scalarSourceTransitionBound A₀ T₀ Kproj Kideal Ksite ∧
        (allocatedCommonCoverParameter (G := G) B dim A₀ (max T₀ (max Kproj Kideal)) p
            (allocatedProductGeometryLog (G := G) B dim A scalarSourceTransitionBound p g P E) P
            (allocatedCommonSmoothingLog B dim A scalarSourceTransitionBound p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + g + P + E + a) ^ a := by
  obtain ⟨A, hA, hfixed⟩ := exists_uniform_normalized_affine.{uG,uI,uB,uJ,uQ,uX}
  refine ⟨A, hA, ?_⟩
  intro m dim
  obtain ⟨A₀, T₀, Kproj, Kideal, Ksite, hA₀, hT₀, hKproj, hKideal, hKsite, hfixed⟩ := hfixed m dim
  obtain ⟨a, ha, hbound⟩ := exists_fixedProductGeometricCommonCoverThreshold_bound
    m dim A₀ (max T₀ (max Kproj Kideal)) Ksite A scalarSourceTransitionBound
  refine ⟨A₀, T₀, Kproj, Kideal, Ksite, a, hA₀, hT₀, hKproj, hKideal, hKsite, ha, ?_⟩
  intro G _ _ I _ n B _ p g P E hp hg hP hE hdim hmP hpP hvars hI hn hBlocks
  exact ⟨allocatedUniformNormalizedAffine_product_geometric B hp hg hP hE hdim hvars hI hn
    (hfixed B hp hP hE hdim hmP hpP hvars hI hn hBlocks),
    hbound B hp hg hP hE hdim hvars hI hn⟩

end Erdos3.VectorPolynomial

end

end OAI
