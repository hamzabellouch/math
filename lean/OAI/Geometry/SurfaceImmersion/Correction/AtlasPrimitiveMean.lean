import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialMetric
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledInitialMap

namespace OAI

/-! Exact normalized mean identities for the global primitive iteration.
The residual is always that of the actual restored polynomial metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
local instance atlasPrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasPrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasPrimitiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasPrimitiveDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasPrimitiveSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasPrimitiveSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M) {n : A.centers → ℕ}

def normalizedPolynomialDefect
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε δ : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (G : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  (δ^2)⁻¹ • (γ-A.atlasPolynomialMetric P ε G)-γ

def polynomialMeanTarget
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε δ δ' : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (G : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  (δ^2)⁻¹ • (γ-A.atlasPolynomialMetric P ε G-δ'^2 • γ)

omit [CompactSpace M] in
lemma polynomialMeanTarget_eq
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε δ δ' : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (G : M → Space) :
    A.polynomialMeanTarget P ε δ δ' γ G =
      γ+A.normalizedPolynomialDefect P ε δ γ G-(δ'^2/δ^2) • γ := by
  funext x
  ext v w
  change (δ^2)⁻¹*(γ x v w-A.atlasPolynomialMetric P ε G x v w-δ'^2*γ x v w) =
    γ x v w+((δ^2)⁻¹*(γ x v w-A.atlasPolynomialMetric P ε G x v w)-γ x v w)-
      (δ'^2/δ^2)*γ x v w
  ring

lemma normalizedPolynomialDefect_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {ε δ : ℝ}
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.normalizedPolynomialDefect P ε δ γ G x)) :=
  (((hγ.sub_section (A.atlasPolynomialMetric_smooth hP hG ε)).const_smul_section).sub_section hγ)

lemma polynomialMeanTarget_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {ε δ δ' : ℝ}
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.polynomialMeanTarget P ε δ δ' γ G x)) :=
  ((hγ.sub_section (A.atlasPolynomialMetric_smooth hP hG ε)).sub_section
    (hγ.const_smul_section (a := δ'^2))).const_smul_section

omit [CompactSpace M] in
lemma normalizedPolynomialDefect_seed
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    {δ : ℝ} (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) :
    A.normalizedPolynomialDefect P ε δ (inducedTensor F) (Real.sqrt (1-δ^2) • F) =
      (-(δ^2)⁻¹) • A.atlasPolynomialValue P ε (Real.sqrt (1-δ^2) • F) := by
  unfold normalizedPolynomialDefect atlasPolynomialMetric
  rw [inducedTensor_const_smul hF,Real.sq_sqrt (sub_nonneg.mpr hδ1)]
  funext x
  ext v w
  change (δ^2)⁻¹*(inducedTensor F x v w-
    ((1-δ^2)*inducedTensor F x v w+
      A.atlasPolynomialValue P ε (Real.sqrt (1-δ^2) • F) x v w))-inducedTensor F x v w =
        -(δ^2)⁻¹*A.atlasPolynomialValue P ε (Real.sqrt (1-δ^2) • F) x v w
  field_simp
  ring

lemma normalizedPolynomialDefect_after_step
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    {ε δ δ' s C : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G G' : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    (hG' : ContMDiff planeModel spaceModel ∞ G')
    (hb : A.TensorWeightedBound s m C
      (A.atlasPolynomialMetric P ε G'-A.atlasPolynomialMetric P ε G-
        δ^2 • A.polynomialMeanTarget P ε δ δ' γ G)) :
    A.TensorWeightedBound s m (C/δ'^2) (A.normalizedPolynomialDefect P ε δ' γ G') := by
  have he : A.normalizedPolynomialDefect P ε δ' γ G' =
      (-(δ'^2)⁻¹) • (A.atlasPolynomialMetric P ε G'-A.atlasPolynomialMetric P ε G-
        δ^2 • A.polynomialMeanTarget P ε δ δ' γ G) := by
    funext x
    ext v w
    change (δ'^2)⁻¹*(γ x v w-A.atlasPolynomialMetric P ε G' x v w)-γ x v w =
      -(δ'^2)⁻¹*(A.atlasPolynomialMetric P ε G' x v w-A.atlasPolynomialMetric P ε G x v w-
        δ^2*((δ^2)⁻¹*(γ x v w-A.atlasPolynomialMetric P ε G x v w-δ'^2*γ x v w)))
    field_simp
    ring
  have hT := A.polynomialMeanTarget_smooth (ε := ε) (δ := δ) (δ' := δ') hP hγ hG
  have hsmooth := ((A.atlasPolynomialMetric_smooth hP hG' ε).sub_section
    (A.atlasPolynomialMetric_smooth hP hG ε)).sub_section
      (hT.const_smul_section (a := δ^2))
  have hh := A.tensorWeightedBound_const_smul hsmooth hb (-(δ'^2)⁻¹)
  rw [← he] at hh
  convert hh using 1
  rw [abs_neg,abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hδ'))]
  ring


/-- The next input stays in the same bounded family whenever the old
normalized defect does. -/
lemma polynomialMeanTarget_bound
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    {ε δ δ' s A₀ B₀ : ℝ} {m : ℕ} (hδ : 0 < δ) (hδ' : 0 ≤ δ')
    (hδδ : δ' ≤ δ) (hs : 0 ≤ s) (hA₀ : 0 ≤ A₀)
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    (hγb : A.TensorWeightedBound s m A₀ γ)
    (hDb : A.TensorWeightedBound s m B₀ (A.normalizedPolynomialDefect P ε δ γ G)) :
    A.TensorWeightedBound s m (2*A₀+B₀) (A.polynomialMeanTarget P ε δ δ' γ G) := by
  have hr : 0 ≤ δ'^2/δ^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hr1 : δ'^2/δ^2 ≤ 1 := (div_le_one (sq_pos_of_pos hδ)).2 (by nlinarith)
  have hscaled := A.tensorWeightedBound_const_smul hγ hγb (δ'^2/δ^2)
  have hscaled' : A.TensorWeightedBound s m A₀ ((δ'^2/δ^2) • γ) := by
    intro i
    apply (hscaled i).mono_const
    rw [abs_of_nonneg hr]
    exact mul_le_of_le_one_left hA₀ hr1
  have hD := A.normalizedPolynomialDefect_smooth (ε := ε) (δ := δ) hP hγ hG
  have hsum := A.tensorWeightedBound_add hγ hD hs hγb hDb
  have hsub := A.tensorWeightedBound_sub (hγ.add_section hD)
    (hγ.const_smul_section (a := δ'^2/δ^2)) hs hsum hscaled'
  rw [A.polynomialMeanTarget_eq]
  convert hsub using 1
  ring

omit [CompactSpace M] in
/-- Quantitative closeness of the next input in the fixed tensor encoding. -/
lemma polynomialMeanTarget_distance
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε δ δ' : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (G : M → Space)
    (x : JetPolynomial.Base) {a b : ℝ}
    (hD : ‖A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x‖ ≤ a)
    (hγ : ‖A.tensorEncode γ x‖ ≤ b) :
    ‖A.tensorEncode (A.polynomialMeanTarget P ε δ δ' γ G) x-A.tensorEncode γ x‖ ≤
      a+(δ'^2/δ^2)*b := by
  rw [A.polynomialMeanTarget_eq,A.tensorEncode_sub,A.tensorEncode_add,A.tensorEncode_smul]
  change ‖(A.tensorEncode γ x+A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x-
    (δ'^2/δ^2) • A.tensorEncode γ x)-A.tensorEncode γ x‖ ≤ _
  have he : (A.tensorEncode γ x+A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x-
    (δ'^2/δ^2) • A.tensorEncode γ x)-A.tensorEncode γ x =
    A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x-
      (δ'^2/δ^2) • A.tensorEncode γ x := by abel
  rw [he]
  calc
    _ ≤ ‖A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x‖+
        ‖(δ'^2/δ^2) • A.tensorEncode γ x‖ := norm_sub_le _ _
    _ = ‖A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x‖+
        (δ'^2/δ^2)*‖A.tensorEncode γ x‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ _ := add_le_add hD (mul_le_mul_of_nonneg_left hγ
      (div_nonneg (sq_nonneg _) (sq_nonneg _)))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
