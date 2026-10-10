import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialMetric
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance polynomialValueFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialValueFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialValueDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialValueDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialValueSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialValueSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem polynomial_outer_cutoff (i : A.centers)
    {U : Set JetPolynomial.Base} (hU : IsOpen U)
    (houter : (chart (i : M)) '' tsupport (A.outer i) ⊆ U) :
    ∃ (K : Compacts JetPolynomial.Base) (χ : SupportedField (F := ℝ) K),
      tsupport (χ : JetPolynomial.Base → ℝ) ⊆ U ∧
      ∀ p ∈ tsupport (A.outer i), χ (chart (i : M) p) = 1 := by
  let S : Set JetPolynomial.Base := (chart (i : M)) '' tsupport (A.outer i)
  have hS : IsCompact S := (isClosed_tsupport (A.outer i)).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.outer_support i))
  obtain ⟨V,hV,hSV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure hS hU houter
  obtain ⟨χ,hχ,_,hχs,hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV hS.isClosed hSV
  let K : Compacts JetPolynomial.Base := ⟨closure V,hVc⟩
  let χ' : SupportedField (F := ℝ) K := ContDiffMapSupportedIn.of_support_subset hχ
    (by rw [hχs]; exact subset_closure)
  refine ⟨K,χ',?_,?_⟩
  · change closure (Function.support χ) ⊆ U
    rw [hχs]
    exact hVU
  · intro p hp
    exact (hχone (chart (i : M) p)).mp ⟨p,hp,rfl⟩

/-- Fixed local low-jet bounds give a global bound on the actual restored
polynomial value. Its scale loss is the maximum of the chartwise losses. -/
theorem atlas_polynomial_value_bound {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (m : ℕ) (B : A.centers → ℝ) (hB : ∀ i, 1 ≤ B i) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      (∀ i, MapsTo (lowJet (A.jetChartMap i G)) (U i) (Q i)) →
      ∀ (s ε : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ i, WeightedEstimates.WeightedBound (U i) s (m + tensorOrder (P i)) (B i)
        (lowJet (A.jetChartMap i G))) →
      A.TensorWeightedBound s m
        (D * ε / s ^ (Finset.univ.sup fun i : A.centers => tensorLoss (P i)))
        (A.atlasPolynomialValue P ε G) := by
  classical
  choose K χ hχU hχone using fun i => A.polynomial_outer_cutoff i (hU i) (houter i)
  choose C hC hc using fun i => coordinatePolynomialValue_bound (hQ i) (P i) (hP i)
    m (B i) (hB i)
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  let N : A.centers → ℝ := fun i => supportedWeightedSeminorm (K i) 1 m (χ i)
  have hN (i) : 0 ≤ N i := apply_nonneg _ _
  let E : A.centers → ℝ := fun i => 2 ^ m * N i * C i
  have hE (i) : 0 ≤ E i := mul_nonneg (mul_nonneg (by positivity) (hN i)) (hC i)
  let E₀ : ℝ := ∑ i, E i
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg (fun i _ => hE i)
  let loss : ℕ := Finset.univ.sup fun i : A.centers => tensorLoss (P i)
  refine ⟨D * E₀,mul_nonneg hD hE₀,?_⟩
  intro G hG hGQ s ε hs hs1 hε hε1 hb
  let f : A.centers → SmallModes.Base → Tensor :=
    fun i => coordinatePolynomialValue (P i) ε (A.jetChartMap i G) 0
  let ψ : A.centers → SmallModes.Base → ℝ :=
    fun i => (χ i) ∘ planeCoordinateIsometry.symm
  let g : A.centers → SmallModes.Base → Tensor := fun i x => ψ i x • f i x
  have hf (i) : ContDiff ℝ ∞ (f i) :=
    coordinatePolynomialValue_smooth (hP i) (A.jetChartMap_smooth i hG) ε
  have hψ (i) : ContDiff ℝ ∞ (ψ i) := (χ i).contDiff.comp planeCoordinateIsometry.symm.contDiff
  have hg (i) : ContDiff ℝ ∞ (g i) := (hψ i).smul (hf i)
  have hψsp (i) : tsupport (ψ i) ⊆ planeCoordinateIsometry.symm ⁻¹' U i := by
    apply (show tsupport (ψ i) ⊆
      planeCoordinateIsometry.symm ⁻¹' tsupport (χ i) from ?_).trans (preimage_mono (hχU i))
    apply closure_minimal _ ((isClosed_tsupport (χ i)).preimage
      planeCoordinateIsometry.symm.continuous)
    intro x hx
    exact subset_tsupport (χ i) hx
  have hψb (i) : WeightedEstimates.WeightedBound univ s m (N i) (ψ i) :=
    weightedBound_comp_isometry planeCoordinateIsometry.symm (χ i).contDiff
      ((weightedBound_of_supportedSeminorm (1 : ℝ≥0) m (χ i)).shrink_scale hs.le hs1)
  have hgb (i) : WeightedEstimates.WeightedBound univ s m (E i * ε / s ^ tensorLoss (P i)) (g i) := by
    let V := planeCoordinateIsometry.symm ⁻¹' U i
    have hV : IsOpen V := (hU i).preimage planeCoordinateIsometry.symm.continuous
    have hlocal := (hψb i).restrict_open hV
    have hpoly := hc i (U i) (hU i) (A.jetChartMap_smooth i hG) (hGQ i)
      s ε hs hs1 hε hε1 (hb i)
    have hprod := hlocal.smul_real hV.uniqueDiffOn hs.le (hN i)
      (div_nonneg (mul_nonneg (hC i) hε) (pow_nonneg hs.le _))
      (hψ i).contDiffOn (hf i).contDiffOn hpoly
    have heq : 2 ^ m * N i * (C i * ε / s ^ tensorLoss (P i)) =
        E i * ε / s ^ tensorLoss (P i) := by dsimp [E]; ring
    rw [heq] at hprod
    exact hprod.extend_support hV
      ((tsupport_smul_subset_left (ψ i) (f i)).trans (hψsp i))
      (div_nonneg (mul_nonneg (hE i) hε) (pow_nonneg hs.le _))
  have hglobal (i) : WeightedEstimates.WeightedBound univ s m (E₀ * ε / s ^ loss) (g i) := by
    apply (hgb i).mono_const
    have hEi : E i ≤ E₀ := Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)
    calc
      E i * ε / s ^ tensorLoss (P i) ≤ E₀ * ε / s ^ tensorLoss (P i) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hEi hε) (pow_nonneg hs.le _)
      _ ≤ E₀ * ε / s ^ loss := div_le_div_of_nonneg_left (mul_nonneg hE₀ hε)
        (pow_pos hs _) (pow_le_pow_of_le_one hs.le hs1
          (Finset.le_sup (f := fun i : A.centers => tensorLoss (P i)) (Finset.mem_univ i)))
  have hout := hd g s (E₀ * ε / s ^ loss) hs hs1
    (div_nonneg (mul_nonneg hE₀ hε) (pow_nonneg hs.le _)) hg hglobal
  have heq : A.tensorPlaneRestore g = A.atlasPolynomialValue P ε G := by
    funext p
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p ∈ tsupport (A.outer i)
    · have hχp := hχone i p hp
      change A.outer i p • (A.tensorTriv i).symmL ℝ p
          (fiberFromThree ((χ i) (planeCoordinateIsometry.symm
            (planeCoordinateIsometry (chart (i : M) p))) • f i
              (planeCoordinateIsometry (chart (i : M) p)))) = _
      simp only [LinearIsometryEquiv.symm_apply_apply,hχp,one_smul]
      rfl
    · have hz : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport hp
      simp only [bundleRestore,hz,zero_smul]
  rw [heq] at hout
  convert hout using 1
  dsimp [loss]
  ring


/-- One profile controls every derivative order, before the actual map and
scales are chosen. -/
theorem atlas_polynomial_value_bounds {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (B : A.centers → ℕ → ℝ) (hB : ∀ i m, 1 ≤ B i m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      (∀ i, MapsTo (lowJet (A.jetChartMap i G)) (U i) (Q i)) →
      ∀ (s ε : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ i m, WeightedEstimates.WeightedBound (U i) s (m + tensorOrder (P i)) (B i m)
        (lowJet (A.jetChartMap i G))) →
      ∀ m, A.TensorWeightedBound s m
        (D m * ε / s ^ (Finset.univ.sup fun i : A.centers => tensorLoss (P i)))
        (A.atlasPolynomialValue P ε G) := by
  choose D hD hb using fun m => A.atlas_polynomial_value_bound P hP U hU houter Q hQ
    m (fun i => B i m) (fun i => hB i m)
  refine ⟨D,hD,?_⟩
  intro G hG hGQ s ε hs hs1 hε hε1 hjet m
  exact hb m G hG hGQ s ε hs hs1 hε hε1 (fun i => hjet i m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
