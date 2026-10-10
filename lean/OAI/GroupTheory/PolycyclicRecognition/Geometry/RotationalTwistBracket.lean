import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationalTwistInvariantField
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PullbackVectorFieldCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteFrameDifferentiation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ReweightedFrameBracket

namespace OAI

/-! # The bracket of the actual invariant rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open Filter VectorField
open scoped Manifold ContDiff Topology

variable {E G K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g) [hτ : Fact (Continuous τ)]
  (hα : ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
    (fun p : G × G => α ((τ p.1)⁻¹) p.2))

attribute [local instance] semidirectProductTopology
local instance : ChartedSpace E (rotationalTwist α τ hinv) :=
  rotationalTwistChartedSpace α τ hinv

include hα hinv in
theorem rotationalTwist_bracket
    (R : G → E →L[ℝ] E)
    (hR : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) ∞ R)
    (hR₀ : R 1 = ContinuousLinearMap.id ℝ E)
    (hRd : ∀ (g : G) (v : E),
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (α ((τ g)⁻¹)) 1 v = R g v)
    (v w : E) :
    (show E from mlieBracket (𝓘(ℝ,E))
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := rotationalTwist α τ hinv) v)
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := rotationalTwist α τ hinv) w) 1) =
    (show E from mlieBracket (𝓘(ℝ,E))
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := G) v)
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := G) w) 1) +
      (show E →L[ℝ] E from mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) R 1 v) w -
      (show E →L[ℝ] E from mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) R 1 w) v := by
  let : LieGroup (𝓘(ℝ,E)) ∞ (rotationalTwist α τ hinv) :=
    rotationalTwistLieGroup α τ hinv hα
  let e := rotationalTwistHomeomorph α τ hinv hτ.out
  let φ := extChartAt (𝓘(ℝ,E)) (1 : G)
  let y₀ := φ 1
  let A : E → E →L[ℝ] E := chartInvariantFrame (E := E) (1 : G)
  let B : E → E →L[ℝ] E := fun y => R (φ.symm y)
  have he1 : e (1 : rotationalTwist α τ hinv) = 1 := rfl
  have hfields (u : E) :
      chartVectorField (1 : rotationalTwist α τ hinv)
        (mulInvariantVectorField (I := 𝓘(ℝ,E)) u) =ᶠ[𝓝 y₀]
      (fun y => A y (B y u)) := by
    have htarget : φ.target ∈ 𝓝 y₀ := by
      simpa only [φ,y₀,mfld_simps,nhdsWithin_univ] using
        extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ,E)) (1 : G)
    filter_upwards [htarget] with y hy
    have hcoords := chartVectorField_pullback e (1 : rotationalTwist α τ hinv)
      (mulInvariantVectorField (I := 𝓘(ℝ,E)) u) y (by simpa only [he1] using hy)
    change _ = chartVectorField (1 : G)
      (fun g => mulInvariantVectorField (I := 𝓘(ℝ,E)) u (e.symm g)) y at hcoords
    rw [hcoords]
    change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ.symm y).inverse
        (mulInvariantVectorField (I := 𝓘(ℝ,E)) u (e.symm (φ.symm y))) = _
    have hinvfield := rotationalTwist_invariant_field α τ hinv hα
      (e.symm (φ.symm y)) u
    have hg : (e.symm (φ.symm y)).val.left = φ.symm y := e.apply_symm_apply _
    rw [hg,hRd] at hinvfield
    exact congrArg (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ.symm y).inverse hinvfield
  have hi : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ φ.symm y₀ := by
    simpa only [φ,y₀,mfld_simps,contMDiffWithinAt_univ] using
      contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ,E)) (n := ∞) (1 : G)
  have hB : DifferentiableAt ℝ B y₀ :=
    ((hR 1).comp_of_eq hi (extChartAt_to_inv (1 : G))).contDiffAt.differentiableAt (by simp)
  have hA := differentiableAt_chartInvariantFrame (E := E) (1 : G)
  have hB₀ : B y₀ = ContinuousLinearMap.id ℝ E := by
    change R (φ.symm (φ 1)) = _
    rw [extChartAt_to_inv,hR₀]
  have hA₀ : A y₀ = ContinuousLinearMap.id ℝ E := chartInvariantFrame_one
  have hdb : fderiv ℝ B y₀ = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) R 1 :=
    fderiv_chart_comp_base hR 1
  have hb := lieBracket_reweighted_frame hA.hasFDerivAt hB.hasFDerivAt hA₀ hB₀ v w
  have hnew := mlieBracket_eq_chartBracket
    (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := rotationalTwist α τ hinv) v)
    (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := rotationalTwist α τ hinv) w) 1
  have hold := mlieBracket_eq_chartBracket
    (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := G) v)
    (mulInvariantVectorField (I := 𝓘(ℝ,E)) (G := G) w) 1
  have hc := Filter.EventuallyEq.lieBracket_vectorField_eq (𝕜 := ℝ) (hfields v) (hfields w)
  change _ = lieBracket ℝ (fun y => A y (B y v)) (fun y => A y (B y w)) y₀ at hc
  change _ = lieBracket ℝ (chartVectorField (1 : rotationalTwist α τ hinv)
    (mulInvariantVectorField (I := 𝓘(ℝ,E)) v))
    (chartVectorField (1 : rotationalTwist α τ hinv)
    (mulInvariantVectorField (I := 𝓘(ℝ,E)) w)) y₀ at hnew
  change _ = lieBracket ℝ (fun y => A y v) (fun y => A y w) y₀ at hold
  exact hnew.trans (hc.trans (hb.trans (by rw [hdb,← hold]; rfl)))

end PolycyclicRecognition

end

end OAI
