import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearProfilesOnBall
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartScaleTransition
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualProbeProfiles

namespace OAI

/-! # Exact scale transport of the actual Cartan profiles on a fixed ball -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℝ L]

/-- The same group point in the two word charts, restricted to a fixed
coordinate ball. Larger physical scales contract this ball. -/
def wordBallScaleTransition
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (R : ℝ) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) :
    C(Metric.closedBall (0 : Fin (finrank ℝ L) → ℝ) R,
      Metric.closedBall (0 : Fin (finrank ℝ L) → ℝ) R) :=
  closedBallLinearSelf
    (basisScaleTransition (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ))
      (Real.log r) (Real.log t)).toContinuousLinearEquiv.toContinuousLinearMap
    (norm_basisScaleTransition_le _ _ (fun _j => Nat.cast_nonneg _)
      (Real.log_le_log hr hrt)) R

theorem wordBallScaleTransition_height
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (height : L →ₗ[ℝ] W) (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    (R : ℝ) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t)
    (z : Metric.closedBall (0 : Fin (finrank ℝ L) → ℝ) R) :
    (t / r) • height ((WordBasisSelections.basis X S β).equivFun.symm
      (wordBallScaleTransition X S β R hr hrt z)) =
      height ((WordBasisSelections.basis X S β).equivFun.symm z) := by
  change (t / r) • height ((WordBasisSelections.basis X S β).equivFun.symm
    (basisScaleTransition _ _ (Real.log r) (Real.log t) z)) = _
  rw [wordChartScaleTransition_height X S β height hkill hr (hr.trans_le hrt), smul_smul]
  have he : t / r * (r / t) = 1 := by field_simp [hr.ne', (hr.trans_le hrt).ne']
  rw [he, one_smul]

section ActualProfile

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

omit [Fintype I] [DecidableEq I] in
theorem CartanFactorModel.wordBall_profile_scale_eq
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (R : ℝ) {r t : ℝ} (hr : 1 ≤ r) (hrt : r ≤ t) (k : F.N.carrier) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)
    let profile := fun u => rescaledContinuousProfile J hJ x (F.inclusionN k)
      (max (Real.log u) 0)
      (F.profileChart (exponentialRescaleBasis b cost (max (Real.log u) 0)))
      (F.continuous_profileChart hD _)
    (profile r).restrict (Metric.closedBall 0 R) =
      rescaleCompactProfile (t / r)
        (wordBallScaleTransition X S β R (zero_lt_one.trans_le hr) hrt)
        ((profile t).restrict (Metric.closedBall 0 R)) := by
  dsimp only
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ht0 : 0 < t := hr0.trans_le hrt
  have hlr : max (Real.log r) 0 = Real.log r := max_eq_left (Real.log_nonneg hr)
  have hlt : max (Real.log t) 0 = Real.log t := max_eq_left (Real.log_nonneg (hr.trans hrt))
  ext z
  change rescaledMapProfile J x (F.inclusionN k) (max (Real.log r) 0)
      (F.profileChart _) z.val =
    (t / r) • rescaledMapProfile J x (F.inclusionN k) (max (Real.log t) 0)
      (F.profileChart _) (wordBallScaleTransition X S β R hr0 hrt z).val
  rw [hlr, hlt]
  have hpoint : F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)) z.val =
    F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log t))
      (wordBallScaleTransition X S β R hr0 hrt z).val := by
    unfold CartanFactorModel.profileChart
    change F.inclusionD (F.ExpD (F.D.equiv _)) = F.inclusionD (F.ExpD (F.D.equiv
      ((exponentialRescaleBasis _ _ (Real.log t)).equivFun.symm
        (basisScaleTransition _ _ (Real.log r) (Real.log t) z.val))))
    rw [basisScaleTransition_point]
  have he := scaled_profile_eq_of_chart_eq J x (F.inclusionN k) hr0 ht0 _ _ _ _ hpoint
  have hh := congrArg (fun w : W => r⁻¹ • w) he
  have hcoeff : r⁻¹ * t = t / r := by ring
  simpa only [smul_smul, inv_mul_cancel₀ hr0.ne', one_smul, hcoeff] using hh

end ActualProfile
end PolycyclicRecognition

end

end OAI
