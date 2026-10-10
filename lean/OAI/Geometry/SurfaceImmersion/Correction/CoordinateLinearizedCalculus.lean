import OAI.Geometry.SurfaceImmersion.Correction.CoordinateLinearizedSupport
import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticInteraction

namespace OAI

/-! Finite additivity and smoothness of the actual full linearized operator.
Coefficient smoothness is required only near the support of the variation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space) :
    coordinateFullLinearized P ε G 0 = 0 := by
  funext p
  exact coordinateFullLinearized_zero_of_notMem P ε G (by simp)

lemma coordinateFullLinearized_sum {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (a : Finset ι) (X : ι → RealModes.RField 4) (hX : ∀ i, ContDiff ℝ ∞ (X i)) :
    coordinateFullLinearized P ε G (fun p => ∑ i ∈ a, X i p) =
      fun p => ∑ i ∈ a, coordinateFullLinearized P ε G (X i) p := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change coordinateFullLinearized P ε G 0 = 0
    exact coordinateFullLinearized_zero P ε G
  | @insert i a hi ih =>
    have hs : ContDiff ℝ ∞ (fun p => ∑ j ∈ a, X j p) := ContDiff.sum fun j _ => hX j
    simp only [Finset.sum_insert hi]
    change coordinateFullLinearized P ε G (X i + fun p => ∑ j ∈ a, X j p) = _
    rw [coordinateFullLinearized_add P ε G (hX i) hs, ih]
    rfl

lemma coordinateFullLinearized_smooth {n : ℕ} {O : Set LowJet} {U : Set Base}
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {X : RealModes.RField 4} (hX : ContDiff ℝ ∞ X)
    (hXs : tsupport X ⊆ (modeSupport K : Set SmallModes.Base)) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinateFullLinearized P ε G X) := by
  let Xs : SupportedField (F := Fin 4 → ℝ) (modeSupport K) :=
    ContDiffMapSupportedIn.of_support_subset hX (subset_closure.trans hXs)
  let Xp := pullSupported planeCoordinateIsometry K Xs
  have hp : ContDiff ℝ ∞ (coordinateRealLinearized P ε G X 0) := by
    apply contDiff_pi.mpr
    intro k
    have hs : ContDiff ℝ ∞ (fun x => ∑ l, ε ^ (l.val + 1) * (P k l).variation G Xp (x, 0)) :=
      ContDiff.sum (s := Finset.univ) (fun l _ =>
      contDiff_const.mul ((P k l).variation_smooth_global hO hU K.isCompact.isClosed hKU
        (hP k l) hG Xp.contDiff hQ Xp.tsupport_subset 0))
    exact hs.comp planeCoordinateIsometry.symm.contDiff
  exact (contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
    (hG.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hX.contDiffOn)).add hp

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
