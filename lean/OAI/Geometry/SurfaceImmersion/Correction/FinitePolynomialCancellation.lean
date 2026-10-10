import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveData
import OAI.Geometry.SurfaceImmersion.Correction.CoordinateLinearizedCalculus

namespace OAI

/-! Finite cancellation by the actual polynomial phase solvers. All
summands are constructed with one common accuracy and wavelength. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

theorem finite_polynomial_cancellation {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ) (K : ι → Compacts Base)
    {τ : ℝ} {s : ℝ≥0} (c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (f : ∀ i, SupportedField (F := ComplexTensor) (modeSupport (K i))) (q : ℕ) :
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧
      tsupport X ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m (∑ i, (c i).size (f i) q m) X) ∧
      (∀ m, WeightedBound Set.univ τ m (∑ i, (c i).residual (f i) q m)
        (fun x => coordinateFullLinearized P ε G X x +
          ∑ i, QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x)) := by
  classical
  choose X hsm hsp hb hr using fun i => (c i).exists_solution hτ hs hτs hs1 hε hsmall (f i) q
  refine ⟨(fun p => ∑ i, X i p), ContDiff.sum (fun i _ => hsm i), ?_, ?_, ?_⟩
  · apply closure_minimal _ (isClosed_iUnion_of_finite fun i => (modeSupport (K i)).isCompact.isClosed)
    intro p hp
    by_contra hn
    apply hp
    apply Finset.sum_eq_zero
    intro i _
    exact image_eq_zero_of_notMem_tsupport (fun hx => hn (Set.mem_iUnion.mpr ⟨i, hsp i hx⟩))
  · intro m
    exact WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => (hsm i).contDiffOn) (fun i _ => hb i m)
  · intro m
    have he : (fun x => coordinateFullLinearized P ε G (fun p => ∑ i, X i p) x +
        ∑ i, QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x) =
        (fun x => ∑ i, (coordinateFullLinearized P ε G (X i) x +
          QuadraticMean.displacement τ (coordinatePhase (φ i)) (f i) x)) := by
      rw [coordinateFullLinearized_sum P ε G Finset.univ X hsm]
      funext x
      exact Finset.sum_add_distrib.symm
    rw [he]
    apply WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => ?_) (fun i _ => hr i m)
    exact ((coordinateFullLinearized_smooth (c i).openO (c i).openU P (c i).smoothP hG
      (c i).mapsG (K i) (c i).supportU (hsm i) (hsp i) ε).add
      (contDiffOn_univ.mp (RealModes.contDiffOn_displacement
        (((c i).smoothPhase.comp planeCoordinateIsometry.symm.contDiff).contDiffOn)
        (f i).contDiff.contDiffOn τ))).contDiffOn

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
