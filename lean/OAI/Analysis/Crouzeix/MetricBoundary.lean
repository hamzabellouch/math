import Mathlib
import OAI.Analysis.Crouzeix.BoundaryMoments

namespace OAI

/-! Metric Boundary. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

lemma spectralRadius_coordinate_lt_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (A : Operator H) (hKU : numericalClosure A ⊆ U) :
    spectralRadius ℂ (holomorphicEval A R.domain R.f) < 1 := by
  apply spectralRadius_holomorphicEval_lt_one A R.isOpen_domain
    (hKU.trans (subset_closure.trans R.closure_subset_domain)) R.analytic_f.differentiableOn
  intro z hz
  exact mem_ball_zero_iff.mp (R.bijective_f.mapsTo (hKU hz))

end Conformal.InteriorCollar

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {n : ℕ} (hn : 0 < n) (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U)

include C hn hKU hU hc hb in
lemma minimizing_metric_sqrt_le_two (κ : ℝ) (H : Coeff n)
    (hH : CrouzeixHilbert.Metric.Feasible
      (operatorToMatrix n (holomorphicEval A R.domain R.f)) (κ ^ 2) H)
    (hmin : ∀ s J, CrouzeixHilbert.Metric.Feasible
      (operatorToMatrix n (holomorphicEval A R.domain R.f)) s J → κ ^ 2 ≤ s) :
    κ ≤ 2 := by
  by_cases hk : κ ≤ 1
  · exact hk.trans (by norm_num)
  have hκ : 1 < κ := lt_of_not_ge hk
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  let T : Coeff n := operatorToMatrix n (holomorphicEval A R.domain R.f)
  change CrouzeixHilbert.Metric.Feasible T (κ ^ 2) H at hH
  have hT : spectralRadius ℂ T < 1 := by
    simpa only [T, operatorToMatrix_apply, spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq] using
      R.spectralRadius_coordinate_lt_one A hKU
  let S := e (CFC.sqrt H)
  let D := e (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))
  have hN : ‖D‖ ≤ 1 := by
    rw [← Matrix.cstar_norm_def]
    exact hH.sqrt_similarity.2.1
  have hD : spectralRadius ℂ D < 1 := by
    simpa only [D, spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq, hH.sqrt_spectrum] using hT
  have hI : S * holomorphicEval A R.domain R.f = D * S := by
    have he : e T = holomorphicEval A R.domain R.f := e.apply_symm_apply _
    rw [← he]
    change e (CFC.sqrt H) * e T = e _ * e (CFC.sqrt H)
    rw [← map_mul, ← map_mul, mul_assoc (CFC.sqrt H * T),
      Ring.inverse_mul_cancel _ hH.sqrt_similarity.1, mul_one]
  obtain ⟨X,Y,Q,V,_,_,_,_,hXY,hX,hY,hx,hy,hV,hKV,_,hQ,hQV,_,hQI⟩ :=
    disk_endpoint_extremal hn T hT hκ H hH hmin
  let W := R.domain ∩ R.f ⁻¹' V
  have hW : IsOpen W := R.analytic_f.continuousOn.isOpen_inter_preimage R.isOpen_domain hV
  have hUW : closure U ⊆ W := fun z hz =>
    ⟨R.closure_subset_domain hz, hKV (R.closed_f.mapsTo hz)⟩
  have hfW : EntrywiseHolomorphic W (matrixRationalFunction Q ∘ R.f) := fun i j =>
    (hQ i j).comp (R.analytic_f.differentiableOn.mono inter_subset_left) (fun z hz => hz.2)
  let F := C.matrixAnalyticTrace hUW (matrixRationalFunction Q ∘ R.f) hfW.continuousOn
  have hF : ∀ t, ‖F t‖ ≤ 1 := by
    intro t
    exact hQV _ (le_of_eq (R.boundary_norm _ (C.boundaryMap_mem_frontier t)))
  let F₀ : C(CircleSpace, Coeff n) :=
    ⟨fun t => matrixRationalFunction Q (circleCoordinate t),
      hQ.continuousOn.comp_continuous circleCoordinate.continuous
        (fun t => hKV (mem_closedBall_zero_iff.mpr (norm_circleCoordinate t).le))⟩
  have hF₀ : F = F₀.comp (C.interiorAngle R) := by
    ext t i j
    change matrixRationalFunction Q (R.f (C.boundaryMap t)) i j =
      matrixRationalFunction Q (circleCoordinate (C.interiorAngle R t)) i j
    rw [C.circleCoordinate_interiorAngle R]
    rfl
  have hInt : tensorIntegral (C.matrixDensity R D hD) F (vectorization X) = vectorization Y := by
    rw [hF₀, C.tensorIntegral_matrixDensity_pullback R D hD hU hc]
    change (∫ t, tensorOperator (Disk.phi D t)
      (matrixRationalFunction Q (fourier 1 t)) ∂Disk.σ) (vectorization X) = _
    rw [Disk.integral_matrixHolomorphic D hN hD hV hKV hQ]
    exact hQI
  have hS : IsSelfAdjoint (tensorOperator S (1 : Coeff n)) := by
    change star (tensorOperator S (1 : Coeff n)) = tensorOperator S (1 : Coeff n)
    rw [← tensorOperator_star, star_one]
    have hs : IsSelfAdjoint S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg H)).map e
    rw [hs.star_eq]
  exact endpoint_le_two_of_physical_tests (C.boundaryOperator hc n)
    (C.norm_boundaryOperator_le hc n) (C.matrixResolventDensity A hKU hU)
    (C.matrixDensity R D hD) F (C.matrixResolventDensity_posSemidef A hKU hU hc)
    (C.matrixDensity_posSemidef R D hD hN) (C.integral_matrixDensity R D hD hU hc) hF
    (C.boundaryCauchy_left_module hU hc hb hW hUW hfW hF)
    (C.boundaryCauchy_right_module hU hc hb hW hUW hfW hF)
    (tensorOperator S (1 : Coeff n)) hS X Y hX hY hXY κ (zero_lt_one.trans hκ) hx hy hInt
    (C.physical_laurent_tests A hKU hU R hc D S hN hD hI)

include C hn hKU hU hc hb in
lemma exists_conformal_contraction :
    ∃ S J D : Operator (EuclideanSpace ℂ (Fin n)),
      J * S = 1 ∧ S * J = 1 ∧ ‖S‖ * ‖J‖ ≤ 2 ∧ ‖D‖ ≤ 1 ∧
      spectralRadius ℂ D < 1 ∧ S * holomorphicEval A R.domain R.f = D * S := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  let T : Coeff n := operatorToMatrix n (holomorphicEval A R.domain R.f)
  have hT : spectralRadius ℂ T < 1 := by
    simpa only [T, operatorToMatrix_apply, spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq] using
      R.spectralRadius_coordinate_lt_one A hKU
  obtain ⟨τ,H,hH,hτ,hmin⟩ := CrouzeixHilbert.Metric.exists_minimizing_metric T hT
  have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
  have hκ : Real.sqrt τ ≤ 2 := C.minimizing_metric_sqrt_le_two R hn A hKU hU hc hb
    (Real.sqrt τ) H (by simpa only [Real.sq_sqrt hτ0] using hH)
    (by simpa only [Real.sq_sqrt hτ0] using hmin)
  let S := e (CFC.sqrt H)
  let J := e (Ring.inverse (CFC.sqrt H))
  let D := e (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))
  refine ⟨S,J,D,?_,?_,?_,?_,?_,?_⟩
  · change e _ * e _ = 1
    rw [← map_mul, Ring.inverse_mul_cancel _ hH.sqrt_similarity.1, map_one]
  · change e _ * e _ = 1
    rw [← map_mul, Ring.mul_inverse_cancel _ hH.sqrt_similarity.1, map_one]
  · change ‖e _‖ * ‖e _‖ ≤ 2
    rw [← Matrix.cstar_norm_def, ← Matrix.cstar_norm_def]
    exact hH.sqrt_similarity.2.2.trans hκ
  · change ‖e _‖ ≤ 1
    rw [← Matrix.cstar_norm_def]
    exact hH.sqrt_similarity.2.1
  · simpa only [D, spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq, hH.sqrt_spectrum] using hT
  · have he : e T = holomorphicEval A R.domain R.f := e.apply_symm_apply _
    rw [← he]
    change e (CFC.sqrt H) * e T = e _ * e (CFC.sqrt H)
    rw [← map_mul, ← map_mul, mul_assoc (CFC.sqrt H * T),
      Ring.inverse_mul_cancel _ hH.sqrt_similarity.1, mul_one]

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
