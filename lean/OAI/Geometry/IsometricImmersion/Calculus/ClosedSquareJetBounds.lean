import OAI.Geometry.IsometricImmersion.Calculus.HessianJetBounds
import OAI.Geometry.IsometricImmersion.Obstructions.PatchAdmissibility
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Interval.Set.Pi

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

theorem modelSquare_closure_interior : closure (interior modelSquare) = modelSquare := by
  unfold modelSquare
  rw [← Set.pi_univ_Icc, interior_pi_set (Set.finite_univ : (Set.univ : Set (Fin 2)).Finite)]
  simp only [interior_Icc, closure_pi_set,
    closure_Ioo (by norm_num : (-3 : ℝ) ≠ 3), Set.pi_univ_Icc]

theorem CoordinateBound.restrict_domain {f : Coord → ℝ} {S T : Set Coord} {n : ℕ} {M : ℝ}
    (hf : CoordinateBound f S n M) (hTS : T ⊆ S) : CoordinateBound f T n M :=
  fun ds hds p hp => hf ds hds p (hTS hp)

theorem CoordinateBound.of_modelSquare_interior {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hB : CoordinateBound f (interior modelSquare) n M) : CoordinateBound f modelSquare n M := by
  intro ds hds p hp
  have hcont : ContinuousOn (fun x => |iteratedCoordPartial ds f x|) modelSquare :=
    ((LowQuotient.iterated_contDiffOn hf hU ds).continuousOn.mono hSU).abs
  have hcl : p ∈ closure (interior modelSquare) := by rw [modelSquare_closure_interior]; exact hp
  apply le_on_closure (fun x hx => hB ds hds x hx) _ continuousOn_const hcl
  rw [modelSquare_closure_interior]
  exact hcont

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem inverseMetric_coordinate_bound_closed_square
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 3 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => inverseMetric g p i j) modelSquare 3 (metricInverseJetBound G d) := by
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun a b => (hg.1 a b).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hBI := inverseMetric_coordinate_bound hgI isOpen_interior hG hd
    (fun a b => (hgB a b).restrict_domain interior_subset)
    (fun p hp => hdet p (interior_subset hp)) i j
  exact CoordinateBound.of_modelSquare_interior (inverseMetric_contDiffOn hg i j) hU hSU hBI

theorem covHessian_coordinate_bound_closed_square
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => covHessian g z p i j) modelSquare 3 (hessianJetBound G Z d) := by
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun a b => (hg.1 a b).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hBI := covHessian_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ hd
    (fun a b => (hgB a b).restrict_domain interior_subset) (hzB.restrict_domain interior_subset)
    (fun p hp => hdet p (interior_subset hp)) i j
  exact CoordinateBound.of_modelSquare_interior (covHessian_contDiffOn hg hU hz i j) hU hSU hBI

theorem exists_open_quotient_domain_with_closed_low_bounds
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      ContDiffOn ℝ ∞ (hessianQuotient g z) V ∧
      CoordinateBound (hessianQuotient g z) modelSquare 3
        (LowQuotient.boundThroughThree (hessianJetBound G Z d) c) := by
  obtain ⟨V, hV, hSV, hVU, hVne, hqV⟩ := exists_open_hessianQuotient_domain hg hU hz hSU
    (LowQuotient.denominator_ne_zero hc hyy)
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun a b => (hg.1 a b).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hBI := (hessianQuotient_bound_from_metric_height_jets hgI isOpen_interior (hz.mono hIU)
    hG hZ hd hc (fun a b => (hgB a b).restrict_domain interior_subset)
    (hzB.restrict_domain interior_subset) (fun p hp => hdet p (interior_subset hp))
    (fun p hp => hyy p (interior_subset hp))).2
  exact ⟨V, hV, hSV, hVU, hVne, hqV,
    CoordinateBound.of_modelSquare_interior hqV hV hSV hBI⟩

end SmoothLocal.Geometry

end

end OAI
