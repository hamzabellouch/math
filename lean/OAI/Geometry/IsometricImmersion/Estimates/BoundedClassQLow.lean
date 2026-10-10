import OAI.Geometry.IsometricImmersion.Estimates.BoundedClassQFloor
import OAI.Geometry.IsometricImmersion.Calculus.ShearMetricJets
import OAI.Geometry.IsometricImmersion.Darboux.QLowActualBounds

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem exists_bounded_class_sheared_QLowBounds
    (G R kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) :
    ∃ MQ : ℝ, 0 ≤ MQ ∧ ∀ (g : MetricField) (z : Coord → ℝ) (S : Set Coord),
      BoundedAdmissibleHeight g M z →
      (∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ S,
        ‖iteratedFDeriv ℝ k (fun r => g r i j) (inverseShearCoordinates q0 p)‖ ≤ G) →
      (∀ p ∈ S, d ≤ |(g (inverseShearCoordinates q0 p)).det|) →
      (∀ p ∈ S, gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2) →
      (∀ p ∈ S, |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
        1 / (10 * boundedClassWidth kappa M)) →
      QLowBounds (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) S
        (shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)) MQ (boundedClassWidth kappa M / 4) := by
  let GS := shearedMetricCoordinateBudget G q0 4
  let ZS := (2 * (1 + |q0|))^3 * (M : ℝ)
  let c := (boundedClassSpeed kappa M)^2 / (2 * (M : ℝ))
  have hGS : 0 ≤ GS := shearedMetricCoordinateBudget_nonneg q0 4 hG
  have hc : 0 < c := boundedClassShearHxxFloor_pos hkappa hM
  obtain ⟨MQ, hMQ, hlow⟩ := exists_actual_QLowBounds GS R ZS hGS hR hd hc
  refine ⟨MQ, hMQ, ?_⟩
  intro g z S hclass hSp hcoords hgB hdet hK hq
  have hclass0 := hclass
  obtain ⟨_, hadm, hjet, _, _⟩ := hclass
  obtain ⟨U, hU, hSU, hg, hz, _, _, _, _⟩ := hadm
  let T : Set Coord := inverseShearCoordinates q0 '' S
  let V : Set Coord := inverseShearCoordinates q0 ⁻¹' U
  have hTU : T ⊆ U := by
    rintro p ⟨r, hr, rfl⟩
    exact hSU (hSp r hr)
  have hSV : S ⊆ V := fun p hp => hSU (hSp p hp)
  have hgCoord : ∀ i j, CoordinateBound (fun p => g p i j) T 4 G := by
    intro i j ds hds p hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU ds (hSU (hSp r hr))).trans
      (hgB i j ds.length hds r hr)
  have hgShear := metric_coordinate_bound_inverse_shear hg hU hTU hG hgCoord q0
  have hgS : ∀ i j, CoordinateBound (fun p => metricInShearCoordinates g q0 p i j) S 4 GS := by
    intro i j ds hds p hp
    exact hgShear i j ds hds p ⟨p, hp, rfl⟩
  have hzCoord : CoordinateBound z modelSquare 3 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  have hzShear := SmoothLocal.Pulse.CoordinateBound.inverse_shear hzCoord hz hU hSU (Nat.cast_nonneg M) q0
  have hzS : CoordinateBound (heightInShearCoordinates z q0) S 3 ZS := by
    intro ds hds p hp
    exact hzShear ds hds p (hSp p hp)
  have hgSmooth := metricInShearCoordinates_smoothPositive hg q0
  have hVS : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hzSmooth := heightInShearCoordinates_contDiffOn hz q0
  obtain ⟨_, hprincipal⟩ := bounded_class_Q_principal_budgets hclass0 hkappa hG hd hSp
    (fun i j k hk => hgB i j k (by omega)) hdet hK hq
  exact hlow (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) V S
    hgSmooth hVS hzSmooth hSV hcoords hgS hzS
    (fun p hp => by simpa only [metricDet_in_shear_coordinates] using hdet p hp)
    (fun p hp => (hprincipal p hp).1)
    (shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)) (boundedClassWidth kappa M / 4)
    (fun p hp => (hprincipal p hp).2.1) (fun p hp => (hprincipal p hp).2.2)

end SmoothLocal.Perturbation

end

end OAI
