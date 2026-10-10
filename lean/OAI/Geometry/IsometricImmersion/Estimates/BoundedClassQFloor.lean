import OAI.Geometry.IsometricImmersion.Darboux.QPositiveFloor
import OAI.Geometry.IsometricImmersion.Estimates.BoundedClassHyperbolicity

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem bounded_class_Q5_floor {g : MetricField} {z : Coord → ℝ}
    {M : ℕ} (h : BoundedAdmissibleHeight g M z) {kappa q0 G d : ℝ}
    (hkappa : 0 < kappa) (hG : 0 ≤ G) (hd : 0 < d) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ modelSquare)
    (hgB : ∀ i j k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun r => g r i j) (inverseShearCoordinates q0 p)‖ ≤ G)
    (hdet : d ≤ |(g (inverseShearCoordinates q0 p)).det|)
    (hK : gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M)) :
    shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ) ≤
      heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p := by
  have hclass := h
  obtain ⟨hM, hadm, hjet, hHb, _⟩ := h
  obtain ⟨U, hU, hSU, hg, hz, hD, _, _, _⟩ := hadm
  have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  obtain ⟨_, hxxfloor, hS, _⟩ := bounded_class_shear_estimates hclass hkappa hp hK hq
  have hxx : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    intro he
    rw [he, abs_zero] at hxxfloor
    exact (not_le_of_gt (boundedClassShearHxxFloor_pos hkappa hM)) hxxfloor
  apply actual_sheared_Q5_floor hg hU hz q0 (hSU hp) hG hMp.le hd hMp
    ?_ ?_ ?_ ?_ hdet (hHb _ hp).1 (hD _ hp) hxx hS
  · intro i j
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hgB i j 0 (by omega)
  · intro a i j
    exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU [a] (hSU hp)).trans
      (hgB i j 1 (by omega))
  · intro i
    exact (norm_iteratedCoordPartial_le_jet hz hU [i] (hSU hp)).trans
      (hjet 1 (by omega) _ hp)
  · intro i j
    exact (norm_iteratedCoordPartial_le_jet hz hU [i, j] (hSU hp)).trans
      (hjet 2 (by omega) _ hp)

theorem bounded_class_Q_principal_budgets {g : MetricField} {z : Coord → ℝ}
    {M : ℕ} (h : BoundedAdmissibleHeight g M z) {kappa q0 G d : ℝ}
    (hkappa : 0 < kappa) (hG : 0 ≤ G) (hd : 0 < d) {S : Set Coord}
    (hS : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare)
    (hgB : ∀ i j k, k ≤ 1 → ∀ p ∈ S,
      ‖iteratedFDeriv ℝ k (fun r => g r i j) (inverseShearCoordinates q0 p)‖ ≤ G)
    (hdet : ∀ p ∈ S, d ≤ |(g (inverseShearCoordinates q0 p)).det|)
    (hK : ∀ p ∈ S, gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : ∀ p ∈ S, |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M)) :
    0 < shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ) ∧
    ∀ p ∈ S,
      (boundedClassSpeed kappa M)^2 / (2 * (M : ℝ)) ≤
        |covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0| ∧
      shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ) ≤
        heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p ∧
      |heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 4 p| +
        Real.sqrt (heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p) ≤
          boundedClassWidth kappa M / 4 := by
  refine ⟨shearedQPositiveFloor_pos q0 hG (Nat.cast_nonneg M) hd (Nat.cast_pos.mpr h.1), ?_⟩
  intro p hp
  obtain ⟨_, hxx, _, hchar⟩ := bounded_class_shear_estimates h hkappa (hS p hp) (hK p hp) (hq p hp)
  exact ⟨hxx, bounded_class_Q5_floor h hkappa hG hd (hS p hp)
    (fun i j k hk => hgB i j k hk p hp) (hdet p hp) (hK p hp) (hq p hp), hchar.le⟩

end SmoothLocal.Perturbation

end

end OAI
