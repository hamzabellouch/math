import OAI.Geometry.IsometricImmersion.Estimates.BoundedClassQLow
import OAI.Geometry.IsometricImmersion.Pulses.PulseFlowDistance
import OAI.Geometry.IsometricImmersion.Calculus.ClosedSquareJetBounds

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

def boundedClassQuotientBudget (G d : ℝ) (M : ℕ) : ℝ :=
  heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ))

def boundedClassSlabRadius (G d kappa q0 : ℝ) (M : ℕ) : ℝ :=
  1 / (100 * boundedClassWidth kappa M * (1 + boundedClassQuotientBudget G d M) *
    (1 + (1 + |q0|) * boundedClassWidth kappa M))

theorem boundedClassQuotientBudget_nonneg {G d : ℝ} {M : ℕ}
    (hG : 0 ≤ G) (hd : 0 < d) (hM : 0 < M) : 0 ≤ boundedClassQuotientBudget G d M :=
  heightQuotientJetBound_nonneg hG (Nat.cast_nonneg M) hd
    (one_div_pos.mpr (Nat.cast_pos.mpr hM))

theorem boundedClassSlabRadius_pos {G d : ℝ} (kappa q0 : ℝ) {M : ℕ}
    (hG : 0 ≤ G) (hd : 0 < d) (hM : 0 < M) : 0 < boundedClassSlabRadius G d kappa q0 M := by
  have hL := boundedClassWidth_pos kappa M
  have hQ := boundedClassQuotientBudget_nonneg hG hd hM
  unfold boundedClassSlabRadius
  positivity

theorem bounded_class_quotient_change_from_origin
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun r => g r i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    {p : Coord} (hp : p ∈ modelSquare) :
    |hessianQuotient g z p - hessianQuotient g z 0| ≤
      boundedClassQuotientBudget G d M * (|p 0| + |p 1|) := by
  obtain ⟨hM, hadm, hjet, hHb, _⟩ := h
  obtain ⟨U, hU, hSU, hg, hz, _, _, _, _⟩ := hadm
  have hgCoord : ∀ i j, CoordinateBound (fun p => g p i j) modelSquare 4 G := by
    intro i j ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU ds (hSU hp)).trans
      (hgB i j ds.length hds p hp)
  have hzCoord : CoordinateBound z modelSquare 5 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  obtain ⟨V, hV, hSV, _, _, hqV, hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG (Nat.cast_nonneg M) hd
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hgCoord hzCoord hdet (fun p hp => (hHb p hp).1)
  apply quotient_change_from_origin hqV hV hSV (boundedClassQuotientBudget_nonneg hG hd hM) ?_ hp
  intro p hp i
  exact hqB [i] (by norm_num) p hp

theorem inverseShear_coordinate_sum_le {q0 L r : ℝ} {p : Coord}
    (_hr : 0 ≤ r) (hx : |p 0| ≤ L * r) (hy : |p 1| ≤ r) :
    |inverseShearCoordinates q0 p 0| + |inverseShearCoordinates q0 p 1| ≤
      r * (1 + (1 + |q0|) * L) := by
  change |p 0| + |p 1 - q0 * p 0| ≤ _
  calc
    _ ≤ |p 0| + (|p 1| + |q0 * p 0|) := add_le_add le_rfl (abs_sub _ _)
    _ ≤ L * r + (r + |q0| * (L * r)) := by
      rw [abs_mul]
      exact add_le_add hx (add_le_add hy (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
    _ = _ := by ring

theorem bounded_class_slab_quotient_small
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    {G d kappa q0 r : ℝ} (hG : 0 ≤ G) (hd : 0 < d) (hr : 0 ≤ r)
    (hrsmall : r ≤ boundedClassSlabRadius G d kappa q0 M)
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => g a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hcenter : |hessianQuotient g z 0 - q0| ≤ 1 / (100 * boundedClassWidth kappa M))
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ modelSquare)
    (hx : |p 0| ≤ boundedClassWidth kappa M * r) (hy : |p 1| ≤ r) :
    |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M) := by
  let L := boundedClassWidth kappa M
  let Q := boundedClassQuotientBudget G d M
  let D := 1 + (1 + |q0|) * L
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hQ : 0 ≤ Q := boundedClassQuotientBudget_nonneg hG hd h.1
  have hD : 0 < D := by dsimp [D]; positivity
  have hbudget : Q * (r * D) ≤ 1 / (100 * L) := by
    calc
      _ ≤ (1 + Q) * (r * D) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hr hD.le)
      _ ≤ (1 + Q) * (boundedClassSlabRadius G d kappa q0 M * D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrsmall hD.le) (by positivity)
      _ = _ := by
        change (1 + Q) * (1 / (100 * L * (1 + Q) * D) * D) = 1 / (100 * L)
        field_simp [hL.ne', hD.ne', ne_of_gt (show 0 < 1 + Q by positivity)]
  have hchange := bounded_class_quotient_change_from_origin h hG hd hgB hdet hp
  have hdist := inverseShear_coordinate_sum_le (q0 := q0) hr hx hy
  have hchange' : |hessianQuotient g z (inverseShearCoordinates q0 p) - hessianQuotient g z 0| ≤
      1 / (100 * L) := hchange.trans ((mul_le_mul_of_nonneg_left hdist hQ).trans hbudget)
  calc
    _ ≤ |hessianQuotient g z (inverseShearCoordinates q0 p) - hessianQuotient g z 0| +
        |hessianQuotient g z 0 - q0| := abs_sub_le _ _ _
    _ ≤ 1 / (100 * L) + 1 / (100 * L) := add_le_add hchange' hcenter
    _ ≤ 1 / (10 * L) := by
      have hInv : 0 < 1 / L := one_div_pos.mpr hL
      calc
        _ = (1 / 50 : ℝ) * (1 / L) := by
          field_simp [hL.ne']
          ring
        _ ≤ (1 / 10 : ℝ) * (1 / L) :=
          mul_le_mul_of_nonneg_right (by norm_num) hInv.le
        _ = _ := by field_simp [hL.ne']

theorem exists_bounded_class_slab_QLowBounds
    (G R kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) :
    ∃ MQ : ℝ, 0 ≤ MQ ∧ ∀ (g : MetricField) (z : Coord → ℝ) (S : Set Coord) (r : ℝ),
      BoundedAdmissibleHeight g M z → 0 ≤ r → r ≤ boundedClassSlabRadius G d kappa q0 M →
      (∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, |p 0| ≤ boundedClassWidth kappa M * r ∧ |p 1| ≤ r) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => g a i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
      (∀ p ∈ S, gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2) →
      |hessianQuotient g z 0 - q0| ≤ 1 / (100 * boundedClassWidth kappa M) →
      QLowBounds (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) S
        (shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)) MQ (boundedClassWidth kappa M / 4) := by
  obtain ⟨MQ, hMQ, hlow⟩ := exists_bounded_class_sheared_QLowBounds G R kappa d q0 M hG hR hkappa hd hM
  refine ⟨MQ, hMQ, ?_⟩
  intro g z S r hclass hr hrsmall hSp hcoords haxes hgB hdet hK hcenter
  exact hlow g z S hclass hSp hcoords
    (fun i j k hk p hp => hgB i j k hk _ (hSp p hp))
    (fun p hp => hdet _ (hSp p hp)) hK
    (fun p hp => bounded_class_slab_quotient_small hclass hG hd hr hrsmall hgB hdet hcenter
      (hSp p hp) (haxes p hp).1 (haxes p hp).2)

end SmoothLocal.Perturbation

end

end OAI
