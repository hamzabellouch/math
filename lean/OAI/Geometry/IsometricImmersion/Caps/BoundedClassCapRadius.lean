import OAI.Geometry.IsometricImmersion.Coordinates.BoundedClassSlabSmallness

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem bounded_class_slab_quotient_small_of_cap_radius
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    {G d kappa q0 r : ℝ} (hG : 0 ≤ G) (hd : 0 < d) (hr : 0 ≤ r)
    (hq0 : |q0| ≤ 1 / 20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
      (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤ 9 / (100 * boundedClassWidth kappa M))
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
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hQ : 0 ≤ Q := boundedClassQuotientBudget_nonneg hG hd h.1
  have hLr : 0 ≤ L * r := mul_nonneg hL.le hr
  have hdist := inverseShear_coordinate_sum_le (q0 := q0) hr hx hy
  have hdist' : |inverseShearCoordinates q0 p 0| + |inverseShearCoordinates q0 p 1| ≤
      r + 107 * (L * r) / 100 := by
    apply hdist.trans
    have hh := mul_le_mul_of_nonneg_right hq0 hLr
    nlinarith
  have hchange := bounded_class_quotient_change_from_origin h hG hd hgB hdet hp
  have hchange' : |hessianQuotient g z (inverseShearCoordinates q0 p) - hessianQuotient g z 0| ≤
      9 / (100 * L) := hchange.trans ((mul_le_mul_of_nonneg_left hdist' hQ).trans hrsmall)
  calc
    _ ≤ |hessianQuotient g z (inverseShearCoordinates q0 p) - hessianQuotient g z 0| +
        |hessianQuotient g z 0 - q0| := abs_sub_le _ _ _
    _ ≤ 9 / (100 * L) + 1 / (100 * L) := add_le_add hchange' hcenter
    _ = _ := by
      change 9 / (100 * L) + 1 / (100 * L) = 1 / (10 * L)
      field_simp [hL.ne']
      ring

theorem exists_bounded_class_cap_radius_QLowBounds
    (G R kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) (hq0 : |q0| ≤ 1 / 20) :
    ∃ MQ : ℝ, 0 ≤ MQ ∧ ∀ (g : MetricField) (z : Coord → ℝ) (S : Set Coord) (r : ℝ),
      BoundedAdmissibleHeight g M z → 0 ≤ r →
      heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
        (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤
          9 / (100 * boundedClassWidth kappa M) →
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
    (fun p hp => bounded_class_slab_quotient_small_of_cap_radius hclass hG hd hr hq0 hrsmall
      hgB hdet hcenter (hSp p hp) (haxes p hp).1 (haxes p hp).2)

end SmoothLocal.Perturbation

end

end OAI
