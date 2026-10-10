import OAI.Geometry.RCD.Metric.HoleFamilyCharge
import OAI.Geometry.RCD.Metric.ScaledHoleVolumeCover

namespace OAI

/-! # The volume omitted by the compact good-set image -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The finite hole cover and actual RCD source-ball masses give the
image-volume estimate. All coordinate hypotheses are local and explicit. -/
theorem NoncollapsedRCD.image_hole_volume_at_radius_le {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X} {R C ρ : ℝ}
    (hρ : 0 < ρ) (hR : ρ ≤ R) (hC : 1 ≤ C) (hcurv : -1 ≤ K*(2*R)^2)
    {u : X → Euclidean n} {U Ω : Set X} (himage : IsClosed (u '' U))
    (hpoint : ∃ q ∈ ball (0 : Euclidean n) ρ, q ∈ u '' U)
    (hfin : hausdorff n X (Ω \ U) ≠ ⊤)
    (hnear : ∀ z ∈ U, u z ∈ ball 0 ρ → dist z p+4*ρ ≤ R)
    (happ : ∀ z ∈ U, ∀ r : ℝ, 0 < r → r < ρ →
      IsPointedApproximation z 0 (64*r) (1/16) (1/128)
        (fun x => (64*r)⁻¹ • (u x-u z)))
    (hroom : ∀ z ∈ U, u z ∈ ball 0 ρ → ∀ x, dist x z ≤ 4*ρ → ball x (ρ/(4*C)) ⊆ Ω)
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (u x) (u y) ≤ C*dist x y) :
    volume.real (ball (0 : Euclidean n) ρ \ u '' U) ≤
      (2*5^n*volume.real (ball (0 : Euclidean n) 1))*
        (((4*C)^n*(Real.cosh 1^(n-1)*2^n)*R^n/(hausdorff n X).real (ball p R))*
          (hausdorff n X).real (Ω \ U)) := by
  let A := ball (0 : Euclidean n) ρ \ u '' U
  have hA : IsOpen A := isOpen_ball.sdiff himage
  have hproper : ∃ q ∈ ball (0 : Euclidean n) ρ, q ∉ A := by
    obtain ⟨q,hq,hqU⟩ := hpoint
    exact ⟨q,hq,fun hh => hh.2 hqU⟩
  obtain ⟨ι,hι,c,r,hdata,hdisj,hvol⟩ := hole_ball_volume_cover_at_radius (by omega : 0 < n)
    hA sdiff_subset hproper (show (1:ℝ)≤1 by rfl)
  let := hι
  have hcontact (i : ι) : ∃ z ∈ U, u z ∈ ball 0 ρ ∧ dist (u z) (c i)=r i := by
    obtain ⟨q,hqs,hqf⟩ := (hdata i).2.2.2.2
    have hqb : q ∈ ball (0 : Euclidean n) ρ :=
      (hdata i).2.2.2.1 (sphere_subset_closedBall hqs)
    have hqimage : q ∈ u '' U := by
      by_contra hqnot
      have hqA : q ∈ A := ⟨hqb,hqnot⟩
      exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hA) hqf hqA
    obtain ⟨z,hz,rfl⟩ := hqimage
    exact ⟨z,hz,hqb,hqs⟩
  choose z hz hinner htouch using hcontact
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hsum := hX.hole_family_charge hn (lt_of_lt_of_le hρ hR) hCpos hcurv hfin
    (fun i => (hdata i).1) htouch
    (fun i => happ (z i) (hz i) (r i) (hdata i).1 (hdata i).2.1)
    (fun i x hx => (ball_subset_ball (div_le_div_of_nonneg_right
      (hdata i).2.1.le (by positivity))).trans
        (hroom (z i) (hz i) (hinner i) x (by linarith only [hx,(hdata i).2.1])))
    hlip
    (fun i => Set.disjoint_left.mpr (fun y hy hyU => ((hdata i).2.2.1 hy).2 hyU))
    (by simpa only [one_mul] using hdisj)
    (fun i => by linarith only [hnear (z i) (hz i) (hinner i),(hdata i).2.1])
    (fun i => by
      have hc : 1 ≤ 4*C := by linarith
      exact (div_le_self (hdata i).1.le hc).trans ((hdata i).2.1.le.trans hR))
  have hv' : volume.real A ≤ (2*5^n*volume.real (ball (0 : Euclidean n) 1))*∑ i, r i^n := by
    simpa only [mul_one] using hvol
  exact hv'.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

end RegularPointCoordinates

end

end OAI
