import OAI.Geometry.IsometricImmersion.Coordinates.ActualPatchQRectangle
import OAI.Geometry.IsometricImmersion.Caps.QPointwiseCauchyJets
import OAI.Geometry.IsometricImmersion.Calculus.ShearMetricJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix NNReal

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_bounded_patch_cauchy_bound
    (G d kappa q0 r C : ℝ) (M : ℕ) (A : ℝ≥0) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hr : 0 < r) (hrhalf : r < 1/2)
    (hC : 0 ≤ C) (hq0 : |q0| ≤ 1/20)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M)) (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa)
      (z : Coord → ℝ) (b : ℝ),
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z → -r ≤ b → b ≤ 0 →
      (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
      |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
      (∀ i j, CoordinateBound (fun p => metricInShearCoordinates (perturbedMetric g0 eta.val) q0 p i j)
        (shrinkingSlab (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r)
          (-r) b (boundedClassWidth kappa M/4)) (max 9 (K+3)) C) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (K+2) → ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r →
        |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ (A : ℝ)) →
      ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
        ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0) b) x‖ ≤ B ∧
        ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0) b) x‖ ≤ B := by
  let L := boundedClassWidth kappa M
  let Zs := (2*(1+|q0|))^8*(M : ℝ)
  let s0 := shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)
  let c0 := (boundedClassSpeed kappa M)^2/(2*(M : ℝ))
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hZs : 0 ≤ Zs := by dsimp [Zs]; positivity
  have hs0 : 0 < s0 := shearedQPositiveFloor_pos q0 hG (Nat.cast_nonneg M) hd (Nat.cast_pos.mpr hM)
  have hc0 : 0 < c0 := boundedClassShearHxxFloor_pos hkappa hM
  obtain ⟨B,hB,hpoint⟩ := exists_finite_actual_Q_cauchy_fullJet_bound
    C 1 Zs s0 (L/4) (-(L*r)) (L*r) r (L*r) A hC (by norm_num) hZs hs0
      (by positivity) hr.le (mul_pos hL hr) (by nlinarith [mul_pos hL hr]) hd hc0 K
  obtain ⟨_,_,hlow⟩ := exists_bounded_patch_actual_slab_QLowBounds
    G kappa d q0 M hG hkappa hd hM hq0
  refine ⟨B,hB,?_⟩
  intro g0 eta z b hclass hab hb hgB hdet hcenter hmetric hcut x hx n hn
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates g q0
  let zs := heightInShearCoordinates z q0
  let S := shrinkingSlab (-(L*r)) (L*r) (-r) b (L/4)
  have hQ := hlow g0 eta z r b hclass hr.le hb hLr hrsmall hgB hdet hcenter
  have haxes (p : Coord) (hp : p ∈ S) := shrinking_class_slab_axis_bounds hr.le hb hp
  have hcentral (p : Coord) (hp : p ∈ S) := actual_patch_curvature_on_class_slab eta hr.le hb hLr hq0 hp
  have hSp (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare :=
    centralBox_subset_modelSquare (hcentral p hp).1
  have hSbox : S ⊆ closedRectangle (-(L*r)) (L*r) (-r) b := by
    intro p hp
    exact ⟨abs_le.mp (haxes p hp).1,hp.1⟩
  obtain ⟨radius,lo,hi,hradius,hlo,hhi,hgs,hzs,hD,hxx⟩ :=
    exists_actual_patch_Q_rectangle eta hclass hG hd hkappa hr hab hb hLr hq0 hrsmall hgB hdet hcenter
  obtain ⟨U,hU,hSU,_,hz,_,_,_,_⟩ := hclass.2.1
  have hZbase : CoordinateBound z modelSquare 8 (M : ℝ) :=
    coordinateBound_of_frechet_bounds hz hU hSU hclass.2.2.1
  have hZshear := SmoothLocal.Pulse.CoordinateBound.inverse_shear
    hZbase hz hU hSU (Nat.cast_nonneg M) q0
  have hzB : CoordinateBound zs S 8 Zs := by
    intro ds hds p hp
    exact hZshear ds hds p (hSp p hp)
  have hdetS (p : Coord) (hp : p ∈ S) : d ≤ |(gs p).det| := by
    rw [metricDet_in_shear_coordinates]
    exact hdet _ (hSp p hp)
  have hdenS (p : Coord) (hp : p ∈ S) : c0 ≤ |covHessian gs zs p 0 0| :=
    (actual_patch_closed_strip_Hxx_floor eta hclass hG hd hkappa hr.le hb hLr hq0 hrsmall
      hgB hdet hcenter (hSbox hp)).2
  have hcoords (p : Coord) (hp : p ∈ S) : |p 0| ≤ 1 ∧ |p 1| ≤ 1 :=
    ⟨(haxes p hp).1.trans (hLr.trans (by norm_num)),
      (haxes p hp).2.trans (by linarith)⟩
  have hbound := hpoint gs zs radius lo hi (-r) b hgs hzs hD hxx
    ((mul_pos hL hr).trans hradius) hab (by linarith)
    (by linarith) hradius ⟨hlo,hab.trans_lt hhi⟩ ⟨hlo.trans_le hab,hhi⟩
    (fun p hp => (hQ p hp).1)
    (fun p hp => (hQ p hp).2.2.2.2.2.2.2) hcoords hmetric hzB hdetS hdenS
    (fun ds hds x hx => hcut ds hds x (abs_le.mpr hx))
    b ⟨hab,le_rfl⟩ x (halfWidth_mem_inward_interval hL hr ⟨hab,hb⟩ hx) n hn
  exact hbound

end SmoothLocal.Perturbation

end

end OAI
