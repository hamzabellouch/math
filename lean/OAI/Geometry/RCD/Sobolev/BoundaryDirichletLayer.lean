import OAI.Geometry.RCD.Sobolev.BoundaryDirichletLocal
import OAI.Geometry.RCD.Metric.FiniteCoverIntegral
import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # Uniform squared-scale control on the whole boundary layer

The net consists of actual shell points. Volume comparison bounds the
overlap of its enlarged balls independently of the thickness and scale.
-/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.boundary_dirichlet_layer {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : X) (r S R δ ε : ℝ),
      0<r → 0<δ → 4*δ≤R → R+2*δ≤S → 0≤ε → ε≤δ/8 →
      ∀ V : X → Euclidean n, IsPointedApproximation p 0 r S ε V →
      -1≤K*(S*r)^2 →
      ∀ w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p (R*r)),
      (∫ z in closedBall p (R*r) \ ball p ((R-δ)*r),
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val z)^2 ∂hausdorff n X)≤
        C*δ^2*r^2*energyForm (hausdorff n X) hX.quadratic w.val w.val := by
  classical
  obtain ⟨C,hC,hlocal⟩ := hX.boundary_dirichlet_local hn (by norm_num : (0:ℝ)≤1)
  obtain ⟨N,hN⟩ := hX.rescaled_separated_card hn (by norm_num : (0:ℝ)<40)
  refine ⟨C*(N+1),by positivity,?_⟩
  intro p r S R δ ε hr hδ hR hS hε hεδ V hV hcurv w
  have hS0 : 0≤S := by linarith
  have hcurvsmall (t : ℝ) (ht : 0≤t) (htS : t≤S*r) : -1≤K*t^2 := by
    by_cases hK : 0≤K
    · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg _))
    · have hh := mul_le_mul_of_nonpos_left ((sq_le_sq₀ ht (mul_nonneg hS0 hr.le)).mpr htS)
        (le_of_not_ge hK)
      linarith
  have hcδ := hcurvsmall (δ*r) (by positivity)
    (mul_le_mul_of_nonneg_right (by linarith : δ≤S) hr.le)
  have hc₅ := hcurvsmall (5*δ*r) (by positivity)
    (mul_le_mul_of_nonneg_right (by linarith : 5*δ≤S) hr.le)
  let μ := hausdorff n X
  let A := closedBall p (R*r) \ ball p ((R-δ)*r)
  let ρ : ℝ≥0 := ⟨δ*r,by positivity⟩
  let s := maximalPatchNet ρ A
  let u := SobolevSpace.toLp μ hX.quadratic w.val
  let G := SobolevSpace.minimalSlope μ hX.quadratic w.val
  have hs : (s:Set X)⊆A := maximalPatchNet_subset _ _
  have hsep : (s:Set X).Pairwise (fun x y => δ*r≤dist x y) :=
    fun x hx y hy hxy => (maximalPatchNet_separated ρ A hx hy hxy).le
  have hcover : A⊆⋃q∈s,ball q (5*δ*r) := by
    intro x hx
    obtain ⟨q,hq,hxq⟩ := maximalPatchNet_covers_bounded
      (show ρ≠0 from ne_of_gt (show (0:ℝ≥0)<ρ from (by change 0<δ*r; positivity)))
      (isBounded_closedBall.subset sdiff_subset) x hx
    exact mem_iUnion₂.mpr ⟨q,hq,hxq.trans_lt (by change δ*r<5*δ*r; nlinarith [mul_pos hδ hr])⟩
  have hoverlap (x : X) : (s.filter (fun q => x∈ball q (40*δ*r))).card≤N+1 := by
    have hnear (q : X) (hq : q∈s.filter (fun q => x∈ball q (40*δ*r))) :
        dist q x≤40*(δ*r) := by
      have hh := (Finset.mem_filter.mp hq).2
      rw [mem_ball,dist_comm] at hh
      nlinarith
    exact (hN x (δ*r) (mul_pos hδ hr) hcδ _
      (hsep.mono (by intro q hq; exact (Finset.mem_filter.mp hq).1)) hnear).trans (Nat.le_succ N)
  have hbound (q : X) (hq : q∈s) :
      (∫ z in ball q (5*δ*r), u z^2 ∂μ)≤
        C*δ^2*r^2*(∫ z in ball q (40*δ*r), G z^2 ∂μ) := by
    have hqA := hs hq
    have hq₀ : (R-δ)*r≤dist q p := by
      simpa only [mem_ball,not_lt] using hqA.2
    have hq₁ : dist q p≤R*r := hqA.1
    have hh := hlocal p q r S R δ ε hr hδ hR hS hε hεδ V hV hq₀ hq₁ hc₅ w
    have heq : (∫ z in ball q (40*δ*r), localGamma μ hX.quadratic w.val w.val z ∂μ)=
        ∫ z in ball q (40*δ*r), G z^2 ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (localGamma_self μ hX.quadratic w.val))
    rwa [heq] at hh
  have hu : Integrable (fun z => u z^2) μ := (Lp.memLp u).integrable_sq
  have hG : Integrable (fun z => G z^2) μ := (Lp.memLp G).integrable_sq
  have he : (∫ z, G z^2 ∂μ)=energyForm μ hX.quadratic w.val w.val := by
    rw [lp_integral_square_eq_norm_square]
    exact (SobolevSpace.minimalSlope_norm_sq μ hX.quadratic w.val).trans
      (energyForm_self μ hX.quadratic w.val).symm
  calc
    _ ≤ ∑ q∈s, ∫ z in ball q (5*δ*r), u z^2 ∂μ :=
      integral_le_sum_cover μ s _ (fun _ _ => measurableSet_ball)
        (measurableSet_closedBall.diff measurableSet_ball) hcover hu (fun z => sq_nonneg _)
    _ ≤ ∑ q∈s, C*δ^2*r^2*(∫ z in ball q (40*δ*r), G z^2 ∂μ) := Finset.sum_le_sum hbound
    _ = C*δ^2*r^2*∑ q∈s, ∫ z in ball q (40*δ*r), G z^2 ∂μ := (Finset.mul_sum s _ _).symm
    _ ≤ C*δ^2*r^2*((N+1)*∫ z, G z^2 ∂μ) :=
      mul_le_mul_of_nonneg_left
        (sum_integral_le_overlap μ s _ (fun _ _ => measurableSet_ball) (N+1) hoverlap
          hG (fun z => sq_nonneg _) |>.trans_eq (by push_cast; rfl)) (by positivity)
    _ = _ := by rw [he]; ring

end RegularPointCoordinates

end

end OAI
