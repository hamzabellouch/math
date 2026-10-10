import OAI.Geometry.RuledCovering.NilpotentLattice

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Convert the finite weighted lattice certificate into actual perpendicular Euclidean cylinders.
The factor is the exact area inflation caused by the derivative remainder. -/
theorem framed_local_cover_of_shape (M : Coordinates ≃L[ℝ] Plane) {h L R delta : ℝ}
    (shape : Cylinder → Prop)
    (hshape : ∀ b : Coordinates, ∀ a : ℝ, 0 < a → ∀ g : Plane,
      shape (projectedCylinder h g (M '' closedBall b a)))
    (hh : 0 < h) (hL : 0 ≤ L) (hR : 0 ≤ R) (hd : 0 ≤ delta)
    {K U : Set Coordinates} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (v : Plane → Plane) (A : Coordinates →L[ℝ] Coordinates)
    (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖M.symm (v (M p)) - M.symm (v (M b)) - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Coordinates → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    (hFval : ∀ p ∈ U, F p = physicalWeight h (v (M p)))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h (M '' K) v L)
      (h * (1 + 2 * L * delta * R) ^ 2 *
        (∫ p in M '' K, physicalWeight h (v p)) + eps) := by
  classical
  let B : ℝ := (1 + 2 * L * delta * R) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hscale : 0 < h * frameJacobian M * B := mul_pos (mul_pos hh (frameJacobian_pos M)) hB
  obtain ⟨n, hn, S, hS, hSU, hcov, hcost⟩ := local_finite_certificate hK hU hKU
    (fun p => M.symm (v (M p))) A hL hd hmodel hrem hF hFpos (div_pos heps hscale)
  let : Fintype S := hS.fintype
  let a : ℝ := (1 / 2 + L * delta * R) / n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; positivity
  let C : S → Cylinder := fun b => projectedCylinder h (v (M b)) (M '' closedBall (b : Coordinates) a)
  have harea (b : S) : (C b).area = h * frameJacobian M * (2 * a) ^ 2 * F b := by
    dsimp only [C]
    rw [projectedCylinder_area hh, frame_volume_image M isClosed_closedBall.measurableSet,
      coordinates_closedBall_volume b ha.le, hFval b (hSU b.property)]
    ring
  have hBrel : (2 * a) ^ 2 = B / (n : ℝ) ^ 2 := by
    dsimp [a, B]
    ring
  have hintegral : (∫ p in M '' K, physicalWeight h (v p)) =
      frameJacobian M * ∫ x in K, F x := by
    rw [frame_integral_image M hK.measurableSet]
    congr 1
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    exact (hFval x (hKU hx)).symm
  apply HasFiniteCover.of_fintype C
  · intro b
    exact hshape b a ha (v (M b))
  · rintro x ⟨_, ⟨p, hp, rfl⟩, s, hs, rfl⟩
    obtain ⟨b, hb, hc⟩ := hcov p hp s hs
    apply mem_iUnion.mpr
    refine ⟨⟨b, hb⟩, ?_⟩
    apply physicalRuled_mem_projectedCylinder
    refine ⟨p + s • (M.symm (v (M p)) - M.symm (v (M b))), ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      convert hc using 1
      congr 1
      module
    · simp
  · have hsum : (∑ b : S, (C b).area) =
        (h * frameJacobian M * B) * ((∑' b : S, F b) / (n : ℝ) ^ 2) := by
      simp_rw [harea, hBrel]
      rw [tsum_fintype, ← Finset.mul_sum]
      ring
    rw [hsum, hintegral]
    have hc := (mul_lt_mul_of_pos_left hcost hscale).le
    calc
      _ ≤ (h * frameJacobian M * B) *
          ((∫ x in K, F x) + eps / (h * frameJacobian M * B)) := hc
      _ = _ := by
        rw [mul_add, mul_div_cancel₀ _ hscale.ne']
        dsimp [B]
        ring


/-- Every square-zero label has a patch whose compact subsets admit finite covers,
with one prescribed arbitrarily small area inflation. -/
theorem nilpotent_local_patch {h B : ℝ} (hh : 0 < h) (hB : 1 < B)
    {v : Plane → Plane} {U : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : Plane} (hp : p ∈ U) (hnil : (fderiv ℝ v p).comp (fderiv ℝ v p) = 0) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ K : Set Plane, IsCompact K → K ⊆ V →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover (squareProjected h) (physicalRuled h K v 1)
        (h * B * (∫ q in K, physicalWeight h (v q)) + eps) := by
  obtain ⟨Q, d, hQ⟩ := nilpotent_frame (fderiv ℝ v p) hnil
  let M := orthogonalFrame Q
  have hM (z : Coordinates) : M.symm ((fderiv ℝ v p) (M z)) = ![d*z 1,0] := by
    have hz := congrArg WithLp.ofLp (hQ (WithLp.toLp 2 z))
    exact hz
  let A : Coordinates →L[ℝ] Coordinates := d • shearCLM
  let R : ℝ := (1+|d|)/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hmodel : LatticeModel A 1 R := nilpotent_lattice_model d
  obtain ⟨delta, hd, hDB⟩ := exists_small_inflation 1 R hB
  let w : Coordinates → Coordinates := fun x => M.symm (v (M x))
  let Uc : Set Coordinates := M ⁻¹' U
  have hUco : IsOpen Uc := hU.preimage M.continuous
  have hpc : M.symm p ∈ Uc := by simpa [Uc]
  have hvc : ContDiffOn ℝ 1 (fun x => v (M x)) Uc :=
    hv.comp M.contDiff.contDiffOn (fun x hx => hx)
  have hwc : ContDiffOn ℝ 1 w Uc := M.symm.contDiff.comp_contDiffOn hvc
  have hvder := (hv.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hwd : fderiv ℝ w (M.symm p) = A := by
    have hvd : HasFDerivAt (fun x => v (M x))
        ((fderiv ℝ v p).comp M.toContinuousLinearMap) (M.symm p) := by
      have hvdp : HasFDerivAt v (fderiv ℝ v p) (M (M.symm p)) := by
        simpa using hvder.hasFDerivAt
      exact hvdp.comp (M.symm p) M.hasFDerivAt
    have hcomp := M.symm.hasFDerivAt.comp (M.symm p) hvd
    change fderiv ℝ (M.symm ∘ (fun x => v (M x))) (M.symm p) = A
    rw [hcomp.fderiv]
    ext z i
    have hz := congrArg (fun a : Coordinates => a i) (hM z)
    fin_cases i <;> simpa [A, shearCLM, shearLinear] using hz
  obtain ⟨r, hr, hrU, hrem⟩ := c1_local_remainder hUco hwc hpc hd
  let Vc := ball (M.symm p) (r / 2)
  have hrhalf : r / 2 < r := by linarith
  have hclU : closedBall (M.symm p) (r / 2) ⊆ Uc :=
    (closedBall_subset_ball hrhalf).trans hrU
  have hclF : ContinuousOn (fun x => physicalWeight h (v (M x)))
      (closedBall (M.symm p) (r / 2)) :=
    (physicalWeight_continuous h).comp_continuousOn (hvc.continuousOn.mono hclU)
  obtain ⟨F, hF, hFnon, hFeq⟩ := continuous_nonneg_extension isClosed_closedBall hclF
    (fun x _ => (physicalWeight_pos h (v (M x))).le)
  refine ⟨M '' Vc, M.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · exact ⟨M.symm p, mem_ball_self (half_pos hr), M.apply_symm_apply p⟩
  · intro K hK hKV eps heps
    let Kc := M.symm '' K
    have hKc : IsCompact Kc := hK.image M.symm.continuous
    have hKcV : Kc ⊆ Vc := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKV hq
      simpa using hx
    have himg : M '' Kc = K := by simp [Kc]
    have hc := framed_local_cover_of_shape M (squareProjected h)
      (fun b a ha g => ⟨_,g,orthogonal_closedBall_square Q b ha,rfl⟩)
      hh (by norm_num : (0:ℝ)≤1) hR.le hd.le hKc isOpen_ball hKcV v A hmodel
      (fun x hx y hy => by
        rw [← hwd]
        exact hrem x (ball_subset_ball hrhalf.le hx) y (ball_subset_ball hrhalf.le hy))
      hF hFnon (fun x hx => hFeq (ball_subset_closedBall hx)) heps
    rw [himg] at hc
    apply hc.mono Subset.rfl
    have hI : 0 ≤ ∫ q in K, physicalWeight h (v q) :=
      integral_nonneg (fun q => (physicalWeight_pos h (v q)).le)
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDB.le hh.le) hI]

/-- Finite square-tile approximation, with unrestricted local shear and arbitrary
compact labels. -/
theorem nilpotent_physical_cover {h : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hnil : ∀ p ∈ D, (fderiv ℝ v p).comp (fderiv ℝ v p) = 0)
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover (squareProjected h) (physicalRuled h D v 1)
      (h * (∫ p in D, physicalWeight h (v p)) + eps) := by
  obtain ⟨U, hU, hDU, hv⟩ := hv
  have hF : IntegrableOn (fun p => physicalWeight h (v p)) D :=
    ((physicalWeight_continuous h).comp_continuousOn (hv.continuousOn.mono hDU)).integrableOn_compact hD
  obtain ⟨B, hB, hbudget⟩ := exists_inflation_budget
    (h * ∫ p in D, physicalWeight h (v p)) (half_pos heps)
  have hc := globalize_local_covers h 1 v (fun p => physicalWeight h (v p)) (h*B) hD hF
    (fun p hp => nilpotent_local_patch hh hB hU hv (hDU hp) (hnil p hp)) (half_pos heps)
  apply hc.mono Subset.rfl
  nlinarith

lemma unitSquare_parallelogram : IsParallelogram unitSquare := by
  have he : unitSquare = (EuclideanSpace.equiv (Fin 2) ℝ).symm ''
      closedBall (0 : Coordinates) (1/2:ℝ) := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.ofLp x, ?_, rfl⟩
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
      exact hx
    · rintro ⟨y,hy,rfl⟩
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)] at hy
      exact hy
  rw [he]
  exact (coordinates_closedBall_parallelogram 0 (by norm_num : (0:ℝ)<1/2)).linear_image
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.injective

lemma IsSquareTile.parallelogram {T : Set Plane} (hT : IsSquareTile T) :
    IsParallelogram T := by
  obtain ⟨c,R,a,ha,rfl⟩ := hT
  have hi : Function.Injective (a • R.toLinearMap) := by
    intro x y hxy
    apply R.injective
    exact (smul_right_injective Plane ha.ne') hxy
  have he : (fun x => c+a • R x) '' unitSquare =
      (fun x => c+x) '' ((a • R.toLinearMap) '' unitSquare) := by
    rw [← image_comp]
    rfl
  rw [he]
  exact (unitSquare_parallelogram.linear_image (a • R.toLinearMap) hi).translate c

end RuledApproximation

end

end OAI
