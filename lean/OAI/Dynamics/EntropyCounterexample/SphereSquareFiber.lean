import OAI.Dynamics.EntropyCounterexample.SphereDoubling

namespace OAI

noncomputable section

namespace Problem340.SphereDoubling

theorem sphereMap_eq_east_iff (x : Sphere) :
    sphereMap x = east ↔ x = east ∨ x = west := by
  constructor
  · intro h
    have hz := congrArg (fun y : Sphere => y.val 2) h
    change 2 * x.val 2 / (1 + x.val 2 ^ 2) = 0 at hz
    have hz' : x.val 2 = 0 := by
      rcases (div_eq_zero_iff).mp hz with hnum | hden
      · linarith
      · exact False.elim ((ne_of_gt (denominator_pos x.val)) hden)
    have hx := congrArg (fun y : Sphere => y.val 0) h
    change (x.val 0 ^ 2 - x.val 1 ^ 2) / (1 + x.val 2 ^ 2) = 1 at hx
    rw [hz'] at hx
    norm_num at hx
    have hs := sphere_equation x
    rw [hz'] at hs
    have hy : x.val 1 = 0 := by nlinarith [sq_nonneg (x.val 1)]
    have hx2 : x.val 0 ^ 2 = 1 := by nlinarith
    have hxpm : x.val 0 = 1 ∨ x.val 0 = -1 := by
      have hp : (x.val 0 - 1) * (x.val 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp with hp | hm
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hxpm with hp | hm
    · left
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [east, hp, hy, hz', Matrix.cons_val_two]
    · right
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [west, hm, hy, hz', Matrix.cons_val_two]
  · rintro (rfl | rfl) <;> simp

theorem preimage_east : sphereMap ⁻¹' {east} = {east, west} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
  exact sphereMap_eq_east_iff x

theorem ncard_preimage_east : (sphereMap ⁻¹' {east}).ncard = 2 := by
  rw [preimage_east]
  simp [east_ne_west]

theorem hasFDerivAt_complex_square_one :
    HasFDerivAt (fun z : ℂ => z ^ 2)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) (1 : ℂ) := by
  convert! (hasDerivAt_pow 2 (1 : ℂ)).hasFDerivAt.restrictScalars ℝ using 1
  ext w
  simp [two_smul, mul_comm]
  ring

theorem hasFDerivAt_complex_square_neg_one :
    HasFDerivAt (fun z : ℂ => z ^ 2)
      ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) (-1 : ℂ) := by
  convert! (hasDerivAt_pow 2 (-1 : ℂ)).hasFDerivAt.restrictScalars ℝ using 1
  ext w
  simp [two_smul, mul_comm]
  ring

theorem det_fderiv_complex_square_one :
    LinearMap.det (fderiv ℝ (fun z : ℂ => z ^ 2) 1).toLinearMap = 4 := by
  rw [hasFDerivAt_complex_square_one.fderiv]
  change LinearMap.det ((2 : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) = 4
  rw [LinearMap.det_smul, Complex.finrank_real_complex, LinearMap.det_id]
  norm_num

theorem det_fderiv_complex_square_neg_one :
    LinearMap.det (fderiv ℝ (fun z : ℂ => z ^ 2) (-1)).toLinearMap = 4 := by
  rw [hasFDerivAt_complex_square_neg_one.fderiv]
  change LinearMap.det ((-2 : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) = 4
  rw [LinearMap.det_smul, Complex.finrank_real_complex, LinearMap.det_id]
  norm_num

@[simp] theorem stereoCoordinate_east : stereoCoordinate east.val = 1 := by
  norm_num [stereoCoordinate, east, Matrix.cons_val_two]

@[simp] theorem stereoCoordinate_west : stereoCoordinate west.val = -1 := by
  norm_num [stereoCoordinate, west, Matrix.cons_val_two]

theorem det_fderiv_complex_square_at_preimage_east (x : Sphere)
    (hx : sphereMap x = east) :
    LinearMap.det (fderiv ℝ (fun z : ℂ => z ^ 2)
      (stereoCoordinate x.val)).toLinearMap = 4 := by
  rcases (sphereMap_eq_east_iff x).mp hx with rfl | rfl
  · simpa using det_fderiv_complex_square_one
  · simpa using det_fderiv_complex_square_neg_one

end Problem340.SphereDoubling

end

end OAI
