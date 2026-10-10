import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingScaleTransfer

namespace OAI

/-! # The exact free step on expanding tori

This is the normalized-coordinate form of manuscript (lin:free-flow),
including the amplitude and the change from `Y_L` to `Y_(L exp(s/2))`.
-/

namespace DefocusingNLS

noncomputable def expandingRadius (L s : ℝ) : ℝ := L * Real.exp (s / 2)

theorem expandingRadius_ge (L s : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s) :
    L ≤ expandingRadius L s := by
  have he : 1 ≤ Real.exp (s / 2) := Real.one_le_exp_iff.mpr (by linarith)
  exact le_mul_of_one_le_right (by linarith) he

noncomputable def expandingFreeTime (L s : ℝ) : ℝ :=
  L ^ (-2 : ℝ) * (1 - Real.exp (-s))

noncomputable def expandingFreeAmplitude (a b s : ℝ) : ℂ :=
  Complex.exp (((-a * s : ℝ) : ℂ) + Complex.I * ((b * s : ℝ) : ℂ))

@[simp] theorem expandingFreeAmplitude_norm (a b s : ℝ) :
    ‖expandingFreeAmplitude a b s‖ = Real.exp (-a * s) := by
  simp [expandingFreeAmplitude, Complex.norm_exp]

theorem expandingRadius_add (L s t : ℝ) :
    expandingRadius (expandingRadius L s) t = expandingRadius L (s + t) := by
  unfold expandingRadius
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem expandingFreeAmplitude_add (a b s t : ℝ) :
    expandingFreeAmplitude a b (s + t) =
      expandingFreeAmplitude a b s * expandingFreeAmplitude a b t := by
  unfold expandingFreeAmplitude
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expandingFreeTime_add (L s t : ℝ) (hL : 1 ≤ L) :
    expandingFreeTime L (s + t) =
      expandingFreeTime L s + expandingFreeTime (expandingRadius L s) t := by
  have hR : expandingRadius L s ^ (-2 : ℝ) = L ^ (-2 : ℝ) * Real.exp (-s) := by
    unfold expandingRadius
    rw [Real.mul_rpow (by linarith : 0 ≤ L) (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  unfold expandingFreeTime
  rw [hR, neg_add, Real.exp_add]
  ring

/-- The free moving-scale operator, including the scalar similarity factor. -/
noncomputable def expandingFreeStep (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) :
    FourierL2 →L[ℂ] FourierL2 :=
  expandingFreeAmplitude a b s •
    (expandingScaleTransfer a k L (expandingRadius L s) ha hk hL
      (expandingRadius_ge L s hL hs)).comp
        (schrodingerFlow (expandingFreeTime L s)).toContinuousLinearMap

theorem expandingFreeStep_apply (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (f : FourierL2) :
    expandingFreeStep a b k L s ha hk hL hs f =
      expandingFreeAmplitude a b s •
        expandingScaleTransfer a k L (expandingRadius L s) ha hk hL
          (expandingRadius_ge L s hL hs) (schrodingerFlow (expandingFreeTime L s) f) := rfl

/-- The exact cancellation of the amplitude against the changing Sobolev weight. -/
theorem expandingFreeStep_factor (a L s : ℝ) (hL : 1 ≤ L) :
    Real.exp (-a * s) * (expandingRadius L s / L) ^ a = Real.exp (-a * s / 2) := by
  have hLn : L ≠ 0 := by linarith
  have hR : expandingRadius L s / L = Real.exp (s / 2) := by
    unfold expandingRadius
    field_simp
  rw [hR, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- The free step decays in the exact `Y_L` norms, uniformly in the starting scale. -/
theorem expandingFreeStep_norm_bound (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (f : FourierL2) :
    ‖expandingFreeStep a b k L s ha hk hL hs f‖ ≤ Real.exp (-a * s / 2) * ‖f‖ := by
  rw [expandingFreeStep_apply, norm_smul, expandingFreeAmplitude_norm]
  calc
    _ ≤ Real.exp (-a * s) *
        ((expandingRadius L s / L) ^ a * ‖schrodingerFlow (expandingFreeTime L s) f‖) :=
      mul_le_mul_of_nonneg_left
        (expandingTransferVector_norm_le a k L (expandingRadius L s) ha hk hL
          (expandingRadius_ge L s hL hs) _) (Real.exp_pos _).le
    _ = _ := by rw [(schrodingerFlow (expandingFreeTime L s)).norm_map,
      ← mul_assoc, expandingFreeStep_factor a L s hL]

theorem expandingFreeStep_opNorm_le (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) :
    ‖expandingFreeStep a b k L s ha hk hL hs‖ ≤ Real.exp (-a * s / 2) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    (expandingFreeStep_norm_bound a b k L s ha hk hL hs)

theorem expandingFourierCoefficient_schrodingerFlow (a k L t : ℝ)
    (f : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k L (schrodingerFlow t f) n =
      schrodingerMultiplier t n * expandingFourierCoefficient a k L f n := by
  simp only [expandingFourierCoefficient, schrodingerFlow_apply]
  ring

/-- The physical coefficients have exactly the phase in the manuscript's free formula. -/
theorem expandingFreeStep_coefficient (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (f : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k (expandingRadius L s)
        (expandingFreeStep a b k L s ha hk hL hs f) n =
      expandingFreeAmplitude a b s * schrodingerMultiplier (expandingFreeTime L s) n *
        expandingFourierCoefficient a k L f n := by
  rw [expandingFreeStep_apply, expandingFourierCoefficient_smul,
    expandingScaleTransfer_coefficient, expandingFourierCoefficient_schrodingerFlow, mul_assoc]

@[simp] theorem expandingFreeStep_zero (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) :
    expandingFreeStep a b k L 0 ha hk hL le_rfl = ContinuousLinearMap.id ℂ FourierL2 := by
  ext f n
  simp [expandingFreeStep, expandingFreeAmplitude, expandingFreeTime, expandingRadius]

private theorem freeStep_coefficients_injective (a k L : ℝ) (hL : 1 ≤ L) :
    Function.Injective (expandingFourierCoefficient a k L) := by
  intro f g h
  ext n
  have hn := congrArg (fun z : ℂ => (expandingSobolevWeight a k L n : ℂ) * z)
    (congrFun h n)
  simpa only [weight_mul_expandingFourierCoefficient a k L hL] using hn

/-- The free steps form the forward propagator on the moving family of tori. -/
theorem expandingFreeStep_add (a b k L s t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (expandingFreeStep a b k (expandingRadius L s) t ha hk
        (hL.trans (expandingRadius_ge L s hL hs)) ht).comp
      (expandingFreeStep a b k L s ha hk hL hs) =
      expandingFreeStep a b k L (s + t) ha hk hL (add_nonneg hs ht) := by
  apply ContinuousLinearMap.ext
  intro f
  apply freeStep_coefficients_injective a k (expandingRadius L (s + t))
    (hL.trans (expandingRadius_ge L (s + t) hL (add_nonneg hs ht)))
  funext n
  change expandingFourierCoefficient a k (expandingRadius L (s + t))
    (expandingFreeStep a b k (expandingRadius L s) t ha hk
      (hL.trans (expandingRadius_ge L s hL hs)) ht
        (expandingFreeStep a b k L s ha hk hL hs f)) n = _
  calc
    _ = expandingFreeAmplitude a b t *
        schrodingerMultiplier (expandingFreeTime (expandingRadius L s) t) n *
          expandingFourierCoefficient a k (expandingRadius L s)
            (expandingFreeStep a b k L s ha hk hL hs f) n := by
      simpa only [expandingRadius_add] using
        expandingFreeStep_coefficient a b k (expandingRadius L s) t ha hk
          (hL.trans (expandingRadius_ge L s hL hs)) ht
          (expandingFreeStep a b k L s ha hk hL hs f) n
    _ = expandingFreeAmplitude a b (s + t) *
        schrodingerMultiplier (expandingFreeTime L (s + t)) n *
          expandingFourierCoefficient a k L f n := by
      rw [expandingFreeStep_coefficient, expandingFreeAmplitude_add,
        expandingFreeTime_add L s t hL, schrodingerMultiplier_add]
      ring
    _ = _ := (expandingFreeStep_coefficient a b k L (s + t) ha hk hL
      (add_nonneg hs ht) f n).symm

end DefocusingNLS

end OAI
