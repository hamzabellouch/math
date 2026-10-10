import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearStrong

namespace OAI

/-! # The nonlinear moving-scale trajectory in the standard Sobolev space -/

open Set

namespace DefocusingNLS

/-- Changing the fixed Fourier weight preserves the reduced strong equation. -/
theorem hasDerivAt_expandingSobolev_reduced (a b k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (w : ℝ → FourierL2) (t : ℝ)
    (hw : HasDerivAt (fun s => lowerSobolevInclusion (w s))
      ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (w t) +
        (L ^ (-2 : ℝ) * Real.exp (-t)) • lowerSobolevGenerator (w t) +
        (-Complex.I) • lowerSobolevInclusion
          (expandingOddPower a k 1 ha ha1 hk le_rfl m (w t))) t) :
    let v := fun s => expandingToSobolev a k ha1 hk (w s)
    HasDerivAt (fun s => lowerSobolevInclusion (v s))
      ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (v t) +
        (L ^ (-2 : ℝ) * Real.exp (-t)) • lowerSobolevGenerator (v t) +
        (-Complex.I) • lowerSobolevInclusion
          (sobolevOddPower k (by linarith) m (v t))) t := by
  intro v
  have h := ((expandingToSobolev a k ha1 hk).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw
  change HasDerivAt (fun s => expandingToSobolev a k ha1 hk (lowerSobolevInclusion (w s)))
    (expandingToSobolev a k ha1 hk
      ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (w t) +
        (L ^ (-2 : ℝ) * Real.exp (-t)) • lowerSobolevGenerator (w t) +
        (-Complex.I) • lowerSobolevInclusion
          (expandingOddPower a k 1 ha ha1 hk le_rfl m (w t)))) t at h
  have hreal (c : ℝ) (f : FourierL2) :
      expandingToSobolev a k ha1 hk (c • f) = c • expandingToSobolev a k ha1 hk f :=
    (expandingToSobolev a k ha1 hk).toLinearMap.map_smul_of_tower c f
  simpa only [map_add, map_smul, hreal, expandingToSobolev_lowerInclusion,
    expandingToSobolev_lowerGenerator, expandingToSobolev_oddPower, v] using h

/-- Every constructed nonlinear Picard fixed point has the standard Sobolev strong equation. -/
theorem hasDerivAt_expandingNonlinearMild_sobolev (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (u : C(Icc (0 : ℝ) T, FourierL2)) (u₀ : FourierL2)
    (hu : u = expandingPicard a b k L T ha hk hL hT
      (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ u)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    let v := fun s => expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L T ha hk hL u (projIcc 0 T hT s))
    HasDerivAt (fun s => lowerSobolevInclusion (v s))
      ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (v t) +
        (L ^ (-2 : ℝ) * Real.exp (-t)) • lowerSobolevGenerator (v t) +
        (-Complex.I) • lowerSobolevInclusion
          (sobolevOddPower k (by linarith) m (v t))) t := by
  exact hasDerivAt_expandingSobolev_reduced a b k L ha ha1 hk m _ t
    (hasDerivAt_expandingNonlinearMild a b k L T ha ha1 hk hL hT m u u₀ hu t ht)

end DefocusingNLS

end OAI
