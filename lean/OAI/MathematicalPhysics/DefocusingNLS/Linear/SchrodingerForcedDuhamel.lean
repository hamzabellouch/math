import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevDuhamelIntegral

namespace OAI

/-! # Duhamel's identity with a Sobolev forcing term

The forcing is an actual vector in the upper Sobolev space, while the time
 derivative is taken after the two-order inclusion.  Fourier coordinates
remove the unbounded generator without assuming upper-space differentiability.
-/

open Filter Topology Set MeasureTheory

namespace DefocusingNLS

/-- The forced equation determines every physical Fourier coefficient. -/
theorem hasDerivAt_coordinate_forced_schrodinger
    (u j : ℝ → FourierL2) (t : ℝ) (n : frequencyLattice)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) + lowerSobolevInclusion (j t)) t) :
    HasDerivAt (fun s => u s n)
      (-Complex.I * ((‖n‖ ^ 2 : ℝ) : ℂ) * u t n + j t n) t := by
  have h := hasDerivAt_coordinate_of_lowerSobolev u _ t n hu
  apply h.congr_deriv
  simp only [lp.coeFn_add, Pi.add_apply, lowerSobolevGenerator_apply,
    lowerSobolevInclusion_apply, Complex.ofReal_div, Complex.ofReal_inv]
  have hb : (((1 + ‖n‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + ‖n‖ ^ 2 by positivity))
  field_simp [hb]

/-- The inverse phase cancels the free generator in the forced equation. -/
theorem hasDerivAt_forced_interaction_coordinate
    (u j : ℝ → FourierL2) (t : ℝ) (n : frequencyLattice)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) + lowerSobolevInclusion (j t)) t) :
    HasDerivAt (fun s => inverseSchrodingerCurve u s n)
      (schrodingerFlow (-t) (j t) n) t := by
  have hp : HasDerivAt (fun s => schrodingerMultiplier (-s) n)
      (Complex.I * ((‖n‖ ^ 2 : ℝ) : ℂ) * schrodingerMultiplier (-t) n) t := by
    have h := (hasDerivAt_schrodingerMultiplier_mul n 1 (-t)).scomp t (hasDerivAt_neg t)
    convert h using 1
    · funext s
      simp
    · simp only [mul_one, neg_smul, one_smul]
      ring
  have h := hp.mul (hasDerivAt_coordinate_forced_schrodinger u j t n hu)
  apply h.congr_deriv
  simp only [schrodingerFlow_apply]
  ring

theorem continuousOn_rotatedSchrodingerForcing (j : ℝ → FourierL2) (J : Set ℝ)
    (hj : ContinuousOn j J) :
    ContinuousOn (fun t => schrodingerFlow (-t) (j t)) J := by
  have hneg : ContinuousOn (fun t : ℝ => -t) J := continuous_neg.continuousOn
  have hp : ContinuousOn (fun t : ℝ => (-t, j t)) J := hneg.prodMk hj
  exact Continuous.comp_continuousOn
    (f := fun t : ℝ => (-t, j t))
    (g := fun p : ℝ × FourierL2 => schrodingerFlow p.1 p.2)
    continuous_schrodingerFlow_uncurry hp

/-- The forced equation gives an upper-Sobolev Bochner integral identity. -/
theorem forcedSobolevDuhamel_identity
    (u j : ℝ → FourierL2) (a b t₀ t : ℝ)
    (hj : ContinuousOn j (Ioo a b))
    (hu : ∀ s ∈ Ioo a b, HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u s) + lowerSobolevInclusion (j s)) s)
    (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    inverseSchrodingerCurve u t = inverseSchrodingerCurve u t₀ +
      ∫ s in t₀..t, schrodingerFlow (-s) (j s) := by
  have hseg : uIcc t₀ t ⊆ Ioo a b := by
    intro s hs
    exact ⟨(lt_min ht₀.1 ht.1).trans_le hs.1, hs.2.trans_lt (max_lt ht₀.2 ht.2)⟩
  have hF := continuousOn_rotatedSchrodingerForcing j (Ioo a b) hj
  have hint : IntervalIntegrable (fun s => schrodingerFlow (-s) (j s)) volume t₀ t :=
    (hF.mono hseg).intervalIntegrable
  ext n
  let E := lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n
  have hintn : IntervalIntegrable (fun s => schrodingerFlow (-s) (j s) n)
      volume t₀ t := (E.continuous.comp_continuousOn (hF.mono hseg)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := t₀) (b := t)
    (f := fun s => inverseSchrodingerCurve u s n)
    (f' := fun s => schrodingerFlow (-s) (j s) n)
    (fun s hs => hasDerivAt_forced_interaction_coordinate u j s n (hu s (hseg hs))) hintn
  have hE : (∫ s in t₀..t, schrodingerFlow (-s) (j s)) n =
      ∫ s in t₀..t, schrodingerFlow (-s) (j s) n :=
    (E.intervalIntegral_comp_comm hint).symm
  change inverseSchrodingerCurve u t n = inverseSchrodingerCurve u t₀ n +
    (∫ s in t₀..t, schrodingerFlow (-s) (j s)) n
  rw [hE, he]
  abel

/-- The usual variation-of-constants formula in the physical Sobolev representation. -/
theorem forcedSobolevDuhamel_physical
    (u j : ℝ → FourierL2) (a b t₀ t : ℝ)
    (hj : ContinuousOn j (Ioo a b))
    (hu : ∀ s ∈ Ioo a b, HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u s) + lowerSobolevInclusion (j s)) s)
    (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    u t = schrodingerFlow (t - t₀) (u t₀) +
      ∫ s in t₀..t, schrodingerFlow (t - s) (j s) := by
  have h := congrArg (schrodingerFlow t)
    (forcedSobolevDuhamel_identity u j a b t₀ t hj hu ht₀ ht)
  rw [map_add, ← (schrodingerFlow t).intervalIntegral_comp_comm] at h
  simpa only [inverseSchrodingerCurve, ← schrodingerFlow_add, add_neg_cancel,
    schrodingerFlow_zero, ← sub_eq_add_neg] using h

/-- Continuous upper-space forcing upgrades the interaction curve to a classical one. -/
theorem hasDerivAt_forced_inverseSchrodingerCurve
    (u j : ℝ → FourierL2) (a b t : ℝ)
    (hj : ContinuousOn j (Ioo a b))
    (hu : ∀ s ∈ Ioo a b, HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u s) + lowerSobolevInclusion (j s)) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (inverseSchrodingerCurve u) (schrodingerFlow (-t) (j t)) t := by
  have hF := continuousOn_rotatedSchrodingerForcing j (Ioo a b) hj
  have hFt : ContinuousAt (fun s => schrodingerFlow (-s) (j s)) t :=
    (hF t ht).continuousAt (isOpen_Ioo.mem_nhds ht)
  have hint : IntervalIntegrable (fun s => schrodingerFlow (-s) (j s)) volume t t := by simp
  have hd := (intervalIntegral.integral_hasDerivAt_right hint
    (hF.stronglyMeasurableAtFilter isOpen_Ioo t ht) hFt).const_add (inverseSchrodingerCurve u t)
  have he : inverseSchrodingerCurve u =ᶠ[𝓝 t]
      (fun s => inverseSchrodingerCurve u t + ∫ r in t..s, schrodingerFlow (-r) (j r)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact forcedSobolevDuhamel_identity u j a b t s hj hu ht hs
  exact hd.congr_of_eventuallyEq he

/-- An approximate nonlinear Schrödinger trajectory has the exact rotated residual. -/
theorem hasDerivAt_residual_inverseSchrodingerCurve
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u r : ℝ → FourierL2) (a b t : ℝ)
    (huc : ContinuousOn u (Ioo a b)) (hrc : ContinuousOn r (Ioo a b))
    (hu : ∀ s ∈ Ioo a b, HasDerivAt (fun x => lowerSobolevInclusion (u x))
      (lowerSobolevGenerator (u s) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u s)) +
        lowerSobolevInclusion (r s)) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (inverseSchrodingerCurve u)
      (schrodingerInteractionField k hk m t (inverseSchrodingerCurve u t) +
        schrodingerFlow (-t) (r t)) t := by
  let j : ℝ → FourierL2 := fun s => (-Complex.I) • sobolevOddPower k hk m (u s) + r s
  have hj : ContinuousOn j (Ioo a b) :=
    (((contDiff_sobolevOddPower k hk m).continuous.comp_continuousOn huc).const_smul
      (-Complex.I)).add hrc
  have h := hasDerivAt_forced_inverseSchrodingerCurve u j a b t hj
    (fun s hs => by simpa [j, map_add, map_smul, sub_eq_add_neg, add_assoc] using hu s hs) ht
  apply h.congr_deriv
  simp [j, schrodingerInteractionField, inverseSchrodingerCurve, map_add, map_smul,
    ← schrodingerFlow_add]

end DefocusingNLS

end OAI
