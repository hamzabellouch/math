import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevDuhamel
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevIntervalUniqueness

namespace OAI

/-! # The Bochner Duhamel identity and uniqueness of strong Sobolev solutions -/

open Filter Topology Set MeasureTheory

namespace DefocusingNLS

noncomputable def inverseSchrodingerCurve (u : ℝ → FourierL2) (t : ℝ) : FourierL2 :=
  schrodingerFlow (-t) (u t)

noncomputable def physicalSchrodingerForcing (k : ℝ) (hk : 6 < k) (m : ℕ)
    (u : ℝ → FourierL2) (t : ℝ) : FourierL2 :=
  (-Complex.I) • schrodingerFlow (-t) (sobolevOddPower k hk m (u t))

theorem continuousOn_physicalSchrodingerForcing (k : ℝ) (hk : 6 < k) (m : ℕ)
    (u : ℝ → FourierL2) (J : Set ℝ) (hu : ContinuousOn u J) :
    ContinuousOn (physicalSchrodingerForcing k hk m u) J := by
  have hN : ContinuousOn (fun t => sobolevOddPower k hk m (u t)) J :=
    (contDiff_sobolevOddPower k hk m).continuous.comp_continuousOn hu
  have hp : ContinuousOn (fun t : ℝ => (-t, sobolevOddPower k hk m (u t))) J :=
    (continuousOn_id.neg).prodMk hN
  exact (continuous_schrodingerFlow_uncurry.comp_continuousOn hp).const_smul (-Complex.I)

/-- Strong solutions satisfy the `H^k`-valued Duhamel identity, proved by their Fourier coordinates. -/
theorem sobolevDuhamel_identity
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2) (a b t₀ t : ℝ)
    (huc : ContinuousOn u (Ioo a b))
    (hu : ∀ s ∈ Ioo a b, HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u s) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u s))) s)
    (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    inverseSchrodingerCurve u t = inverseSchrodingerCurve u t₀ +
      ∫ s in t₀..t, physicalSchrodingerForcing k hk m u s := by
  have hseg : uIcc t₀ t ⊆ Ioo a b := by
    intro s hs
    exact ⟨(lt_min ht₀.1 ht.1).trans_le hs.1, hs.2.trans_lt (max_lt ht₀.2 ht.2)⟩
  have hF := continuousOn_physicalSchrodingerForcing k hk m u (Ioo a b) huc
  have hint : IntervalIntegrable (physicalSchrodingerForcing k hk m u) volume t₀ t :=
    (hF.mono hseg).intervalIntegrable
  ext n
  let E := lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n
  have hintn : IntervalIntegrable (fun s => physicalSchrodingerForcing k hk m u s n)
      volume t₀ t := (E.continuous.comp_continuousOn (hF.mono hseg)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := t₀) (b := t)
    (f := fun s => inverseSchrodingerCurve u s n)
    (f' := fun s => physicalSchrodingerForcing k hk m u s n)
    (fun s hs => hasDerivAt_interaction_coordinate k hk m u s n (hu s (hseg hs))) hintn
  have hE : (∫ s in t₀..t, physicalSchrodingerForcing k hk m u s) n =
      ∫ s in t₀..t, physicalSchrodingerForcing k hk m u s n :=
    (E.intervalIntegral_comp_comm hint).symm
  change inverseSchrodingerCurve u t n = inverseSchrodingerCurve u t₀ n +
    (∫ s in t₀..t, physicalSchrodingerForcing k hk m u s) n
  rw [hE, he]
  abel

/-- A strong Sobolev solution becomes a classical `H^k` interaction solution. -/
theorem hasDerivAt_inverseSchrodingerCurve
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2) (a b t : ℝ)
    (huc : ContinuousOn u (Ioo a b))
    (hu : ∀ s ∈ Ioo a b, HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u s) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u s))) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (inverseSchrodingerCurve u)
      (schrodingerInteractionField k hk m t (inverseSchrodingerCurve u t)) t := by
  have hF := continuousOn_physicalSchrodingerForcing k hk m u (Ioo a b) huc
  have hFt : ContinuousAt (physicalSchrodingerForcing k hk m u) t :=
    (hF t ht).continuousAt (isOpen_Ioo.mem_nhds ht)
  have hint : IntervalIntegrable (physicalSchrodingerForcing k hk m u) volume t t := by simp
  have hd := (intervalIntegral.integral_hasDerivAt_right hint
    (hF.stronglyMeasurableAtFilter isOpen_Ioo t ht) hFt).const_add (inverseSchrodingerCurve u t)
  have he : inverseSchrodingerCurve u =ᶠ[𝓝 t]
      (fun s => inverseSchrodingerCurve u t + ∫ r in t..s, physicalSchrodingerForcing k hk m u r) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact sobolevDuhamel_identity k hk m u a b t s huc hu ht hs
  have hf : schrodingerInteractionField k hk m t (inverseSchrodingerCurve u t) =
      physicalSchrodingerForcing k hk m u t := by
    unfold schrodingerInteractionField inverseSchrodingerCurve physicalSchrodingerForcing
    rw [← schrodingerFlow_add]
    simp
  rw [hf]
  exact hd.congr_of_eventuallyEq he

/-- Strong `H^k` solutions of the actual Schrödinger equation are unique on a common interval. -/
theorem sobolevSchrodingerSolution_unique_on_interval
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u v : ℝ → FourierL2) (a b t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo a b) (huc : ContinuousOn u (Ioo a b)) (hvc : ContinuousOn v (Ioo a b))
    (hu : ∀ t ∈ Ioo a b, HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t)
    (hv : ∀ t ∈ Ioo a b, HasDerivAt (fun s => lowerSobolevInclusion (v s))
      (lowerSobolevGenerator (v t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (v t))) t)
    (heq : u t₀ = v t₀) : EqOn u v (Ioo a b) := by
  have he := sobolevInteractionSolution_unique_on_interval k hk m
    (inverseSchrodingerCurve u) (inverseSchrodingerCurve v) a b t₀ ht₀
    (fun t ht => hasDerivAt_inverseSchrodingerCurve k hk m u a b t huc hu ht)
    (fun t ht => hasDerivAt_inverseSchrodingerCurve k hk m v a b t hvc hv ht)
    (by simp only [inverseSchrodingerCurve, heq])
  intro t ht
  have h := congrArg (schrodingerFlow t) (he ht)
  simpa only [inverseSchrodingerCurve, ← schrodingerFlow_add, add_neg_cancel,
    schrodingerFlow_zero] using h

end DefocusingNLS

end OAI
