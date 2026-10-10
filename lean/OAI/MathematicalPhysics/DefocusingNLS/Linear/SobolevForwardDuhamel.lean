import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevDuhamelIntegral

namespace OAI

/-! # Duhamel at the initial endpoint of a forward strong solution

Continuity at time zero and the strong equation on positive times suffice;
no two-sided derivative at the initial endpoint is assumed.
-/

open Filter Topology Set MeasureTheory

namespace DefocusingNLS

theorem continuousOn_inverseSchrodingerCurve (u : ℝ → FourierL2) (J : Set ℝ)
    (hu : ContinuousOn u J) : ContinuousOn (inverseSchrodingerCurve u) J := by
  intro t ht
  have hp : ContinuousWithinAt (fun s : ℝ => (-s, u s)) J t :=
    (continuousWithinAt_id : ContinuousWithinAt (id : ℝ → ℝ) J t).neg.prodMk (hu t ht)
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun s : ℝ => (-s, u s))
    (g := fun p : ℝ × FourierL2 => schrodingerFlow p.1 p.2)
    (continuous_schrodingerFlow_uncurry.continuousAt (x := (-t, u t))) hp

theorem sobolevForwardDuhamel_identity
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2) (T t : ℝ)
    (huc : ContinuousOn u (Icc 0 T))
    (hu : ∀ s ∈ Ioo 0 T, HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u s) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u s))) s)
    (ht : t ∈ Icc 0 T) :
    inverseSchrodingerCurve u t = inverseSchrodingerCurve u 0 +
      ∫ s in (0 : ℝ)..t, physicalSchrodingerForcing k hk m u s := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hF := continuousOn_physicalSchrodingerForcing k hk m u (Icc 0 T) huc
  have hint : IntervalIntegrable (physicalSchrodingerForcing k hk m u) volume 0 t :=
    (hF.mono hsub).intervalIntegrable_of_Icc ht.1
  ext n
  let E := lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n
  have hintn : IntervalIntegrable (fun s => physicalSchrodingerForcing k hk m u s n)
      volume 0 t := (E.continuous.comp_continuousOn (hF.mono hsub)).intervalIntegrable_of_Icc ht.1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s => inverseSchrodingerCurve u s n)
    (f' := fun s => physicalSchrodingerForcing k hk m u s n) ht.1
    (E.continuous.comp_continuousOn ((continuousOn_inverseSchrodingerCurve u _ huc).mono hsub))
    (fun s hs => hasDerivAt_interaction_coordinate k hk m u s n
      (hu s ⟨hs.1, hs.2.trans_le ht.2⟩)) hintn
  have hE : (∫ s in (0 : ℝ)..t, physicalSchrodingerForcing k hk m u s) n =
      ∫ s in (0 : ℝ)..t, physicalSchrodingerForcing k hk m u s n :=
    (E.intervalIntegral_comp_comm hint).symm
  change inverseSchrodingerCurve u t n = inverseSchrodingerCurve u 0 n +
    (∫ s in (0 : ℝ)..t, physicalSchrodingerForcing k hk m u s) n
  rw [hE, he]
  abel

theorem hasDerivWithinAt_inverseSchrodingerCurve_zero
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2) (T : ℝ) (hT : 0 < T)
    (huc : ContinuousOn u (Icc 0 T))
    (hu : ∀ s ∈ Ioo 0 T, HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u s) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u s))) s) :
    HasDerivWithinAt (inverseSchrodingerCurve u)
      (schrodingerInteractionField k hk m 0 (inverseSchrodingerCurve u 0)) (Ici 0) 0 := by
  let F := physicalSchrodingerForcing k hk m u
  have hF : ContinuousOn F (Icc 0 T) :=
    continuousOn_physicalSchrodingerForcing k hk m u (Icc 0 T) huc
  let G := fun s : ℝ => F (projIcc 0 T hT.le s)
  have hG : Continuous G := hF.domRestrict.comp continuous_projIcc
  let V := fun s => inverseSchrodingerCurve u 0 + ∫ r in (0 : ℝ)..s, G r
  have hV : HasDerivAt V (G 0) 0 :=
    (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 0)
      hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).const_add _
  have hEq (s : ℝ) (hs : s ∈ Icc 0 T) : inverseSchrodingerCurve u s = V s := by
    rw [sobolevForwardDuhamel_identity k hk m u T s huc hu hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 T := by
      have hr0 : r ∈ Icc 0 s := by simpa only [uIcc_of_le hs.1] using hr
      exact ⟨hr0.1, hr0.2.trans hs.2⟩
    simp only [G, F, projIcc_of_mem _ hr']
  have he : inverseSchrodingerCurve u =ᶠ[𝓝[Ici 0] 0] V := by
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds hT) : Iio T ∈ 𝓝[Ici 0] (0 : ℝ))] with s hs hst
    exact hEq s ⟨hs, hst.le⟩
  have hd := hV.hasDerivWithinAt.congr_of_eventuallyEq_of_mem he (show (0 : ℝ) ∈ Ici 0 by simp)
  convert hd using 1
  simp [G, F, inverseSchrodingerCurve, physicalSchrodingerForcing, schrodingerInteractionField]

end DefocusingNLS

end OAI
