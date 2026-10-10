import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.MaximalSobolevFlow
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerNonlinearEquation

namespace OAI

/-! # Finite endpoints of the maximal Sobolev solution -/

open Filter Topology Set

namespace DefocusingNLS

/-- A finite right boundary of the maximal solution domain cannot be continued across. -/
theorem maximalSobolevInteractionFlow_not_continuable
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) (a T : ℝ)
    (ha : a < 0) (hT : 0 < T)
    (hsub : Ioo a T ⊆ maximalSobolevInteractionDomain k hk m f₀)
    (hnot : T ∉ maximalSobolevInteractionDomain k hk m f₀) :
    ¬ HasSobolevInteractionContinuation k hk m (maximalSobolevInteractionFlow k hk m f₀) T := by
  rintro ⟨ε, hε, w, hw, heq⟩
  let V := maximalSobolevInteractionFlow k hk m f₀
  let u : ℝ → FourierL2 := fun s => if s < T then V s else w s
  have hueq : u =ᶠ[𝓝 T] w := by
    filter_upwards [Ioo_mem_nhds (show T - ε < T by linarith)
      (show T < T + ε by linarith)] with s hs
    dsimp [u]
    split_ifs with hst
    · exact (heq ⟨hs.1, hst⟩).symm
    · rfl
  have hsol : ∀ s ∈ Ioo a (T + ε / 2),
      HasDerivAt u (schrodingerInteractionField k hk m s (u s)) s := by
    intro s hs
    rcases lt_trichotomy s T with hst | he | hts
    · have hnear : u =ᶠ[𝓝 s] V := by
        filter_upwards [isOpen_Iio.mem_nhds hst] with r hr
        change r < T at hr
        simp only [u, ite_eq_left hr]
      have hd := hasDerivAt_maximalSobolevInteractionFlow k hk m f₀ (hsub ⟨hs.1, hst⟩)
      rw [show u s = V s by simp only [u, ite_eq_left hst]]
      exact hd.congr_of_eventuallyEq hnear
    · subst s
      rw [show u T = w T by simp [u]]
      exact (hw T ⟨by linarith, by linarith⟩).congr_of_eventuallyEq hueq
    · have hnear : u =ᶠ[𝓝 s] w := by
        filter_upwards [isOpen_Ioi.mem_nhds hts] with r hr
        change T < r at hr
        simp only [u, ite_eq_right (not_lt_of_ge hr.le)]
      have hd := hw s ⟨by linarith, by linarith [hs.2]⟩
      rw [show u s = w s by simp only [u, ite_eq_right (not_lt_of_ge hts.le)]]
      exact hd.congr_of_eventuallyEq hnear
  let P : SobolevInteractionPatch k hk m f₀ :=
    { left := a
      right := T + ε / 2
      left_neg := ha
      right_pos := by linarith
      curve := u
      initial := by simp [u, hT, V]
      solves := hsol }
  apply hnot
  exact P.subset_maximalDomain ⟨by dsimp [P]; linarith, by dsimp [P]; linarith⟩

/-- The Sobolev norm diverges at a finite right boundary of the actual maximal solution. -/
theorem maximalSobolevInteractionFlow_norm_tendsto_atTop
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) (a T : ℝ)
    (ha : a < 0) (hT : 0 < T)
    (hsub : Ioo a T ⊆ maximalSobolevInteractionDomain k hk m f₀)
    (hnot : T ∉ maximalSobolevInteractionDomain k hk m f₀) :
    Tendsto (fun t => ‖maximalSobolevInteractionFlow k hk m f₀ t‖) (𝓝[<] T) atTop := by
  apply sobolevInteraction_norm_tendsto_atTop k hk m _ a T (by linarith)
  · intro t ht
    exact hasDerivAt_maximalSobolevInteractionFlow k hk m f₀ (hsub ht)
  · exact maximalSobolevInteractionFlow_not_continuable k hk m f₀ a T ha hT hsub hnot

/-- Return the maximal interaction solution to the physical Schrödinger variable. -/
noncomputable def maximalSobolevSchrodingerFlow (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) (t : ℝ) : FourierL2 :=
  schrodingerFlow t (maximalSobolevInteractionFlow k hk m f₀ t)

@[simp] theorem maximalSobolevSchrodingerFlow_initial (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) : maximalSobolevSchrodingerFlow k hk m f₀ 0 = f₀ := by
  simp [maximalSobolevSchrodingerFlow]

theorem hasDerivAt_maximalSobolevSchrodingerFlow (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) {t : ℝ} (ht : t ∈ maximalSobolevInteractionDomain k hk m f₀) :
    HasDerivAt (fun s => lowerSobolevInclusion (maximalSobolevSchrodingerFlow k hk m f₀ s))
      (lowerSobolevGenerator (maximalSobolevSchrodingerFlow k hk m f₀ t) -
        Complex.I • lowerSobolevInclusion
          (sobolevOddPower k hk m (maximalSobolevSchrodingerFlow k hk m f₀ t))) t := by
  exact hasDerivAt_of_schrodingerInteraction k hk m _ t
    (hasDerivAt_maximalSobolevInteractionFlow k hk m f₀ ht)

theorem maximalSobolevSchrodingerFlow_norm_tendsto_atTop
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) (a T : ℝ)
    (ha : a < 0) (hT : 0 < T)
    (hsub : Ioo a T ⊆ maximalSobolevInteractionDomain k hk m f₀)
    (hnot : T ∉ maximalSobolevInteractionDomain k hk m f₀) :
    Tendsto (fun t => ‖maximalSobolevSchrodingerFlow k hk m f₀ t‖) (𝓝[<] T) atTop := by
  simpa only [maximalSobolevSchrodingerFlow, LinearIsometry.norm_map] using
    maximalSobolevInteractionFlow_norm_tendsto_atTop k hk m f₀ a T ha hT hsub hnot

/-- If the maximal time domain is bounded above, its supremum is a positive excluded endpoint. -/
theorem bounded_maximalSobolevDomain_endpoint (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) (hb : BddAbove (maximalSobolevInteractionDomain k hk m f₀)) :
    ∃ a : ℝ, a < 0 ∧ 0 < sSup (maximalSobolevInteractionDomain k hk m f₀) ∧
      Ioo a (sSup (maximalSobolevInteractionDomain k hk m f₀)) ⊆
        maximalSobolevInteractionDomain k hk m f₀ ∧
      sSup (maximalSobolevInteractionDomain k hk m f₀) ∉
        maximalSobolevInteractionDomain k hk m f₀ := by
  let D := maximalSobolevInteractionDomain k hk m f₀
  have hzero : (0 : ℝ) ∈ D := zero_mem_maximalSobolevInteractionDomain k hk m f₀
  have hpre : IsPreconnected D := isPreconnected_maximalSobolevInteractionDomain k hk m f₀
  obtain ⟨P⟩ := sobolevInteractionPatch_nonempty k hk m f₀
  have hleft : P.left / 2 ∈ D := P.subset_maximalDomain ⟨by linarith [P.left_neg],
    by linarith [P.left_neg, P.right_pos]⟩
  have hright : P.right / 2 ∈ D := P.subset_maximalDomain ⟨by linarith [P.left_neg, P.right_pos],
    by linarith [P.right_pos]⟩
  have hpos : 0 < sSup D := lt_of_lt_of_le (by linarith [P.right_pos]) (le_csSup hb hright)
  refine ⟨P.left / 2, by linarith [P.left_neg], hpos, ?_, ?_⟩
  · intro t ht
    obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup ⟨0, hzero⟩ ht.2
    exact hpre.Icc_subset hleft hr ⟨ht.1.le, htr.le⟩
  · intro hT
    have ho : IsOpen D := isOpen_maximalSobolevInteractionDomain k hk m f₀
    obtain ⟨l, r, ⟨hlt, htr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hT)
    have hy : (sSup D + r) / 2 ∈ D := hsub ⟨by linarith, by linarith⟩
    have hle := le_csSup hb hy
    linarith

/-- A finite maximal forward lifespan has divergent Sobolev norm at its endpoint. -/
theorem maximalSobolevSchrodingerFlow_finite_lifespan_blowup
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2)
    (hb : BddAbove (maximalSobolevInteractionDomain k hk m f₀)) :
    Tendsto (fun t => ‖maximalSobolevSchrodingerFlow k hk m f₀ t‖)
      (𝓝[<] (sSup (maximalSobolevInteractionDomain k hk m f₀))) atTop := by
  obtain ⟨a, ha, hT, hsub, hnot⟩ := bounded_maximalSobolevDomain_endpoint k hk m f₀ hb
  exact maximalSobolevSchrodingerFlow_norm_tendsto_atTop k hk m f₀ a _ ha hT hsub hnot

/-- An unbounded maximal forward time domain contains every nonnegative time. -/
theorem maximalSobolevInteractionDomain_global_of_unbounded
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2)
    (hb : ¬ BddAbove (maximalSobolevInteractionDomain k hk m f₀))
    (t : ℝ) (ht : 0 ≤ t) : t ∈ maximalSobolevInteractionDomain k hk m f₀ := by
  obtain ⟨r, hr, htr⟩ := not_bddAbove_iff.mp hb t
  exact (isPreconnected_maximalSobolevInteractionDomain k hk m f₀).Icc_subset
    (zero_mem_maximalSobolevInteractionDomain k hk m f₀) hr ⟨ht, htr.le⟩

end DefocusingNLS

end OAI
