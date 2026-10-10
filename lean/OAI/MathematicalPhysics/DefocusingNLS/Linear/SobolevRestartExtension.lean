import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTimeTranslation

namespace OAI

/-! # Extending a maximal trajectory through a later local solution -/

open Filter Topology Set

namespace DefocusingNLS

/-- A classical interaction solution through a later point extends the original maximal
trajectory to the right. This is a gluing theorem, with no assumed continuation principle. -/
theorem maximalSobolevInteractionFlow_restart_extension
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) (s δ : ℝ)
    (hs : s ∈ maximalSobolevInteractionDomain k hk m f₀) (hs₀ : 0 ≤ s) (hδ : 0 < δ)
    (w : ℝ → FourierL2)
    (hw : ∀ t ∈ Ioo (s - δ) (s + δ),
      HasDerivAt w (schrodingerInteractionField k hk m t (w t)) t)
    (hw₀ : w s = maximalSobolevInteractionFlow k hk m f₀ s) :
    ∀ t ∈ Ico s (s + δ),
      t ∈ maximalSobolevInteractionDomain k hk m f₀ ∧
        maximalSobolevInteractionFlow k hk m f₀ t = w t := by
  obtain ⟨P, hP⟩ := mem_iUnion.mp hs
  have heq₀ : P.curve s = w s :=
    (maximalSobolevInteractionFlow_eq_patch P hP).symm.trans hw₀.symm
  have hscommon : s ∈ Ioo (max P.left (s - δ)) (min P.right (s + δ)) :=
    ⟨max_lt hP.1 (by linarith), lt_min hP.2 (by linarith)⟩
  have heq := sobolevInteractionSolution_unique_on_interval k hk m P.curve w
    (max P.left (s - δ)) (min P.right (s + δ)) s hscommon
    (fun t ht => P.solves t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩)
    (fun t ht => hw t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩) heq₀
  let u : ℝ → FourierL2 := fun t => if t ≤ s then P.curve t else w t
  have hunear : u =ᶠ[𝓝 s] w := by
    filter_upwards [isOpen_Ioo.mem_nhds hscommon] with t ht
    dsimp [u]
    split_ifs with hts
    · exact heq ht
    · rfl
  have hu : ∀ t ∈ Ioo P.left (s + δ),
      HasDerivAt u (schrodingerInteractionField k hk m t (u t)) t := by
    intro t ht
    rcases lt_trichotomy t s with hts | hts | hst
    · have hnear : u =ᶠ[𝓝 t] P.curve := by
        filter_upwards [isOpen_Iio.mem_nhds hts] with r hr
        change r < s at hr
        simp only [u, ite_eq_left hr.le]
      rw [show u t = P.curve t by simp only [u, ite_eq_left hts.le]]
      exact (P.solves t ⟨ht.1, hts.trans hP.2⟩).congr_of_eventuallyEq hnear
    · subst t
      rw [show u s = w s by simpa [u] using heq₀]
      exact (hw s ⟨by linarith, by linarith⟩).congr_of_eventuallyEq hunear
    · have hnear : u =ᶠ[𝓝 t] w := by
        filter_upwards [isOpen_Ioi.mem_nhds hst] with r hr
        change s < r at hr
        simp only [u, ite_eq_right (not_le_of_gt hr)]
      rw [show u t = w t by simp only [u, ite_eq_right (not_le_of_gt hst)]]
      exact (hw t ⟨by linarith, ht.2⟩).congr_of_eventuallyEq hnear
  let Q : SobolevInteractionPatch k hk m f₀ :=
    { left := P.left
      right := s + δ
      left_neg := P.left_neg
      right_pos := by linarith
      curve := u
      initial := by simpa [u, hs₀] using P.initial
      solves := hu }
  intro t ht
  have htQ : t ∈ Ioo Q.left Q.right := ⟨hP.1.trans_le ht.1, ht.2⟩
  refine ⟨Q.subset_maximalDomain htQ, ?_⟩
  rw [maximalSobolevInteractionFlow_eq_patch Q htQ]
  change (if t ≤ s then P.curve t else w t) = w t
  split_ifs with hts
  · have hts' : t = s := le_antisymm hts ht.1
    subst t
    exact heq₀
  · rfl

/-- A local physical solution through a later state extends the original maximal physical
solution. The derivative is taken in the lower Sobolev space, as in the Cauchy problem. -/
theorem maximalSobolevSchrodingerFlow_restart_extension
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) (s δ : ℝ)
    (hs : s ∈ maximalSobolevInteractionDomain k hk m f₀) (hs₀ : 0 ≤ s) (hδ : 0 < δ)
    (w : ℝ → FourierL2) (hw₀ : w 0 = maximalSobolevSchrodingerFlow k hk m f₀ s)
    (hwc : ContinuousOn w (Ioo (-δ) δ))
    (hw : ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun r => lowerSobolevInclusion (w r))
      (lowerSobolevGenerator (w t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (w t))) t) :
    ∀ t ∈ Ico 0 δ,
      s + t ∈ maximalSobolevInteractionDomain k hk m f₀ ∧
        maximalSobolevSchrodingerFlow k hk m f₀ (s + t) = w t := by
  let z : ℝ → FourierL2 := fun t => w (-s + t)
  have hzc : ContinuousOn z (Ioo (s - δ) (s + δ)) := by
    have hl : (-δ) - (-s) = s - δ := by ring
    have hr : δ - (-s) = s + δ := by ring
    simpa only [z, hl, hr] using continuousOn_timeTranslation w (-δ) δ (-s) hwc
  have hzd : ∀ t ∈ Ioo (s - δ) (s + δ),
      HasDerivAt (fun r => lowerSobolevInclusion (z r))
        (lowerSobolevGenerator (z t) -
          Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (z t))) t := by
    intro t ht
    apply hasDerivAt_schrodinger_timeTranslation
    apply hw
    constructor <;> linarith [ht.1, ht.2]
  have hvi : inverseSchrodingerCurve z s = maximalSobolevInteractionFlow k hk m f₀ s := by
    simp [inverseSchrodingerCurve, z, hw₀, maximalSobolevSchrodingerFlow,
      ← schrodingerFlow_add]
  have hext := maximalSobolevInteractionFlow_restart_extension k hk m f₀ s δ hs hs₀ hδ
    (inverseSchrodingerCurve z)
    (fun t ht => hasDerivAt_inverseSchrodingerCurve k hk m z (s - δ) (s + δ) t hzc hzd ht) hvi
  intro t ht
  have h := hext (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨h.1, ?_⟩
  change schrodingerFlow (s + t) (maximalSobolevInteractionFlow k hk m f₀ (s + t)) = w t
  rw [h.2]
  simp [inverseSchrodingerCurve, z, ← schrodingerFlow_add]

end DefocusingNLS

end OAI
