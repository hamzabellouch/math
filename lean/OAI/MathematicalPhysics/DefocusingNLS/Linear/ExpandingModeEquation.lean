import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingModeDuhamel
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPotentialContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerGenerator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! # The actual Fourier-mode equation on an expanding torus

At fixed normalized torus position, each physical coefficient solves the
Schrödinger equation with the expected frequency factor `L_s⁻² |n|²`.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

noncomputable def expandingModeRate (a b L s : ℝ) (n : frequencyLattice) : ℂ :=
  (-(a : ℂ) + Complex.I * b) -
    Complex.I * ((L ^ (-2 : ℝ) * Real.exp (-s) * ‖n‖ ^ 2 : ℝ) : ℂ)

theorem hasDerivAt_expandingFreeTime (L s : ℝ) :
    HasDerivAt (expandingFreeTime L) (L ^ (-2 : ℝ) * Real.exp (-s)) s := by
  have h := ((hasDerivAt_const s (1 : ℝ)).sub
    (((hasDerivAt_id s).neg).exp)).const_mul (L ^ (-2 : ℝ))
  convert h using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_expandingFreeAmplitude (a b s : ℝ) :
    HasDerivAt (expandingFreeAmplitude a b)
      ((-(a : ℂ) + Complex.I * b) * expandingFreeAmplitude a b s) s := by
  let C : ℂ := -(a : ℂ) + Complex.I * b
  have h : HasDerivAt (fun t : ℝ => Complex.exp (C * (t : ℂ)))
      (Complex.exp (C * (s : ℂ)) * C) s := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (s : ℂ)).const_mul C).cexp).comp_ofReal
  have heq : (fun t : ℝ => Complex.exp (C * (t : ℂ))) = expandingFreeAmplitude a b := by
    funext t
    unfold expandingFreeAmplitude
    congr 1
    dsimp [C]
    push_cast
    ring
  rw [heq] at h
  apply h.congr_deriv
  have hs : Complex.exp (C * (s : ℂ)) = expandingFreeAmplitude a b s := congrFun heq s
  rw [hs]
  exact mul_comm _ _

theorem hasDerivAt_expandingFreeMode (a b L s : ℝ) (n : frequencyLattice) :
    HasDerivAt (fun t => expandingFreeMode a b L t n)
      (expandingModeRate a b L s n * expandingFreeMode a b L s n) s := by
  have hp := (hasDerivAt_schrodingerMultiplier_mul n 1 (expandingFreeTime L s)).scomp s
    (hasDerivAt_expandingFreeTime L s)
  simp only [mul_one] at hp
  have h := (hasDerivAt_expandingFreeAmplitude a b s).mul hp
  convert h using 1
  · rfl
  · unfold expandingModeRate expandingFreeMode
    simp only [Complex.real_smul, Function.comp_def]
    push_cast
    ring

theorem continuous_expandingFreeMode (a b L : ℝ) (n : frequencyLattice) :
    Continuous (fun t => expandingFreeMode a b L t n) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_expandingFreeMode a b L t n).continuousAt)

/-- Physical coefficient evaluation is jointly continuous in the radius and vector. -/
theorem continuous_expandingFourierCoefficient (a k : ℝ) (n : frequencyLattice) :
    Continuous (fun p : {L : ℝ // 1 ≤ L} × FourierL2 =>
      expandingFourierCoefficient a k p.1.1 p.2 n) := by
  have hL : Continuous (fun p : {L : ℝ // 1 ≤ L} × FourierL2 => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hl : Continuous (fun p : {L : ℝ // 1 ≤ L} × FourierL2 => p.1.1 ^ (2 * a)) :=
    hL.rpow_const (fun p => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one p.1.2)))
  have hh : Continuous (fun p : {L : ℝ // 1 ≤ L} × FourierL2 => p.1.1 ^ (12 - 2 * k)) :=
    hL.rpow_const (fun p => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one p.1.2)))
  have hw : Continuous (fun p : {L : ℝ // 1 ≤ L} × FourierL2 =>
      expandingSobolevWeight a k p.1.1 n) := by
    unfold expandingSobolevWeight expandingSobolevWeightSq
    exact continuous_const.mul (Real.continuous_sqrt.comp
      ((hl.mul continuous_const).add (hh.mul continuous_const)))
  exact (Complex.continuous_ofReal.comp
    (hw.inv₀ (fun p => (expandingSobolevWeight_pos a k p.1.1 p.1.2 n).ne'))).mul
    ((lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n).continuous.comp continuous_snd)

theorem continuousOn_expandingPhysicalCoefficient (a k L T : ℝ) (hL : 1 ≤ L)
    (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 T)) (n : frequencyLattice) :
    ContinuousOn (fun t => expandingFourierCoefficient a k (expandingRadius L t) (r t) n)
      (Icc 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_expandingFourierCoefficient a k n).comp
    ((expandingRadiusCurve L T hL).continuous.prodMk hr.domRestrict)

/-- Differentiating the exact mild formula gives the actual moving Fourier equation. -/
theorem hasDerivAt_expandingMild_coefficient (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u r : ℝ → FourierL2) (u₀ : FourierL2) (hr : ContinuousOn r (Icc 0 T))
    (hu : ∀ (s : ℝ) (hs : s ∈ Icc 0 T), u s = expandingFreeStep a b k L s ha hk hL hs.1 u₀ +
      expandingDuhamel a b k L ha hk hL s r)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (n : frequencyLattice) :
    HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n)
      (expandingModeRate a b L t n *
        expandingFourierCoefficient a k (expandingRadius L t) (u t) n +
        expandingFourierCoefficient a k (expandingRadius L t) (r t) n) t := by
  let c := expandingFourierCoefficient a k L u₀ n
  let f := fun s => (expandingFreeMode a b L s n)⁻¹ *
    expandingFourierCoefficient a k (expandingRadius L s) (r s) n
  have hf : ContinuousOn f (Icc 0 T) :=
    ((continuous_expandingFreeMode a b L n).inv₀
      (expandingFreeMode_ne_zero a b L · n)).continuousOn.mul
        (continuousOn_expandingPhysicalCoefficient a k L T hL r hr n)
  have hI := intervalIntegral.integral_hasDerivAt_right
    ((hf.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hf.mono Ioo_subset_Icc_self) t ht)
    (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))
  have hd := (hasDerivAt_expandingFreeMode a b L t n).mul
    ((hasDerivAt_const t c).add hI)
  have heq : (fun s => expandingFreeMode a b L s n * (c + ∫ τ in 0..s, f τ)) =ᶠ[𝓝 t]
      (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [hu s ⟨hs.1.le, hs.2.le⟩,
      expandingMild_coefficient a b k L s ha hk hL hs.1.le r
        (hr.mono (Icc_subset_Icc le_rfl hs.2.le)) u₀ n]
    congr 2
    rw [intervalIntegral.integral_of_le hs.1.le, ← integral_Icc_eq_integral_Ioc]
  have heqt := heq.eq_of_nhds
  apply (hd.congr_of_eventuallyEq heq.symm).congr_deriv
  rw [← heqt]
  dsimp [f]
  have hc : expandingFreeMode a b L t n *
      ((expandingFreeMode a b L t n)⁻¹ *
        expandingFourierCoefficient a k (expandingRadius L t) (r t) n) =
      expandingFourierCoefficient a k (expandingRadius L t) (r t) n := by
    rw [← mul_assoc, mul_inv_cancel₀ (expandingFreeMode_ne_zero a b L t n), one_mul]
  rw [zero_add, hc]
  ring

end DefocusingNLS

end OAI
