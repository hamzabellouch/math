import OAI.Analysis.CoulombTransport.CoulombCalculus

namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.GeometryJets

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative interface supplied by the inverse-norm calculus. -/
def KernelDerivative : Prop :=
  ∀ b : E, b ≠ 0 → HasFDerivAt (fun v : E => ‖v‖⁻¹)
    ((-(‖b‖ ^ 3)⁻¹) • innerSL ℝ b) b

private theorem kernelDerivative : KernelDerivative (E := E) := by
  intro b hb
  exact CoulombCalculus.hasFDerivAt_pairCost hb

omit [InnerProductSpace ℝ E] in
theorem center_nonzero {a : E} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h
  simp [h] at ha

/-- The two opposite outer centers cancel the derivative in the central coordinate. -/
theorem hasFDerivAt_center_x
    (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt
      (fun x : E => ‖x - a‖⁻¹ + ‖x - (-a)‖⁻¹ + ‖a - (-a)‖⁻¹)
      (0 : E →L[ℝ] ℝ) (0 : E) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have h1 := (kernelDerivative (0 - a) (by simpa using hneg)).comp (0 : E)
    ((hasFDerivAt_id (0 : E)).sub_const a)
  have h2 := (kernelDerivative (0 - (-a)) (by simpa using ha0)).comp (0 : E)
    ((hasFDerivAt_id (0 : E)).sub_const (-a))
  have hs := (h1.add h2).add_const (‖a - (-a)‖⁻¹)
  simpa [ha, innerSL, ContinuousLinearMap.comp_id] using hs

/-- The derivative in the negative outer coordinate at an opposite unit pair. -/
theorem hasFDerivAt_center_z
    (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt
      (fun z : E => ‖(0 : E) - a‖⁻¹ + ‖(0 : E) - z‖⁻¹ + ‖a - z‖⁻¹)
      ((5 / 4 : ℝ) • innerSL ℝ a) (-a) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : -a - a = (-2 : ℝ) • a := by module
  have hnorm : ‖-a - a‖ = 2 := by rw [hvec, norm_smul, ha]; norm_num
  have hdouble : -a - a ≠ 0 := by
    intro heq
    simp [heq] at hnorm
  have h1 := kernelDerivative (-a) hneg
  have h2 := (kernelDerivative (-a - a) hdouble).comp (-a)
    ((hasFDerivAt_id (-a)).sub_const a)
  have hs := ((hasFDerivAt_const (‖a‖⁻¹) (-a)).add h1).add h2
  convert! hs using 1
  · ext z
    simp [norm_sub_rev]
  · ext v
    simp [hvec, norm_smul, ha, innerSL]
    ring

/-- Joint state derivative, with the positive outer coordinate held fixed. -/
theorem hasFDerivAt_center_state
    (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt
      (fun p : E × E => ‖p.1 - a‖⁻¹ + ‖p.1 - p.2‖⁻¹ + ‖a - p.2‖⁻¹)
      ((5 / 4 : ℝ) • (innerSL ℝ a).comp (ContinuousLinearMap.snd ℝ E E))
      (0, -a) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hnorm : ‖a - -a‖ = 2 := by rw [hvec, norm_smul, ha]; norm_num
  have hdouble : a - -a ≠ 0 := by
    intro heq
    simp [heq] at hnorm
  have hf : HasFDerivAt (fun p : E × E => p.1)
      (ContinuousLinearMap.fst ℝ E E) (0, -a) := hasFDerivAt_fst
  have hz : HasFDerivAt (fun p : E × E => p.2)
      (ContinuousLinearMap.snd ℝ E E) (0, -a) := hasFDerivAt_snd
  have h1 := (kernelDerivative (0 - a) (by simpa using hneg)).comp (0, -a)
    (hf.sub_const a)
  have h2 := (kernelDerivative (0 - -a) (by simpa using ha0)).comp (0, -a)
    (hf.sub hz)
  have h3 := (kernelDerivative (a - -a) hdouble).comp (0, -a)
    (hz.const_sub a)
  convert! (h1.add h2).add h3 using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [hvec, norm_smul, ha, innerSL]
  ring

/-- Subtracting the common central and negative outer potentials makes the center stationary. -/
theorem hasFDerivAt_center_stationary
    (a : E) (ha : ‖a‖ = 1) (K : ℝ) :
    HasFDerivAt
      (fun p : E × E =>
        (‖p.1 - a‖⁻¹ + ‖p.1 - p.2‖⁻¹ + ‖a - p.2‖⁻¹) -
        ((5 / 2 : ℝ) - K / 2 * ‖p.1‖ ^ 2) -
        ((5 / 4 : ℝ) * inner ℝ a (p.2 + a) - K / 2 * ‖p.2 + a‖ ^ 2))
      (0 : (E × E) →L[ℝ] ℝ) (0, -a) := by
  have hf : HasFDerivAt (fun p : E × E => p.1)
      (ContinuousLinearMap.fst ℝ E E) (0, -a) := hasFDerivAt_fst
  have hz : HasFDerivAt (fun p : E × E => p.2)
      (ContinuousLinearMap.snd ℝ E E) (0, -a) := hasFDerivAt_snd
  have hu := (hf.norm_sq.const_mul (K / 2)).const_sub (5 / 2)
  have hza := hz.add_const a
  have hv1 := ((innerSL ℝ a).hasFDerivAt.comp (0, -a) hza).const_mul (5 / 4)
  have hv2 := hza.norm_sq.const_mul (K / 2)
  have hs := ((hasFDerivAt_center_state a ha).sub hu).sub (hv1.sub hv2)
  convert! hs using 1
  simp

end Problem356.GeometryJets

end

end OAI
