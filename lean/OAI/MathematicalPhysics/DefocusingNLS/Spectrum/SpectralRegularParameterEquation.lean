import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularParameterState

namespace OAI

/-! The parameter derivative of a regular column solves exactly the forced
radial equation belonging to a Jordan chain. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem spectralRegularState_source_hasDerivAt (d : ℕ) (α : ℝ)
    (c : ℂ × ℂ) (s : RegularSpectralSpace) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (spectralRegularState d α c s)
      (((spectralRegularState d α c s r).1.2,
        spectralRegularWeightedSource α s.1 r -
          ((d : ℂ) / (r : ℂ) + Complex.I * (r : ℂ) / 2) * (spectralRegularState d α c s r).1.2),
       ((spectralRegularState d α c s r).2.2,
        spectralRegularWeightedSource α s.2 r -
          ((d : ℂ) / (r : ℂ) - Complex.I * (r : ℂ) / 2) * (spectralRegularState d α c s r).2.2)) r := by
  have hp := (spectralRegularPrimitive_hasDerivAt d 1 _
    (spectralRegularWeightedSource_continuous α s.1) r).const_add c.1
  have hm := (spectralRegularPrimitive_hasDerivAt d (-1) _
    (spectralRegularWeightedSource_continuous α s.2) r).const_add c.2
  have hdp := spectralRegularSlope_hasDerivAt d 1 _
    (spectralRegularWeightedSource_continuous α s.1) r hr
  have hdm := spectralRegularSlope_hasDerivAt d (-1) _
    (spectralRegularWeightedSource_continuous α s.2) r hr
  apply ((hp.prodMk hdp).prodMk (hm.prodMk hdm)).congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · rfl
  · simp only [spectralRegularState, one_mul]
    push_cast
    ring
  · rfl
  · simp only [spectralRegularState]
    push_cast
    ring

theorem spectralRegularParameterState_hasDerivAt (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (c : ℂ × ℂ) (z : ℂ)
    (hgap : spectralRegularSourceBound A B (cp + Complex.I * z) (cm - Complex.I * z) < 2 * α)
    (r : ℝ) (hr : r ∈ Ioc 0 R) :
    let s := spectralRegularSolutionSource d R α hR hα A B cp cm c
    let W := spectralRegularState d α c (s z)
    let V := spectralRegularState d α 0 (deriv s z)
    HasDerivAt V
      (spectralRegularField d (A r) (B r) (cp + Complex.I * z) (cm - Complex.I * z) r (V r) +
        ((0, -Complex.I * (W r).1.1), (0, Complex.I * (W r).2.1))) r := by
  let s := spectralRegularSolutionSource d R α hR hα A B cp cm c
  let v := spectralRegularVector d R α hR hα A B cp cm c
  let W := spectralRegularState d α c (s z)
  let V := spectralRegularState d α 0 (deriv s z)
  change HasDerivAt V
    (spectralRegularField d (A r) (B r) (cp + Complex.I * z) (cm - Complex.I * z) r (V r) +
      ((0, -Complex.I * (W r).1.1), (0, Complex.I * (W r).2.1))) r
  have hv : deriv v z = spectralRegularInitial R α hα.le 0 +
      spectralRegularPairKernel d R α hR hα (deriv s z) := by
    simpa only [spectralRegularInitial, Prod.fst_zero, Prod.snd_zero, zero_smul,
      Prod.mk_zero_zero, zero_add] using
      spectralRegularVector_deriv_equation d R α hR hα A B cp cm c z hgap
  have hU := spectralRegularLift_unweight d R α hR hα 0 (deriv v z) (deriv s z) hv
    r ⟨hr.1.le, hr.2⟩
  have hW := spectralRegularLift_unweight d R α hR hα c (v z) (s z)
    (spectralRegularVector_equation d R α hR hα A B cp cm c z hgap) r ⟨hr.1.le, hr.2⟩
  have hUp : (Real.exp (α * r ^ 2) : ℂ) * (deriv v z).1 r = (V r).1.1 :=
    congrArg Prod.fst hU
  have hUm : (Real.exp (α * r ^ 2) : ℂ) * (deriv v z).2 r = (V r).2.1 :=
    congrArg Prod.snd hU
  have hWp : (Real.exp (α * r ^ 2) : ℂ) * (v z).1 r = (W r).1.1 :=
    congrArg Prod.fst hW
  have hWm : (Real.exp (α * r ^ 2) : ℂ) * (v z).2 r = (W r).2.1 :=
    congrArg Prod.snd hW
  have hs : deriv s z = spectralRegularSourceCLM A B (cp + Complex.I * z)
      (cm - Complex.I * z) (deriv v z) + spectralRegularSourceSlope (v z) :=
    spectralRegularSolutionSource_deriv d R α hR hα A B cp cm c z hgap
  have hsource : (spectralRegularWeightedSource α (deriv s z).1 r,
      spectralRegularWeightedSource α (deriv s z).2 r) =
      (A r * (V r).1.1 + B r * (V r).2.1 - (cp + Complex.I * z) * (V r).1.1 -
        Complex.I * (W r).1.1,
       star (B r) * (V r).1.1 + star (A r) * (V r).2.1 -
        (cm - Complex.I * z) * (V r).2.1 + Complex.I * (W r).2.1) := by
    rw [hs]
    change ((Real.exp (α * r ^ 2) : ℂ) *
      ((A r * (deriv v z).1 r + B r * (deriv v z).2 r -
        (cp + Complex.I * z) * (deriv v z).1 r) + -Complex.I * (v z).1 r),
      (Real.exp (α * r ^ 2) : ℂ) *
      ((star (B r) * (deriv v z).1 r + star (A r) * (deriv v z).2 r -
        (cm - Complex.I * z) * (deriv v z).2 r) + Complex.I * (v z).2 r)) = _
    rw [← hUp, ← hUm, ← hWp, ← hWm]
    apply Prod.ext <;> ring
  apply (spectralRegularState_source_hasDerivAt d α 0 (deriv s z) r hr.1).congr_deriv
  have hp := congrArg Prod.fst hsource
  have hm := congrArg Prod.snd hsource
  dsimp only at hp hm
  apply Prod.ext <;> apply Prod.ext
  · simp only [Prod.fst_add, add_zero, spectralRegularField]
    rfl
  · dsimp only [V, spectralRegularField, Prod.fst_add, Prod.snd_add]
    rw [hp]
    ring
  · simp only [Prod.snd_add, Prod.fst_add, add_zero, spectralRegularField]
    rfl
  · dsimp only [V, spectralRegularField, Prod.fst_add, Prod.snd_add]
    rw [hm]
    ring

end DefocusingNLS

end OAI
