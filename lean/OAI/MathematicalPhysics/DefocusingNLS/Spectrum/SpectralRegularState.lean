import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularLiftEquation

namespace OAI

/-! The regular solution as an exact first-order four-component spectral state. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralRegularState (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) (r : ℝ) : E₄ :=
  (((spectralRegularLift d α c s r).1,
     (r : ℂ)*spectralRegularAverage d 1 (spectralRegularWeightedSource α s.1) r),
   ((spectralRegularLift d α c s r).2,
     (r : ℂ)*spectralRegularAverage d (-1) (spectralRegularWeightedSource α s.2) r))

noncomputable def spectralRegularField (d : ℕ) (A B cp cm : ℂ) (r : ℝ) (Z : E₄) : E₄ :=
  ((Z.1.2,-((d : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2)*Z.1.2+A*Z.1.1+B*Z.2.1-cp*Z.1.1),
   (Z.2.2,-((d : ℂ)/(r : ℂ)-Complex.I*(r : ℂ)/2)*Z.2.2+
     star B*Z.1.1+star A*Z.2.1-cm*Z.2.1))

theorem spectralRegularState_continuous (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) : Continuous (spectralRegularState d α c s) := by
  have hp := spectralRegularLift_continuous d α c s
  have hsp := spectralRegularAverage_continuous d 1 _ (spectralRegularWeightedSource_continuous α s.1)
  have hsm := spectralRegularAverage_continuous d (-1) _ (spectralRegularWeightedSource_continuous α s.2)
  exact (hp.fst.prodMk (Complex.continuous_ofReal.mul hsp)).prodMk
    (hp.snd.prodMk (Complex.continuous_ofReal.mul hsm))

theorem spectralRegularState_initial (d : ℕ) (α : ℝ) (c : ℂ × ℂ)
    (s : RegularSpectralSpace) : spectralRegularState d α c s 0=((c.1,0),(c.2,0)) := by
  simp [spectralRegularState,spectralRegularLift,spectralRegularPrimitive]

theorem spectralRegularState_hasDerivAt (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) (c : ℂ × ℂ)
    (v s : RegularSpectralSpace)
    (hv : v=spectralRegularInitial R α hα.le c+spectralRegularPairKernel d R α hR hα s)
    (hs : s=spectralRegularSourceCLM A B cp cm v) (r : ℝ) (hr : r ∈ Ioc 0 R) :
    HasDerivAt (spectralRegularState d α c s)
      (spectralRegularField d (A r) (B r) cp cm r (spectralRegularState d α c s r)) r := by
  have hp := (spectralRegularPrimitive_hasDerivAt d 1 _
    (spectralRegularWeightedSource_continuous α s.1) r).const_add c.1
  have hm := (spectralRegularPrimitive_hasDerivAt d (-1) _
    (spectralRegularWeightedSource_continuous α s.2) r).const_add c.2
  have hdp := spectralRegularSlope_hasDerivAt d 1 _
    (spectralRegularWeightedSource_continuous α s.1) r hr.1
  have hdm := spectralRegularSlope_hasDerivAt d (-1) _
    (spectralRegularWeightedSource_continuous α s.2) r hr.1
  have he := spectralRegularLift_source d R α hR hα A B cp cm c v s hv hs r ⟨hr.1.le,hr.2⟩
  have hep := congrArg Prod.fst he
  have hem := congrArg Prod.snd he
  dsimp only at hep hem
  apply ((hp.prodMk hdp).prodMk (hm.prodMk hdm)).congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · rfl
  · simp only [spectralRegularField,spectralRegularState,one_mul]
    rw [hep]
    push_cast
    ring
  · rfl
  · simp only [spectralRegularField,spectralRegularState]
    rw [hem]
    push_cast
    ring

end DefocusingNLS

end OAI
