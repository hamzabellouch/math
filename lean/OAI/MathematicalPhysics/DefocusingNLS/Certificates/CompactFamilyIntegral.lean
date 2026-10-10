import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffFamilyContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Differentiation of a compact physical family before Fourier sampling -/

open Set MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- A fixed compact support supplies the integrable local derivative bound. -/
theorem hasDerivAt_compactFamily_integral (F Fd : ℝ → E → ℂ)
    (hF : Continuous (Function.uncurry F)) (hFd : Continuous (Function.uncurry Fd))
    (K : Set E) (hK : IsCompact K)
    (hzero : ∀ t x, x ∉ K → F t x = 0)
    (hdzero : ∀ t x, x ∉ K → Fd t x = 0)
    (hd : ∀ t x, HasDerivAt (fun s => F s x) (Fd t x) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, F s x) (∫ x, Fd t x) t := by
  have hc (s : ℝ) : Continuous (F s) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hdc (s : ℝ) : Continuous (Fd s) :=
    hFd.comp (continuous_const.prodMk continuous_id)
  have hsupp (s : ℝ) : HasCompactSupport (F s) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hzero s x hxK)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hFd.continuousOn : ContinuousOn (Function.uncurry Fd) (Icc (t - 1) (t + 1) ×ˢ K))
  let C : ℝ := max B 0
  let bound : E → ℝ := K.indicator (fun _ => C)
  have hb : Integrable bound :=
    (integrableOn_const (μ := (volume : Measure E)) hK.measure_lt_top.ne).integrable_indicator
      hK.measurableSet
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := Fd) (bound := bound)
    (Ioo_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Eventually.of_forall fun s => (hc s).aestronglyMeasurable)
    ((hc t).integrable_of_hasCompactSupport (hsupp t))
    (hdc t).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      intro s hs
      by_cases hx : x ∈ K
      · rw [show bound x = C by simp [bound, hx]]
        exact (hB (s, x) ⟨⟨hs.1.le, hs.2.le⟩, hx⟩).trans (le_max_left _ _)
      · rw [hdzero s x hx]
        simp [bound, hx])
    hb (Eventually.of_forall fun x => fun s _ => hd s x)).2

/-- The same local argument differentiates the physical Fourier transform. -/
theorem hasDerivAt_compactFamily_fourier (F Fd : ℝ → E → ℂ)
    (hF : Continuous (Function.uncurry F)) (hFd : Continuous (Function.uncurry Fd))
    (K : Set E) (hK : IsCompact K)
    (hzero : ∀ t x, x ∉ K → F t x = 0)
    (hdzero : ∀ t x, x ∉ K → Fd t x = 0)
    (hd : ∀ t x, HasDerivAt (fun s => F s x) (Fd t x) t) (t : ℝ) (ξ : E) :
    HasDerivAt (fun s => radianFourierIntegral (F s) ξ)
      (radianFourierIntegral (Fd t) ξ) t := by
  let e : E → ℂ := fun x => Complex.exp ((-inner ℝ x ξ : ℝ) * Complex.I)
  have he : Continuous e := by fun_prop
  exact hasDerivAt_compactFamily_integral
    (fun s x => e x * F s x) (fun s x => e x * Fd s x)
    ((he.comp continuous_snd).mul hF) ((he.comp continuous_snd).mul hFd)
    K hK (fun s x hx => by rw [hzero s x hx, mul_zero])
    (fun s x hx => by rw [hdzero s x hx, mul_zero])
    (fun s x => (hd s x).const_mul (e x)) t

end DefocusingNLS

end OAI
