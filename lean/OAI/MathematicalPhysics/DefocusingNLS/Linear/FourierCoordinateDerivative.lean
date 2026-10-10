import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianRealization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # Recovering a strong Fourier-space derivative from continuous coordinates

For the Schrödinger application the candidate derivative loses two Sobolev
orders. Once that derivative is a continuous Hilbert-space curve, its
coordinate identities imply the strong derivative by the fundamental
theorem of calculus.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

theorem hasDerivAt_fourierL2_of_coordinates (u v : ℝ → FourierL2) (a b t : ℝ)
    (hv : ContinuousOn v (Ioo a b))
    (hu : ∀ s ∈ Ioo a b, ∀ n : frequencyLattice,
      HasDerivAt (fun x => u x n) (v s n) s)
    (ht : t ∈ Ioo a b) : HasDerivAt u (v t) t := by
  have hvt : ContinuousAt v t := (hv t ht).continuousAt (isOpen_Ioo.mem_nhds ht)
  have hmeas := hv.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo t ht
  have hi : IntervalIntegrable v volume t t := by simp
  have hd := (intervalIntegral.integral_hasDerivAt_right hi hmeas hvt).const_add (u t)
  have heq : u =ᶠ[𝓝 t] (fun s => u t + ∫ x in t..s, v x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hseg : uIcc t s ⊆ Ioo a b := by
      intro x hx
      exact ⟨(lt_min ht.1 hs.1).trans_le hx.1,
        hx.2.trans_lt (max_lt ht.2 hs.2)⟩
    have hvi : IntervalIntegrable v volume t s := (hv.mono hseg).intervalIntegrable
    ext n
    let E := lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n
    have hvin : IntervalIntegrable (fun x => v x n) volume t s :=
      (E.continuous.comp_continuousOn (hv.mono hseg)).intervalIntegrable
    have hn := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => u x n) (f' := fun x => v x n)
      (fun x hx => hu x (hseg hx) n) hvin
    have hE : (∫ x in t..s, v x) n = ∫ x in t..s, v x n :=
      (E.intervalIntegral_comp_comm hvi).symm
    change u s n = u t n + (∫ x in t..s, v x) n
    rw [hE, hn]
    abel
  simpa only [zero_add] using hd.congr_of_eventuallyEq heq

end DefocusingNLS

end OAI
