import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialPrimitiveIntegral

namespace OAI

/-! Completed radial values and weak derivatives are locally integrable away from the origin. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralRadialL2_locallyIntegrableOn (R : ℝ) (u : SpectralRadialL2 R) :
    LocallyIntegrableOn (fun r => u r) (Ioo 0 R) := by
  intro x hx
  rcases hx with ⟨hx0,hxR⟩
  have hlo : 0 < x/2 := by linarith
  have hlx : x/2 < x := by linarith
  have hxu : x < (x+R)/2 := by linarith
  have huR : (x+R)/2 ≤ R := by linarith
  refine ⟨Icc (x/2) ((x+R)/2),mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hlx hxu),?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (hlx.trans hxu).le).mp
    (spectralRadialL2_intervalIntegrable R (x/2) ((x+R)/2) hlo
      (hlx.trans hxu).le huR u)

end DefocusingNLS

end OAI
