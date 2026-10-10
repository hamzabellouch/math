import OAI.Probability.SLE.Loewner.InitialInverseJointContinuity
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Local uniform time continuity of the exact inverse slit charts. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

theorem initialInverseChart_locallyUniform_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (s : unitInterval) :
    TendstoLocallyUniformlyOn (initialInverseChart p hi h0 hH)
      (initialInverseChart p hi h0 hH s) (𝓝 s) upperHalfPlane := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalfPlane]
  intro K hKH hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun a : unitInterval × K =>
      initialInverseChart p hi h0 hH a.1 a.2) := by
    exact (initialInverseChart_joint_continuous p hi h0 hH).comp
      (continuous_fst.prodMk (Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_snd) (fun a => hKH a.2.property)))
  have hu := Continuous.tendstoUniformly
    (fun t (z : K) => initialInverseChart p hi h0 hH t z) hc s
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hu

end SLEExactGauge

end

end OAI
