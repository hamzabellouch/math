import OAI.Analysis.CircleDomains.Topology.SymmetricCircleAnnulus
import Mathlib.Analysis.Normed.Module.Connected

namespace OAI

/-! Connectedness of the fixed reflection collar, using radius and unit
circle coordinates. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma isConnected_symmetricCircleAnnulus {R:ℝ} (hR:1<R) :
    IsConnected (symmetricCircleAnnulus R) := by
  have hRp : 0<R := zero_lt_one.trans hR
  have hRi : R⁻¹<1 := (inv_lt_one₀ hRp).mpr hR
  have hs : IsConnected (sphere (0:ℂ) 1) :=
    isConnected_sphere (by rw [Complex.rank_real_complex];norm_num) 0 zero_le_one
  let g : ℝ × ℂ → ℂ := fun p => p.1 • p.2
  have hg : Continuous g := continuous_fst.smul continuous_snd
  have he : g '' (Ioo R⁻¹ R ×ˢ sphere (0:ℂ) 1)=symmetricCircleAnnulus R := by
    apply Subset.antisymm
    · rintro _ ⟨⟨r,z⟩,⟨hr,hz⟩,rfl⟩
      have hrp : 0<r := (inv_pos.mpr hRp).trans hr.1
      have hnorm : ‖g (r,z)‖=r := by
        change ‖r • z‖=r
        rw [norm_smul,mem_sphere_zero_iff_norm.mp hz,Real.norm_eq_abs,abs_of_pos hrp,mul_one]
      change R⁻¹<‖g (r,z)‖ ∧ ‖g (r,z)‖<R
      rwa [hnorm]
    · intro z hz
      refine ⟨(‖z‖,NormedSpace.normalize z),⟨hz,?_⟩,?_⟩
      · exact mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize
          (symmetricCircleAnnulus_ne_zero hRp hz))
      · exact NormedSpace.norm_smul_normalize z
  rw [←he]
  exact ((isConnected_Ioo (hRi.trans hR)).prod hs).image g hg.continuousOn

end CircleDomainRigidity

end

end OAI
