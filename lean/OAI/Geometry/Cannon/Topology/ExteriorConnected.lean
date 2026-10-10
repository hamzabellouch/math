import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonPlaneExterior
open Set Metric Topology

lemma exterior_connected {R : ℝ} (hR : 0≤R) :
    IsConnected {z : ℂ | R<‖z‖} := by
  have hs := isConnected_sphere (E:=ℂ) (by rw [Complex.rank_real_complex]; norm_num) (0:ℂ)
    (by norm_num : 0≤(1:ℝ))
  have ht : IsConnected (Ioi R) := isConnected_Ioi
  have hc := (hs.prod ht).image (fun p : ℂ×ℝ => p.2 • p.1) (by fun_prop)
  have he : (fun p : ℂ×ℝ => p.2 • p.1) '' (sphere (0:ℂ) 1 ×ˢ Ioi R)=
      {z : ℂ | R<‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨u,t⟩,⟨hu,ht⟩,rfl⟩
      have hu' : ‖u‖=1 := by simpa [mem_sphere,dist_zero_right] using hu
      change R<‖t • u‖
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hR.trans ht.le),hu',mul_one]
      exact ht
    · intro hz
      have hn : 0<‖z‖ := hR.trans_lt hz
      refine ⟨(‖z‖⁻¹ • z,‖z‖),⟨?_,hz⟩,?_⟩
      · simp [hn.ne']
      · simp [hn.ne']
  rwa [he] at hc
end CannonPlaneExterior

end
end
end
end

end OAI
