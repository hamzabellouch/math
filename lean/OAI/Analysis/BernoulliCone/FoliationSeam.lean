import OAI.Analysis.BernoulliCone.UpperCalibration

namespace OAI

universe uE

section
noncomputable section
open scoped RealInnerProductSpace
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The extended calibration jump across the graph of a matching seam. -/
lemma seam_flux_identity (Gp Gm H N:E) (ρp ρm:ℝ)
    (hp:H=Gp+ρp • N) (hm:H=Gm+ρm • N) :
    ‖Gp‖^2-‖Gm‖^2-2*inner ℝ (Gp-Gm) H=
      -(ρp+ρm)*inner ℝ (Gp-Gm) N := by
  have hh:Gp+Gm-(2:ℝ) • H=-(ρp+ρm) • N := by
    rw [hp] at hm
    have hg:Gm=Gp+(ρp-ρm) • N := by
      calc
        Gm = (Gm+ρm • N)-ρm • N := by abel
        _ = _ := by rw [←hm]; module
    rw [hg,hp]
    module
  have hid:inner ℝ (Gp-Gm) (Gp+Gm-(2:ℝ) • H)=
      ‖Gp‖^2-‖Gm‖^2-2*inner ℝ (Gp-Gm) H := by
    simp only [inner_sub_right,inner_add_right,inner_sub_left,real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm Gm Gp]
    ring
  rw [←hid,hh,real_inner_smul_right]
lemma seam_flux_nonpos (Gp Gm H N:E) (ρp ρm:ℝ)
    (hp:H=Gp+ρp • N) (hm:H=Gm+ρm • N)
    (hρ:0≤ρp+ρm) (hj:0 ≤ inner ℝ (Gp-Gm) N) :
    ‖Gp‖^2-‖Gm‖^2-2*inner ℝ (Gp-Gm) H≤0 := by
  rw [seam_flux_identity Gp Gm H N ρp ρm hp hm]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) hj
end Bernoulli.Foliation

end
end

end OAI
