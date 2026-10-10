import Mathlib
import OAI.Combinatorics.UniformKServer.ParentBeta

namespace OAI

                                    
section

/-! One absolute choice in the source's ordered smallness requirements.
All parameters remain independent of the star, k, law and horizon. -/
namespace UniformKServer.StarConstants
noncomputable section

def delta : ℝ := 1/1000000000000
def rho : ℝ := 1/10000000000000000
def lam : ℝ := 1/1000000000000
def eps : ℝ := 1/100000000000
def ct : ℝ := 1/1000000000000
def cw : ℝ := 1/100000000000000
def multiplier : ℝ := 10000000000000000

theorem delta_bounds : 0 < delta ∧ delta < 1/2 := by norm_num [delta]
theorem rho_bounds : 0 < rho ∧ rho < 1/2 := by norm_num [rho]
theorem lam_bounds : 0 < lam ∧ lam ≤ 1/4 := by norm_num [lam]
theorem eps_pos : 0 < eps := by norm_num [eps]
theorem fine_error : rho+4*ParentBeta.cBeta*delta ≤ lam/4 := by
  norm_num [rho,ParentBeta.cBeta,delta,lam]
theorem fine_gap : 4*lam ≤ (ParentBeta.cBeta/50)/96 := by norm_num [lam,ParentBeta.cBeta]
theorem fine_eps : 4*lam ≤ eps := by norm_num [lam,eps]
theorem ct_pos : 0 < ct := by norm_num [ct]
theorem ct_height : ct*50000 ≤ 1 := by norm_num [ct]
theorem multiplier_bound : 1000 < multiplier*ct := by norm_num [multiplier,ct]
theorem cw_pos : 0 < cw := by norm_num [cw]
theorem cw_height : cw*50000 ≤ 1 := by norm_num [cw]

end
end UniformKServer.StarConstants

end

end OAI
