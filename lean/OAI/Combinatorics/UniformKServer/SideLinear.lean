import Mathlib
import OAI.Combinatorics.UniformKServer.AdaptiveSide

namespace OAI

                                 
section

/-! Exact affine side-potential coefficients. Their boundedness holds at every
 compact-domain state, not only at states feasible for the fresh posteriors. -/
noncomputable section
namespace UniformKServer.SideLinear
open Finset UniformKServer.AdaptiveSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

def bCoefficient (p : Config ι) (w : ι → ℝ) (i : ι) : ℝ :=
  -28*SideStability.bCoefficient p.b (theta p i) (offset p i) (w i)
def dCoefficient (p : Config ι) (w : ι → ℝ) : ℝ :=
  28*∑ i, SideStability.dCoefficient (theta p i) (offset p i) (w i)

theorem affine (p : Config ι) (B w : ι → ℝ) (D : ℝ) :
    potential p B D w=(∑ i, bCoefficient p w i*B i)+dCoefficient p w*D := by
  unfold potential SideTracker.potential bCoefficient dCoefficient
  rw [mul_sum,sum_mul,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [SideStability.coordinate_affine]
  ring

theorem zero (p : Config ι) (w : ι → ℝ) : potential p (fun _ => 0) 0 w=0 := by
  rw [affine]
  simp only [mul_zero,sum_const_zero,add_zero]

theorem bBound {p : Config ι} (hp : valid p) (w : ι → ℝ)
    (hw : DomainTransport.domain p.active 11 w) (i : ι) : |bCoefficient p w i| ≤ slope p := by
  have h := input_bound hp (fun j => if j=i then 1 else 0) (fun _ => 0) w 0 0 hw
  rw [zero,affine] at h
  simpa only [mul_zero,add_zero,sub_zero,abs_ite,abs_one,abs_zero,
    sum_ite_eq',mem_univ,ite_true,mul_ite,mul_one] using h

theorem dBound {p : Config ι} (hp : valid p) (w : ι → ℝ)
    (hw : DomainTransport.domain p.active 11 w) : |dCoefficient p w| ≤ slope p := by
  have h := input_bound hp (fun _ => 0) (fun _ => 0) w 1 0 hw
  rw [zero,affine] at h
  simpa only [mul_zero,sum_const_zero,zero_add,mul_one,sub_zero,abs_zero,abs_one] using h

end UniformKServer.SideLinear

end


end

end OAI
