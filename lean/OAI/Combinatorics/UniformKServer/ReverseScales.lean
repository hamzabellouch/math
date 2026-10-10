import Mathlib
import OAI.Combinatorics.UniformKServer.GeometricMass

namespace OAI

noncomputable section
                                    
section

/-! Finite geometric scale reversal for the pilot finance theorem. -/
namespace UniformKServer.GeometricMass
open Finset

theorem radius_reverse (R q : ℝ) (hq : q≠0) (J j : ℕ) (hj : j<J) :
    radius R q (J-1-j)=(R*q^J)*(q⁻¹)^j := by
  have he : J-1-j+1+j=J := by omega
  unfold radius
  have hp : q^J=q^(J-1-j+1)*q^j := by rw [←pow_add,he]
  rw [hp,inv_pow]
  have hqj : q^j≠0 := pow_ne_zero _ hq
  field_simp

 theorem reverse_sum {M : Type*} [AddCommMonoid M] (f : ℕ→M) (J : ℕ) :
    (∑ j∈range J, f (J-1-j))=∑ j∈range J, f j := sum_range_reflect f J

end UniformKServer.GeometricMass

end


end

end OAI
