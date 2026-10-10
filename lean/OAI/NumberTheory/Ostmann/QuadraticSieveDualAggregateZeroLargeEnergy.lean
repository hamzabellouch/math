import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateGrowth
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateNormBlocks

namespace OAI

namespace Ostmann.QuadraticSieve

lemma dual_zero_large_root_energy {C N δ E : ℝ} (hC : 0<C) (hN : 0<N) (hE : 0≤E) :
    Real.sqrt (C*N^(2*δ)*E*E)=Real.sqrt C*N^δ*E := by
  have hp : N^(2*δ)=(N^δ)^2 := by
    rw [mul_comm (2:ℝ),Real.rpow_mul hN.le,Real.rpow_two]
  rw [hp,show C*(N^δ)^2*E*E=C*(N^δ*E)^2 by ring,
    Real.sqrt_mul hC.le,Real.sqrt_sq (by positivity)]
  ring

end Ostmann.QuadraticSieve

end OAI
