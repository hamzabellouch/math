import Mathlib.Analysis.SpecificLimits.Normed
import OAI.Analysis.Laughlin.Operators.PhysicalCoupling
import OAI.Analysis.Laughlin.Spin.DescendantNorm

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem affine_spin_tendsto (a c : ℕ) (ha : 0 < a) :
    Tendsto (fun Q : ℕ => a*Q-c) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k+c)] with Q hQ
  have hm : Q ≤ a*Q := by
    simpa using Nat.mul_le_mul_right Q (show 1 ≤ a by omega)
  omega

theorem affine_spin_fraction_tendsto (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun Q : ℕ => ((b*Q-d : ℕ) : ℝ)/(((a*Q-c : ℕ) : ℝ)+((b*Q-d : ℕ) : ℝ)))
      atTop (𝓝 ((b : ℝ)/((a : ℝ)+b))) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have ht : Tendsto (fun Q : ℕ => (-(d : ℝ)+(b : ℝ)*Q)/
      (-(c : ℝ)-(d : ℝ)+((a : ℝ)+b)*Q)) atTop (𝓝 ((b : ℝ)/((a : ℝ)+b))) :=
    tendsto_add_mul_div_add_mul_atTop_nhds (-(d : ℝ)) (-(c : ℝ)-(d : ℝ)) (b : ℝ) (by positivity)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (c+d)] with Q hQ
  have hmA : Q ≤ a*Q := by simpa using Nat.mul_le_mul_right Q (show 1 ≤ a by omega)
  have hmB : Q ≤ b*Q := by simpa using Nat.mul_le_mul_right Q (show 1 ≤ b by omega)
  rw [Nat.cast_sub (by omega : c ≤ a*Q),Nat.cast_sub (by omega : d ≤ b*Q)]
  push_cast
  congr 1 <;> ring

theorem genericUnitDescendant_threeBody (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    genericUnitDescendant (2*Q-2) Q z (by omega) hz n =
      normalizedCoupledDescendant Q z hQ hz n := by rfl

theorem source_threeBody_coupling_tendsto (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient (2*Q-2) Q z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p)) := by
  have hA := affine_spin_tendsto 2 2 (by omega)
  have hB : Tendsto (fun Q : ℕ => Q) atTop atTop := tendsto_id
  have hf : Tendsto (fun Q : ℕ => (Q : ℝ)/(((2*Q-2 : ℕ) : ℝ)+Q)) atTop (𝓝 (1/3 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 2 1 2 0 (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => 2*Q-2) (fun Q => Q) (1/3) hA hB
    (by norm_num) (by norm_num) hf z T p hz hp
  norm_num at hh ⊢
  exact hh

theorem source_fourBody_inner_coupling_tendsto (r T p : ℕ) (hr : r ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient Q Q r T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) r (T-r) p)) := by
  have hf : Tendsto (fun Q : ℕ => (Q : ℝ)/((Q : ℝ)+Q)) atTop (𝓝 (1/2 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 1 1 0 0 (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => Q) (fun Q => Q) (1/2) tendsto_id tendsto_id
    (by norm_num) (by norm_num) hf r T p hr hp
  norm_num at hh ⊢
  exact hh

theorem source_fourBody_outer_coupling_tendsto (r z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient (2*Q-2) (2*Q-2*r) z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z (T-z) p)) := by
  have hf : Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ)/
      (((2*Q-2 : ℕ) : ℝ)+((2*Q-2*r : ℕ) : ℝ))) atTop (𝓝 (1/2 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 2 2 2 (2*r) (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => 2*Q-2) (fun Q => 2*Q-2*r) (1/2)
    (affine_spin_tendsto 2 2 (by omega)) (affine_spin_tendsto 2 (2*r) (by omega))
    (by norm_num) (by norm_num) hf z T p hz hp
  norm_num at hh ⊢
  exact hh

end Laughlin.Spin

end OAI
