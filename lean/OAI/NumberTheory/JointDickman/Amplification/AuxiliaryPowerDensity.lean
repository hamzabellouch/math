import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryBandDensity

namespace OAI

/-! # A power-scale auxiliary band's finite-sieve error vanishes -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma auxiliary_power_boundary_tendsto {β : ℝ} (r : ℕ)
    (hβ : β*(4*r:ℕ)<1) :
    Tendsto (fun X : ℝ => ((2*r+1:ℕ):ℝ)*2^(2*r)*(X^β)^(4*r)/X)
      atTop (𝓝 0) := by
  have hpow := tendsto_rpow_neg_atTop (show 0 < 1-β*(4*r:ℕ) by linarith)
  have hh := hpow.const_mul (((2*r+1:ℕ):ℝ)*2^(2*r))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  rw [← Real.rpow_mul_natCast hX.le,
    show -(1-β*(4*r:ℕ))=β*(4*r:ℕ)-1 by ring,Real.rpow_sub_one hX.ne']
  ring

theorem auxiliary_power_missing : ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧
    ∀ R β : ℝ, 1 ≤ R → 0 < β → ∀ r : ℕ, β*(4*r:ℕ)<1 →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
    ∀ (A N : ℕ) [NeZero N], X ≤ (N:ℝ) →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand (X^(β/R)) (X^β)) (A+j.val)) ≤
        C/R+Real.exp (2*(Real.log R+M))/(2:ℝ)^(2*r+1)+ε := by
  obtain ⟨C,M,hC,hM,hbound⟩ := auxiliary_band_missing_bound
  refine ⟨C,M,hC,hM,?_⟩
  intro R β hR hβ r hsmall ε hε
  have hR0 : 0 < R := by linarith
  have hleft := tendsto_rpow_atTop (div_pos hβ hR0)
  filter_upwards [hleft.eventually (eventually_ge_atTop 2),eventually_gt_atTop (1:ℝ),
    (auxiliary_power_boundary_tendsto r hsmall).eventually (eventually_lt_nhds hε)] with
    X hP hX herr
  intro A N _ hXN
  have hN0 : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  have hPQ : X^(β/R) ≤ X^β := by
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    exact (div_le_self hβ.le hR)
  have hlog : Real.log (X^β)=R*Real.log (X^(β/R)) := by
    rw [Real.log_rpow (by linarith : 0<X),Real.log_rpow (by linarith : 0<X)]
    field_simp
  have hh := hbound (X^(β/R)) (X^β) R hP hPQ hR hlog A N r
  apply hh.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ((2*r+1:ℕ):ℝ)*2^(2*r)*(X^β)^(4*r)/X :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hXN
    _ ≤ ε := herr.le

end JointDickman

end OAI
