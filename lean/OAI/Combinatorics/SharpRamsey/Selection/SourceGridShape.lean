import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourcePencilScales
import OAI.Combinatorics.SharpRamsey.Geometry.SparsePencilBounds

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real Finset
open scoped Topology BigOperators
noncomputable section

lemma log_grid_bound {n : ℕ} (hn : 0<n) (q : ℝ) (hq : 0<q) (j : ℕ)
    (h : (n:ℝ)≤2*q^j) :
    (Nat.log 2 n+2:ℕ)*Real.log 2≤3*Real.log 2+(j:ℝ)*Real.log q := by
  have hp : (2:ℝ)^(Nat.log 2 n)≤n := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have hl := Real.log_le_log (show (0:ℝ)<2^(Nat.log 2 n) by positivity) (hp.trans h)
  rw [Real.log_pow,Real.log_mul (by norm_num) (pow_ne_zero _ hq.ne'),Real.log_pow] at hl
  push_cast
  linarith

theorem eventually_grid_shape (d : ℕ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℝ) (j n : ℕ),0<q → Real.log q=σ → j≤d →
      0<n → (n:ℝ)≤2*q^j → (Nat.log 2 n+2:ℕ)≤σ^2 := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop ((d:ℝ)/Real.log 2+3)] with
    σ hσ hσ' q j n hq hlog hj hn hN
  have hh := log_grid_bound hn q hq j hN
  rw [hlog] at hh
  have hd : (j:ℝ)≤d := by exact_mod_cast hj
  have hmul : (d:ℝ)+3*Real.log 2≤σ*Real.log 2 := by
    have hab := mul_le_mul_of_nonneg_right hσ' hl.le
    rw [add_mul,div_mul_cancel₀ _ hl.ne'] at hab
    exact hab
  have hmul' := mul_le_mul_of_nonneg_right hmul (show 0≤σ by linarith)
  have hl' := mul_le_mul_of_nonneg_left hσ (show 0≤3*Real.log 2 by positivity)
  have hd' := mul_le_mul_of_nonneg_right hd (show 0≤σ by linarith)
  apply (mul_le_mul_iff_left₀ hl).mp
  nlinarith

section Geometry
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] in
lemma support_le_projective_power {j : ℕ} (hdim : Module.finrank K V=j+1)
    (S : Finset (Projectivization K V)) :
    (S.card:ℝ)≤2*(Nat.card K:ℝ)^j := by
  have hq : (2:ℝ)≤Nat.card K := by
    have hh : 2≤Nat.card K := Finite.one_lt_card
    exact_mod_cast hh
  have hh : (S.card:ℝ)≤Fintype.card (Projectivization K V) := by exact_mod_cast card_le_univ S
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim] at hh
  push_cast at hh
  exact hh.trans (Incidence.geom_sum_le_twice_pow _ hq j)

end Geometry
end
end SharpLogRamsey.SourceScales

end

end OAI
