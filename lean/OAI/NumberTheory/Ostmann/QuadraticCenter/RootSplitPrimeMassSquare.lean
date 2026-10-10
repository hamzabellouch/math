import OAI.NumberTheory.Ostmann.QuadraticCenter.RootSplitPrimeMassBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem realCutoff_prime_log_lower {Q : ℝ} (hQ : 1≤Q) :
    Real.log Q-(Real.log 4+4) ≤ ∑ p ∈ (⌊Q⌋₊).primesLE, Real.log p/(p:ℝ) := by
  have hset : (Finset.Ioc 0 ⌊Q⌋₊).filter Nat.Prime=(⌊Q⌋₊).primesLE := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Ioc,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,hpQ⟩,hp⟩; exact ⟨hpQ,hp⟩
    · rintro ⟨hpQ,hp⟩; exact ⟨⟨hp.pos,hpQ⟩,hp⟩
  have hh := (abs_le.mp (Erdos970.Mertens.sum_log_prime_div_eq_log hQ)).1
  rw [hset] at hh
  linarith

theorem remaining_prime_log_lower {M : ℕ} (hM : 1≤M) {X Q : ℝ}
    (hX : 1≤Real.log X) (hQ : 1≤Q) (hsize : Real.log M≤4*Real.log X) :
    Real.log Q-Real.log (Real.log X)-(2*(Real.log 4+4)+4) ≤
      ∑ p ∈ (⌊Q⌋₊).primesLE.filter (fun p=>¬p∣M),Real.log p/(p:ℝ) := by
  classical
  let P := (⌊Q⌋₊).primesLE
  have hremoved := Dirichlet.sum_prime_divisor_log_weight_le
    (P.filter (fun p=>p∣M)) M hM
    (fun p hp=>(Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2)
    (fun p hp=>(Finset.mem_filter.mp hp).2) hX
  have hquot : Real.log M/Real.log X≤4 :=
    (div_le_iff₀ (by linarith : 0<Real.log X)).mpr hsize
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p=>p∣M)
    (fun p:ℕ=>Real.log p/(p:ℝ))
  have hfull := realCutoff_prime_log_lower hQ
  change Real.log Q-(Real.log 4+4)≤∑p∈P,Real.log p/(p:ℝ) at hfull
  change Real.log Q-Real.log (Real.log X)-(2*(Real.log 4+4)+4)≤
    ∑p∈P.filter (fun p=>¬p∣M),Real.log p/(p:ℝ)
  linarith

theorem eventually_square_rootSplitPrimeMass_lower :
    ∀ᶠ X : ℝ in atTop, ∀ eta : ℝ, 0≤eta → eta≤1/1000 →
      ∀ n : ℤ, IsSquare n → ∀ m : ℕ, 1≤4*m*n.natAbs →
        Real.log (4*m*n.natAbs:ℕ)≤4*Real.log X →
        (3/100:ℝ)*Real.log X≤rootSplitPrimeMass n m (X^(1/2-5*eta:ℝ)) := by
  have hsmall := Real.tendsto_log_atTop.eventually
    (Dirichlet.eventually_log_add_le_linear (2*(Real.log 4+4)+4)
      (by norm_num : (0:ℝ)<1/10))
  filter_upwards [hsmall,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℝ)] with X hs hlog hX
  intro eta heta0 heta n hn m hM hsize
  have he : 0≤(1/2-5*eta:ℝ) := by linarith
  have hQ : 1≤X^(1/2-5*eta:ℝ) := Real.one_le_rpow hX he
  have hh := remaining_prime_log_lower hM hlog hQ hsize
  rw [←rootSplitPrimeMass_square n hn m,Real.log_rpow (by linarith : 0<X)] at hh
  change Real.log (Real.log X)+(2*(Real.log 4+4)+4)≤(1/10:ℝ)*Real.log X at hs
  have hm := mul_le_mul_of_nonneg_right heta (by linarith : 0≤Real.log X)
  nlinarith

end Ostmann.QuadraticCenter

end

end OAI
