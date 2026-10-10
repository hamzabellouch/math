import OAI.NumberTheory.Ostmann.Dirichlet.ContourZeroCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators

theorem contour_zero_multiplicity_polynomial {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {T : ℝ} (hT : 2 ≤ T)
    (S : Finset ℂ) (hS : ∀ rho ∈ S, 1/4 ≤ rho.re ∧ rho.re ≤ 1 ∧ |rho.im| ≤ T+1) :
    (∑ rho ∈ S, (zeroMultiplicity chi rho:ℝ)) ≤
      (128000000*absoluteZetaTwo)*((q:ℝ)*(T+2))^5 := by
  have h := contour_zero_multiplicity_le chi hchi (by linarith) S (fun rho hr => by
    obtain ⟨hre,hre1,him⟩ := hS rho hr
    exact ⟨by linarith,hre1,by linarith⟩)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq4 : (q:ℝ) ≤ (q:ℝ)^4 := le_self_pow₀ hq (by norm_num)
  have hshift : (T+4)^4 ≤ (2*(T+2))^4 := by gcongr; linarith
  have hZ : 0 ≤ absoluteZetaTwo := zero_le_one.trans one_le_absoluteZetaTwo
  have hR : 1 ≤ (q:ℝ)*(T+2) := by
    calc
      1 ≤ 1*1 := by norm_num
      _ ≤ (q:ℝ)*(T+2) := mul_le_mul hq (by linarith) (by norm_num) (by positivity)
  have hp : ((q:ℝ)*(T+2))^4 ≤ ((q:ℝ)*(T+2))^5 := pow_le_pow_right₀ hR (by norm_num)
  calc
    _ ≤ 8000000*absoluteZetaTwo*q*(T+4)^4 := h
    _ ≤ 8000000*absoluteZetaTwo*q*(2*(T+2))^4 := by gcongr
    _ = (128000000*absoluteZetaTwo*(T+2)^4)*(q:ℝ) := by ring
    _ ≤ (128000000*absoluteZetaTwo*(T+2)^4)*(q:ℝ)^4 :=
      mul_le_mul_of_nonneg_left hq4 (by positivity)
    _ = (128000000*absoluteZetaTwo)*((q:ℝ)*(T+2))^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end Ostmann.Dirichlet

end OAI
