import OAI.NumberTheory.JointDickman.Counting.FiniteWeightedCoefficient
import OAI.NumberTheory.JointDickman.Counting.HighCofactorWindow

namespace OAI

/-! # The finite-weight cofactor window outside bounded frequencies -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

theorem finite_weight_count_window_logarithmic {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, ∃ K : ℕ, 0 < T ∧ 2 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c →
        p^k ≤ ⌊(2*N:ℝ)/a⌋₊ → f (p^k) = 1) →
      (∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n → f ((∏ p ∈ D,p)*n) = f n) →
      ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c < (p:ℝ) ∧
        (p:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ)) → Disjoint E P →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 3*(Real.log (⌊(N:ℝ)/a⌋₊:ℝ))^8 →
        ‖mrtCofactorPolynomial P (finiteWeightedCoefficient f E w) N a t‖ ≤ ε := by
  obtain ⟨T,hT,hprefix⟩ := finite_weight_count_prefix hc hc1 E hE (show 0<ε/5 by positivity)
  obtain ⟨K,hK⟩ := eventually_atTop.mp hprefix
  refine ⟨T,max K 2,hT,le_max_right _ _,?_⟩
  intro N a ha hm f hf hfb hsmall hinv P hP hdis w hw t htlo hthi
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hmr : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm2r : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hx : 2 ≤ (N:ℝ)/a := hm2r.trans (Nat.floor_le (by positivity))
  have hb := mrt_cofactor_bound_of_prefix P (finiteWeightedCoefficient f E w) N ha hx t (A := ε/5) (by positivity) (by
    intro k hk
    change k ∈ Icc m n at hk
    obtain ⟨hmk,hkn⟩ := mem_Icc.mp hk
    have hkr : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hkN : K ≤ k := (le_max_left _ _).trans (hm.trans hmk)
    have hknr : (k:ℝ) ≤ n := by exact_mod_cast hkn
    have hsmallk : ∀ p j : ℕ, p.Prime → (p:ℝ) ≤ (k:ℝ)^c → p^j ≤ k → f (p^j) = 1 := by
      intro p j hp hpc hpj
      exact hsmall p j hp (hpc.trans (Real.rpow_le_rpow hkr.le hknr hc.le)) (hpj.trans hkn)
    have hPk : ∀ p ∈ P, p.Prime ∧ (k:ℝ)^c < (p:ℝ)  := by
      intro p hp
      refine ⟨(hP p hp).1,?_⟩
      · exact (Real.rpow_le_rpow hkr.le hknr hc.le).trans_lt (hP p hp).2.1
    have hlogm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    have hlogk : Real.log (m:ℝ) ≤ Real.log (k:ℝ) :=
      Real.log_le_log hmr (by exact_mod_cast hmk)
    have htk : |t| ≤ 3*(Real.log (k:ℝ))^8 := hthi.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogm hlogk 8) (by norm_num))
    have hh := (div_le_iff₀ hkr).mp (hK k hkN f hf hfb hsmallk hinv P hPk hdis w hw t htlo htk)
    simpa only [halaszPowerPhase_eq_conj_twist,finiteWeightedCoefficient,ArithmeticFunction.coe_mk] using hh)
  exact hb.trans_eq (by ring)

end JointDickman

end OAI
