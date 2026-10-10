import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylWitnessLift
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericWitnessAlgebra
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericWitnessGeometry
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericWitnessScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_centered_quadratic_small_integer_witness (epsilon0 : ℝ)
    (hepsilon0 : 0 < epsilon0) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ,
      2 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      1 ≤ L → (L:ℝ) ≤ (Z:ℝ)^(1/50:ℝ) →
      ∀ (ι : Type*) [Fintype ι] (p : ι → ℕ) [∀ i,NeZero (p i)] [NeZero (∏ i,p i)],
      (∀ i,(p i).Prime) → ∀ (hcop : Pairwise (fun i j => (p i).Coprime (p j))),
      ∀ (S : ∀ i,Finset (ZMod (p i))) (mInv : ZMod (∏ i,p i)) (s v M : ℕ),
      1 ≤ s → 1 ≤ v → 0 < M → s ≤ L^4 → v ∣ L → (∏ i,p i) ∣ L →
      ∀ X : ℝ, 0 < X → (Z:ℝ)^10 ≤ (M:ℝ)/X → (M:ℝ)/X ≤ (Z:ℝ)^13 →
      ∀ h t : ℤ,
      Real.sqrt ((2:ℝ)^Fintype.card ι)*Real.exp (-(auxiliaryK Z z:ℝ)) ≤
        ‖centeredQuadraticSum p hcop
          S mInv s v 1 ((M:ℝ)/X) h ((t:ℝ)/(M:ℝ))‖ →
      ∃ (a : ℕ) (n : ℤ), 1 ≤ a ∧ (a:ℝ) ≤ (Z:ℝ)^(3/25+epsilon0) ∧
        |(n:ℝ)| ≤ X*(Z:ℝ)^(3/25+epsilon0) ∧
        ∀ (ell : ℕ) (tp : ℤ), (ell:ℤ) ∣ (M:ℤ) → (ell:ℤ) ∣ t-tp →
          (ell:ℤ) ∣ n-(a:ℤ)*tp := by
  have hC := cutoffFourierBound_pos
  have hQ := eventually_auxiliary_exp_cost 2 8 epsilon0 (by norm_num) (by norm_num) hepsilon0
  have hN := eventually_auxiliary_exp_cost (100*cutoffFourierBound^2) 10 epsilon0
    (by positivity) (by norm_num) hepsilon0
  filter_upwards [eventually_numeric_witness_scales,hQ,hN] with T hscales hQ hN
  intro Z z L hZ hZl hZu hz hzl hzu hL hLZ ι _ p _ _ hp hcop S mInv s v M hs hv hM hsL hvL hdL
    X hX hRlo hRhi h t hlarge
  let d : ℕ := ∏ i,p i
  let N : ℝ := Real.sqrt (((M:ℝ)/X)/((s:ℝ)*v/d))
  let Y : ℝ := N/d
  let K : ℝ := auxiliaryK Z z
  have hZr : (2:ℝ) ≤ Z := by exact_mod_cast hZ
  have hZp : (0:ℝ) < Z := by linarith
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hsr : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hvr : (1:ℝ) ≤ v := by exact_mod_cast hv
  have hdn : 1 ≤ d := Nat.pos_of_neZero d
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hdn
  have hvL' : (v:ℝ) ≤ L := by exact_mod_cast Nat.le_of_dvd (by omega : 0<L) hvL
  have hdL' : (d:ℝ) ≤ L := by exact_mod_cast Nat.le_of_dvd (by omega : 0<L) hdL
  have hsL' : (s:ℝ) ≤ (L:ℝ)^4 := by exact_mod_cast hsL
  have hg : 0 < Y ∧ Y^2 = ((M:ℝ)/X)/((s:ℝ)*v*d) ∧ (Z:ℝ) ≤ Y ∧
      Real.log Y ≤ 7*Real.log Z ∧ (s:ℝ)*v*d ≤ (Z:ℝ)^(3/25:ℝ) :=
    numeric_witness_scale_geometry hZr hLr hsr hvr hdr hsL' hvL' hdL' hLZ hRlo hRhi
  have hscale := hscales Z z (by omega) hZl hZu hz hzl hzu Y hg.2.2.1 hg.2.2.2.1
  have hdN : (d:ℝ) ≤ N := by
    have hY1 : 1 ≤ Y := (show (1:ℝ) ≤ Z by linarith).trans hg.2.2.1
    have hdpos : (0:ℝ) < d := by linarith
    simpa only [one_mul] using (le_div_iff₀ hdpos).mp hY1
  obtain ⟨q,n,hq,hqB,hn,hincidence⟩ := centered_quadratic_witness_lift p hp hcop S mInv s v M hM
    ((M:ℝ)/X) h t (Real.exp (-K)) (Real.exp (8*K)) hdN
    hscale.1 hscale.2.1 hscale.2.2.1 hscale.2.2.2.1 hscale.2.2.2.2 hlarge
  have hqCost := hQ Z z (by omega) hZl hZu hz hzl hzu
  have hnCost := hN Z z (by omega) hZl hZu hz hzl hzu
  have hqBound : (q:ℝ) ≤ (Z:ℝ)^epsilon0 := hqB.trans hqCost
  have hSpos : 0 < (s:ℝ)*v*d := by positivity
  have hprod : (Z:ℝ)^epsilon0*(Z:ℝ)^(3/25:ℝ) = (Z:ℝ)^(3/25+epsilon0) := by
    rw [← Real.rpow_add hZp]
    congr 1
    ring
  refine ⟨q*s*v*d,n,?_,?_,?_,hincidence⟩
  · have hqpos : 0 < q := by omega
    have hspos : 0 < s := by omega
    have hvpos : 0 < v := by omega
    have hdpos : 0 < d := by omega
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · push_cast
    calc
      (q:ℝ)*s*v*d = (q:ℝ)*((s:ℝ)*v*d) := by ring
      _ ≤ (Z:ℝ)^epsilon0*(Z:ℝ)^(3/25:ℝ) :=
        mul_le_mul hqBound hg.2.2.2.2 hSpos.le (Real.rpow_nonneg hZp.le _)
      _ = _ := hprod
  · change |(n:ℝ)| ≤ (M:ℝ)*Real.exp (8*K)/(Y*(Real.exp (-K)/(10*cutoffFourierBound)))^2 at hn
    rw [numeric_witness_numerator_identity hX hSpos hg.1 hC hg.2.1] at hn
    calc
      |(n:ℝ)| ≤ 100*cutoffFourierBound^2*X*((s:ℝ)*v*d)*Real.exp (10*K) := hn
      _ = X*((100*cutoffFourierBound^2*Real.exp (10*K))*((s:ℝ)*v*d)) := by ring
      _ ≤ X*((Z:ℝ)^epsilon0*(Z:ℝ)^(3/25:ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hnCost hg.2.2.2.2 hSpos.le (Real.rpow_nonneg hZp.le _)) hX.le
      _ = _ := by rw [hprod]

end Ostmann.QuadraticCenter

end

end OAI
