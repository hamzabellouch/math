import OAI.NumberTheory.TwoPoint.Halasz.HalaszLargeDegrees
import OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentRoot

namespace OAI

/-! The large-height logarithmic Taylor polynomial gains a quadratic
saving in the degree before taking its selected moment root. -/
namespace TwoPointCorrelations

open Finset

theorem halasz_large_log_polynomial : ∃ R₀ : ℕ, ∀ m : ℕ, 8≤m →
    ∀ M : ℕ, 1≤M → ∀ t z N lam : ℝ, (M:ℝ)≤N → N≤z → z≤2*N →
    |t|=N^lam → N^(1/4:ℝ)≤2*(M:ℝ) →
    6*(m:ℝ)-6≤lam → lam≤6*m →
    let k := 12*m
    let r := halaszSelectedMoment k
    let p := 2*r*r
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
      ((32*(r:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)*(halaszLogWeightCost k r)^k)^((p:ℝ)⁻¹)*
        N^(-(m:ℝ)^2/(4*(p:ℝ))) := by
  obtain ⟨R₀,hR⟩ := halasz_selected_double_moment
  refine ⟨R₀,?_⟩
  intro m hm M hM t z N lam hMN hz hzhi ht hscale hlo hhi
  dsimp only
  let k := 12*m
  let r := halaszSelectedMoment k
  let p := 2*r*r
  have hk : 2≤k := by dsimp only [k]; omega
  have hr : 1≤r := halasz_selected_moment_pos hk
  have hp : 0<p := by dsimp only [p]; positivity
  have hMR : 1≤(M:ℝ) := by exact_mod_cast hM
  have hN : 1≤N := hMR.trans hMN
  have hN0 : 0<N := by linarith
  have ht0 : t≠0 := by
    intro ht0
    have hh := Real.rpow_pos_of_pos hN0 lam
    rw [ht0,abs_zero] at ht
    linarith
  have hz0 : z≠0 := by linarith
  have hbase := hR k hk M hM (halaszLogCoefficient t z)
    (halasz_log_coefficient_ne_zero ht0 hz0)
  have hweights := halasz_large_degree_weight_product hm hr hM hN hz hzhi ht hscale hlo hhi
  have hbound := hbase.trans (mul_le_mul_of_nonneg_left hweights (by positivity))
  let A := (32*(r:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)
  let D := (halaszLogWeightCost k r)^k
  have hexp : 4*(r:ℝ)^2=((2*p:ℕ):ℝ) := by
    dsimp only [p]
    push_cast
    ring
  have hbound' :
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^p ≤
      A*(M:ℝ)^(((2*p:ℕ):ℝ)+(k:ℝ)^2/1024)*D*
        N^(-(((2*m+1:ℕ):ℝ)*((m:ℝ)-6))) := by
    convert hbound using 1
    dsimp only [A,D,k,r]
    rw [hexp]
    ring_nf
  have hmargin : (k:ℝ)^2/1024-((2*m+1:ℕ):ℝ)*((m:ℝ)-6)≤ -(m:ℝ)^2/4 := by
    have hh := halasz_large_degree_margin (by exact_mod_cast hm : (8:ℝ)≤m)
    dsimp only [k]
    push_cast
    nlinarith only [hh]
  have hh := halasz_moment_transfer hp (by positivity)
    (show 0≤A by dsimp only [A]; positivity)
    (show 0≤D by dsimp only [D]; exact pow_nonneg (halasz_log_weight_cost_pos _ _).le _)
    hMR hMN (by positivity : (0:ℝ)≤(k:ℝ)^2/1024) hmargin hbound'
  convert hh using 1
  congr 1
  congr 1
  ring

end TwoPointCorrelations

end OAI
