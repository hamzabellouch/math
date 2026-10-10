import Mathlib
import OAI.Combinatorics.KMedian.Process.RoundParameters

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch
open PhysicalPotential

theorem exists_rational_grid_horizon {τ : ℝ} (hτ : 0 < τ) (D₀ : ℕ) :
    ∃ Δ : ℕ, ∃ Λ g : ℚ, D₀ ≤ Δ ∧ Even Δ ∧ 0 < Δ ∧ 0 < (Λ:ℝ) ∧
      0 < (g:ℝ) ∧ (g:ℝ) ≤ 1 ∧ (g:ℝ)*(Δ:ℝ)=1 ∧
      (Λ:ℝ)*(g:ℝ)+5*(Δ:ℝ)*Real.exp (-(Λ:ℝ)/2) ≤ τ/2 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (max (D₀:ℝ) (122/τ)))
  have hn1 : 1 < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0:ℝ) < n := by linarith only [hn1]
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hnD : D₀ ≤ n := by
    have hh : (D₀:ℝ) < n := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
    exact_mod_cast hh.le
  have hnτ : 122/τ < n := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hsmall : 61/(n:ℝ) ≤ τ/2 := by
    apply (div_le_iff₀ hn0).mpr
    have ht := (div_lt_iff₀ hτ).mp hnτ
    linarith only [ht]
  refine ⟨2*n^2,2*(n:ℚ),1/(2*(n:ℚ)^2),?_,even_two_mul _,by positivity,?_,?_,?_,?_,?_⟩
  · exact hnD.trans (by nlinarith only [sq_nonneg (n-1)])
  · push_cast; positivity
  · push_cast; positivity
  · push_cast
    exact (div_le_one (by positivity)).mpr (by nlinarith only [hn1])
  · push_cast; field_simp
  · push_cast
    simpa only [div_eq_mul_inv,one_mul] using (horizon_error hn0).trans hsmall

structure RationalParameters (τ : ℝ) where
  Δ : ℕ
  g : ℚ
  h : ℚ
  φ : ℚ
  β : ℚ
  ζ : ℚ
  T : ℕ
  taper : Fin T → ℚ
  Δpos : 0<Δ
  gpos : 0<(g:ℝ)
  gle : (g:ℝ)≤1
  unit : (g:ℝ)*(Δ:ℝ)=1
  hpos : 0<(h:ℝ)
  hle : (h:ℝ)≤1
  φpos : 0<(φ:ℝ)
  φle : (φ:ℝ)≤1
  βpos : 0<(β:ℝ)
  ζpos : 0<(ζ:ℝ)
  ζle : (ζ:ℝ)<1/4
  probability : (1+(φ:ℝ))*(2*(h:ℝ)*(g:ℝ))≤1
  small : (16*((Δ^2+Δ:ℕ):ℝ)+10)*(h:ℝ)≤ savingsFraction (g:ℝ)
  survival : (2*(h:ℝ)*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ))≤1
  count : 8*(2*(h:ℝ)*(g:ℝ))*(Δ:ℝ)≤(φ:ℝ)*(g:ℝ)
  error : (T:ℝ)*(h:ℝ)*((g:ℝ)+12*(ζ:ℝ))+
    (T:ℝ)*batchConstant Δ*(h:ℝ)*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)+
    5*(Δ:ℝ)*Real.exp (-(T:ℝ)*(h:ℝ)/2)≤τ
  failure : (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((2*(h:ℝ)*(g:ℝ))*(φ:ℝ)^2*(g:ℝ)))≤τ
  taper_pos : ∀ t, 0<(taper t:ℝ)
  taper_le : ∀ t, (taper t:ℝ)≤1/2
  taper_error : ∀ t, |(taper t:ℝ)-Analytic.P (Real.exp (-(t.val:ℝ)*(h:ℝ)))|≤(ζ:ℝ)

theorem exists_rational_parameters {τ : ℝ} (hτ : 0<τ) (D₀ : ℕ) :
    ∃ p : RationalParameters τ, D₀≤p.Δ ∧ Even p.Δ := by
  obtain ⟨Δ,Λ,g,hD,heven,hΔ,hΛ,hg,hg1,hunit,hgrid⟩ := exists_rational_grid_horizon hτ D₀
  have hΔr : (0:ℝ)<Δ := by exact_mod_cast hΔ
  have hC : 0<batchConstant Δ := by unfold batchConstant; positivity
  obtain ⟨φ,hφ,hφb⟩ := exists_rat_btwn (show (0:ℝ)< min 1 (τ/(8*(Λ:ℝ)*batchConstant Δ*(Δ:ℝ))) by positivity)
  have hφ1 : (φ:ℝ)≤1 := (hφb.trans_le (min_le_left _ _)).le
  have hφτ : 8*(Λ:ℝ)*batchConstant Δ*(Δ:ℝ)*(φ:ℝ)≤τ := by
    have ht := (le_div_iff₀ (by positivity : 0<8*(Λ:ℝ)*batchConstant Δ*(Δ:ℝ))).mp
      (hφb.trans_le (min_le_right _ _)).le
    nlinarith only [ht]
  let D : ℝ := 16*((Δ^2+Δ:ℕ):ℝ)+10
  let K : ℝ := 2*(g:ℝ)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ))
  have hDpos : 0<D := by dsimp [D]; positivity
  have hKpos : 0<K := by dsimp [K]; positivity
  let r := min (1/4) (min (φ:ℝ) (min (savingsFraction (g:ℝ)/D) (min (1/K) ((φ:ℝ)/(16*(Δ:ℝ))))))
  have hr : 0<r := by
    apply lt_min (by norm_num)
    apply lt_min hφ
    apply lt_min (div_pos (savingsFraction_pos hg) hDpos)
    exact lt_min (by positivity) (by positivity)
  obtain ⟨T,hT⟩ := exists_nat_gt (max 0 ((Λ:ℝ)/r))
  have hTr : (0:ℝ)<T := lt_of_le_of_lt (le_max_left _ _) hT
  let h : ℚ := Λ/T
  have hTh : (T:ℝ)*(h:ℝ)=(Λ:ℝ) := by dsimp only [h]; push_cast; field_simp
  have hh : 0<(h:ℝ) := by dsimp only [h]; push_cast; positivity
  have hhr : (h:ℝ)≤r := by
    have ht := (div_lt_iff₀ hr).mp (lt_of_le_of_lt (le_max_right _ _) hT)
    dsimp only [h]
    push_cast
    apply (div_le_iff₀ hTr).mpr
    linarith only [ht]
  have hh4 : (h:ℝ)≤1/4 := hhr.trans (min_le_left _ _)
  have hrest := hhr.trans (min_le_right _ _)
  have hhφ : (h:ℝ)≤(φ:ℝ) := hrest.trans (min_le_left _ _)
  have hrest' := hrest.trans (min_le_right _ _)
  have hhD : (h:ℝ)≤ savingsFraction (g:ℝ)/D := hrest'.trans (min_le_left _ _)
  have hrest'' := hrest'.trans (min_le_right _ _)
  have hhK : (h:ℝ)≤1/K := hrest''.trans (min_le_left _ _)
  have hhΔ : (h:ℝ)≤(φ:ℝ)/(16*(Δ:ℝ)) := hrest''.trans (min_le_right _ _)
  obtain ⟨β,hβ,hβb⟩ := exists_rat_btwn (show (0:ℝ)<τ*((2*(h:ℝ)*(g:ℝ))*(φ:ℝ)^2*(g:ℝ))/(96*(Δ:ℝ)^2*(T:ℝ)) by positivity)
  obtain ⟨ζ,hζ,hζb⟩ := exists_rat_btwn (show (0:ℝ)< min (1/4) (τ/(48*(Λ:ℝ))) by positivity)
  have hζ1 : (ζ:ℝ)<1/4 := hζb.trans_le (min_le_left _ _)
  have hζτ : 48*(Λ:ℝ)*(ζ:ℝ)≤τ := by
    have ht := (le_div_iff₀ (by positivity : 0<48*(Λ:ℝ))).mp
      (hζb.trans_le (min_le_right _ _)).le
    nlinarith only [ht]
  have hprob : (1+(φ:ℝ))*(2*(h:ℝ)*(g:ℝ))≤1 := by
    have hp : 1+(φ:ℝ)≤2 := by linarith only [hφ1]
    have htwo : 2*(h:ℝ)*(g:ℝ)≤1/2 :=
      (mul_le_of_le_one_right (by positivity) hg1).trans (by linarith only [hh4])
    have ht := mul_le_mul_of_nonneg_right hp (show 0≤2*(h:ℝ)*(g:ℝ) by positivity)
    linarith only [ht,htwo]
  have hsmall : D*(h:ℝ)≤ savingsFraction (g:ℝ) := by
    have ht := (le_div_iff₀ hDpos).mp hhD
    linarith only [ht]
  have hsurv : (2*(h:ℝ)*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ))≤1 := by
    have ht := (le_div_iff₀ hKpos).mp hhK
    dsimp only [K] at ht
    nlinarith only [ht]
  have hcount : 8*(2*(h:ℝ)*(g:ℝ))*(Δ:ℝ)≤(φ:ℝ)*(g:ℝ) := by
    have ht := (le_div_iff₀ (by positivity : 0<16*(Δ:ℝ))).mp hhΔ
    have hhg := mul_le_mul_of_nonneg_right ht hg.le
    nlinarith only [hhg]
  have herr : (T:ℝ)*(h:ℝ)*((g:ℝ)+12*(ζ:ℝ))+
      (T:ℝ)*batchConstant Δ*(h:ℝ)*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)+
      5*(Δ:ℝ)*Real.exp (-(T:ℝ)*(h:ℝ)/2)≤τ := by
    have hc := mul_le_mul_of_nonneg_left hhφ (show 0≤(Λ:ℝ)*batchConstant Δ*(Δ:ℝ) by positivity)
    have ht : (Λ:ℝ)*batchConstant Δ*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)≤τ/4 := by
      nlinarith only [hc,hφτ]
    have heq : (T:ℝ)*batchConstant Δ*(h:ℝ)*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)=
        (Λ:ℝ)*batchConstant Δ*((φ:ℝ)+(h:ℝ))*(Δ:ℝ) := by
      rw [show (T:ℝ)*batchConstant Δ*(h:ℝ)=(T:ℝ)*(h:ℝ)*batchConstant Δ by ring,hTh]
    rw [heq,hTh,show -(T:ℝ)*(h:ℝ)/2=-(Λ:ℝ)/2 by rw [neg_mul,hTh]]
    nlinarith only [ht,hgrid,hζτ]
  have hf : (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((2*(h:ℝ)*(g:ℝ))*(φ:ℝ)^2*(g:ℝ)))≤τ := by
    have hb := (le_div_iff₀ (by positivity : 0<96*(Δ:ℝ)^2*(T:ℝ))).mp hβb.le
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hb]
  have happrox : ∀ t : Fin T, ∃ q : ℚ, 0<(q:ℝ) ∧ (q:ℝ)≤1/2 ∧
      |(q:ℝ)-Analytic.P (Real.exp (-(t.val:ℝ)*(h:ℝ)))|≤(ζ:ℝ) := by
    intro t
    let a := Analytic.P (Real.exp (-(t.val:ℝ)*(h:ℝ)))
    have ha : 0<a := Analytic.P_pos (Real.exp_pos _).le
    have ha1 : a≤1/2 := Analytic.P_le_half (Real.exp_pos _).le
    obtain ⟨q,hql,hqr⟩ := exists_rat_btwn (show max 0 (a-(ζ:ℝ))<a from max_lt ha (by linarith only [hζ]))
    refine ⟨q,(le_max_left _ _).trans_lt hql,hqr.le.trans ha1,?_⟩
    rw [abs_of_neg (sub_neg.mpr hqr)]
    have ht := (le_max_right _ _).trans_lt hql
    linarith only [ht]
  choose taper ht0 ht1 hte using happrox
  exact ⟨⟨Δ,g,h,φ,β,ζ,T,taper,hΔ,hg,hg1,hunit,hh,by linarith only [hh4],hφ,hφ1,hβ,hζ,hζ1,
    hprob,hsmall,hsurv,hcount,herr,hf,ht0,ht1,hte⟩,hD,heven⟩

end MetricKMedian.FixedBatch
end

end OAI
