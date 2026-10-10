import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchUniform

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open PhysicalPotential

theorem horizon_error {N : ℝ} (hN : 0 < N) :
    (2*N)/(2*N^2)+5*(2*N^2)*Real.exp (-(2*N)/2) ≤ 61/N := by
  have he := Real.pow_div_factorial_le_exp N hN.le 3
  norm_num at he
  have ht : 5*(2*N^2)*Real.exp (-(2*N)/2) ≤ 60/N := by
    rw [show -(2*N)/2 = -N by ring,Real.exp_neg]
    apply (le_div_iff₀ hN).mpr
    have he' : N^3 ≤ 6*Real.exp N := by linarith only [he]
    have he'' := mul_le_mul_of_nonneg_right he' (inv_nonneg.mpr (Real.exp_pos N).le)
    rw [mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero N), mul_one] at he''
    nlinarith only [he'']
  have hid : (2*N)/(2*N^2)=1/N := by field_simp
  rw [hid]
  calc
    _ ≤ 1/N+60/N := add_le_add le_rfl ht
    _ = _ := by ring

theorem exists_grid_horizon {τ : ℝ} (hτ : 0 < τ) (D₀ : ℕ) :
    ∃ Δ : ℕ, ∃ Λ g : ℝ, D₀ ≤ Δ ∧ Even Δ ∧ 0 < Δ ∧ 0 < Λ ∧
      0 < g ∧ g ≤ 1 ∧ g*(Δ:ℝ)=1 ∧
      Λ*g+5*(Δ:ℝ)*Real.exp (-Λ/2) ≤ τ/2 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (max (D₀:ℝ) (122/τ)))
  have hn1 : 1 < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0:ℝ) < n := by linarith only [hn1]
  have hnD : D₀ ≤ n := by
    have h : (D₀:ℝ) < n := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
    exact_mod_cast h.le
  have hne : n ≠ 0 := by exact_mod_cast ne_of_gt hn0
  have hnτ : 122/τ < n := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hsmall : 61/(n:ℝ) ≤ τ/2 := by
    apply (div_le_iff₀ hn0).mpr
    have ht := (div_lt_iff₀ hτ).mp hnτ
    linarith only [ht]
  refine ⟨2*n^2,2*(n:ℝ),1/(2*(n:ℝ)^2),?_,?_,by positivity,by positivity,
    by positivity,?_,?_,?_⟩
  · exact hnD.trans (by nlinarith only [sq_nonneg (n-1)])
  · exact even_two_mul _
  · exact (div_le_one (by positivity)).mpr (by nlinarith only [hn1])
  · push_cast
    field_simp
  · push_cast
    simpa only [div_eq_mul_inv, one_mul] using (horizon_error hn0).trans hsmall

theorem exists_time_step {Λ r : ℝ} (hΛ : 0 < Λ) (hr : 0 < r) :
    ∃ T : ℕ, ∃ h : ℝ, 0 < T ∧ 0 < h ∧ h ≤ r ∧ (T:ℝ)*h=Λ := by
  obtain ⟨T,hT⟩ := exists_nat_gt (max 0 (Λ/r))
  have hT0 : (0:ℝ) < T := lt_of_le_of_lt (le_max_left _ _) hT
  have hTr : Λ/r < T := lt_of_le_of_lt (le_max_right _ _) hT
  refine ⟨T,Λ/T,by exact_mod_cast hT0,div_pos hΛ hT0,?_,?_⟩
  · apply (div_le_iff₀ hT0).mpr
    have := (div_lt_iff₀ hr).mp hTr
    linarith only [this]
  · field_simp

structure Parameters (τ : ℝ) where
  Δ : ℕ
  g : ℝ
  h : ℝ
  φ : ℝ
  b : ℝ
  T : ℕ
  Δpos : 0 < Δ
  gpos : 0 < g
  gle : g ≤ 1
  unit : g*(Δ:ℝ)=1
  hpos : 0 < h
  hle : h ≤ 1
  φpos : 0 < φ
  φle : φ ≤ 1
  bpos : 0 < b
  probability : (1+φ)*(2*h*g) ≤ 1
  small : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g
  survival : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1
  count : 8*(2*h*g)*(Δ:ℝ) ≤ φ*g
  error : (T:ℝ)*h*g+(T:ℝ)*batchConstant Δ*h*(φ+h)*(Δ:ℝ)+
    5*(Δ:ℝ)*Real.exp (-(T:ℝ)*h/2) ≤ τ
  failure : (T:ℝ)*(96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g)) ≤ τ

 theorem exists_parameters {τ : ℝ} (hτ : 0 < τ) (D₀ : ℕ) :
    ∃ p : Parameters τ, D₀ ≤ p.Δ ∧ Even p.Δ := by
  obtain ⟨Δ,Λ,g,hD,heven,hΔ,hΛ,hg,hg1,hunit,hgrid⟩ := exists_grid_horizon hτ D₀
  have hΔr : (0:ℝ) < Δ := by exact_mod_cast hΔ
  have hC : 0 < batchConstant Δ := by unfold batchConstant; positivity
  let φ := min 1 (τ/(4*Λ*batchConstant Δ*(Δ:ℝ)))
  have hφ : 0 < φ := lt_min (by norm_num) (by positivity)
  have hφ1 : φ ≤ 1 := min_le_left _ _
  have hφτ : 4*Λ*batchConstant Δ*(Δ:ℝ)*φ ≤ τ := by
    have ht := (le_div_iff₀ (by positivity : 0 < 4*Λ*batchConstant Δ*(Δ:ℝ))).mp (min_le_right 1 (τ/(4*Λ*batchConstant Δ*(Δ:ℝ))))
    nlinarith only [ht]
  let D : ℝ := 16*((Δ^2+Δ:ℕ):ℝ)+10
  let K : ℝ := 2*g*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ))
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  let r := min (1/4) (min φ (min (savingsFraction g/D) (min (1/K) (φ/(16*(Δ:ℝ))))))
  have hr : 0 < r := by
    apply lt_min (by norm_num)
    apply lt_min hφ
    apply lt_min (div_pos (savingsFraction_pos hg) hDpos)
    exact lt_min (by positivity) (by positivity)
  obtain ⟨T,h,hT,hh,hr',hTh⟩ := exists_time_step hΛ hr
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  have hh4 : h ≤ 1/4 := hr'.trans (min_le_left _ _)
  have hrest := hr'.trans (min_le_right _ _)
  have hhφ : h ≤ φ := hrest.trans (min_le_left _ _)
  have hrest' := hrest.trans (min_le_right _ _)
  have hhD : h ≤ savingsFraction g/D := hrest'.trans (min_le_left _ _)
  have hrest'' := hrest'.trans (min_le_right _ _)
  have hhK : h ≤ 1/K := hrest''.trans (min_le_left _ _)
  have hhΔ : h ≤ φ/(16*(Δ:ℝ)) := hrest''.trans (min_le_right _ _)
  let b := τ*((2*h*g)*φ^2*g)/(96*(Δ:ℝ)^2*(T:ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have hprob : (1+φ)*(2*h*g) ≤ 1 := by
    have hp : 1+φ ≤ 2 := by linarith only [hφ1]
    have htwo : 2*h*g ≤ 1/2 := by
      exact (mul_le_of_le_one_right (by positivity) hg1).trans (by linarith only [hh4])
    have := mul_le_mul hp htwo (by positivity : 0 ≤ 2*h*g) (by norm_num : (0:ℝ) ≤ 2)
    norm_num at this
    exact this
  have hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g := by
    have := (le_div_iff₀ hDpos).mp hhD
    dsimp only [D] at this
    nlinarith only [this]
  have hsurv : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1 := by
    have := (le_div_iff₀ hKpos).mp hhK
    dsimp only [K] at this
    nlinarith only [this]
  have hcount : 8*(2*h*g)*(Δ:ℝ) ≤ φ*g := by
    have ht := (le_div_iff₀ (by positivity : 0 < 16*(Δ:ℝ))).mp hhΔ
    have := mul_le_mul_of_nonneg_right ht hg.le
    nlinarith only [this]
  have he : (T:ℝ)*h*g+(T:ℝ)*batchConstant Δ*h*(φ+h)*(Δ:ℝ)+
      5*(Δ:ℝ)*Real.exp (-(T:ℝ)*h/2) ≤ τ := by
    have hc := mul_le_mul_of_nonneg_left hhφ (show 0 ≤ Λ*batchConstant Δ*(Δ:ℝ) by positivity)
    have ht : Λ*batchConstant Δ*(φ+h)*(Δ:ℝ) ≤ τ/2 := by
      nlinarith only [hc,hφτ]
    have heq : (T:ℝ)*batchConstant Δ*h*(φ+h)*(Δ:ℝ)=Λ*batchConstant Δ*(φ+h)*(Δ:ℝ) := by
      rw [show (T:ℝ)*batchConstant Δ*h=(T:ℝ)*h*batchConstant Δ by ring,hTh]
    rw [heq,mul_assoc (T:ℝ) h g,← mul_assoc,hTh,
      show -(T:ℝ)*h/2 = -Λ/2 by rw [neg_mul,hTh]]
    linarith only [ht,hgrid]
  have hf : (T:ℝ)*(96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g))=τ := by
    dsimp only [b]
    field_simp
  exact ⟨⟨Δ,g,h,φ,b,T,hΔ,hg,hg1,hunit,hh,by linarith only [hh4],hφ,hφ1,hb,
    hprob,hsmall,hsurv,hcount,he,hf.le⟩,hD,heven⟩

end MetricKMedian.FixedBatch
end
end

end OAI
