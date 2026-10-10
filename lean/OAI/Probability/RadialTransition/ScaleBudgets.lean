import OAI.Probability.RadialTransition.MultiScale

namespace OAI

noncomputable section
open scoped BigOperators
open Set Filter
namespace RadialTransition

lemma scale_budgets {U C C₀ D K : ℝ} (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hC₀ : 0 < C₀) (hD : 0 < D) :
    ∃ b k l : ℝ, 2 ≤ b ∧ 2*K ≤ b ∧ 0 < k ∧ 0 < l ∧
      (∀ n, (5/4*U+k+l+1)*(∑ j ∈ Finset.range n, scaleTail b j) ≤ 1/8) ∧
      (∀ n, ∑ j ∈ Finset.range n, (2*(D*(scaleTail b j)^2)/(l*scaleTail b j)+scaleTail b j*U^2/2) ≤ phaseRadius/2) ∧
      (∀ n, 2*(k+2*(D*(scaleTail b n)^2)/(k*scaleTail b n)+2*C*l/k+phaseRadius)<packingDensity) ∧
      (∀ n, ∑ j ∈ Finset.range n, (D*(scaleTail b j)^2+C₀*scaleTail b j) ≤ pressureRadius/64) := by
  let p := packingDensity
  have hp : 0 < p := packingDensity_pos
  let k := p/16
  let l := k*p/(64*(C+1))
  have hk : 0 < k := by dsimp [k]; positivity
  have hl : 0 < l := by dsimp [l]; positivity
  have hcl : 2*C*l/k ≤ p/32 := by
    dsimp only [l]
    have he : 2*C*(k*p/(64*(C+1)))/k = C*p/(32*(C+1)) := by field_simp; ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0<32*(C+1))).mpr
    nlinarith
  have hgap : 2*(k+2*C*l/k+phaseRadius)<p := by
    dsimp only [k,p,phaseRadius] at *
    linarith
  let S := 5/4*U+k+l+1
  let R := 2*D/l+U^2/2
  let T := D+C₀
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hq : Tendsto (fun b : ℝ => b⁻¹^4) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero : Tendsto (fun b : ℝ => b⁻¹) atTop (nhds 0)).pow 4
  have hs : ∀ᶠ b : ℝ in atTop, S*(2*b⁻¹^4) ≤ 1/8 := by
    have htend : Tendsto (fun b : ℝ => S*(2*b⁻¹^4)) atTop (nhds 0) := by simpa using (hq.const_mul 2).const_mul S
    exact (htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8))).mono (fun _ h => h.le)
  have hr : ∀ᶠ b : ℝ in atTop, R*(2*b⁻¹^4) ≤ phaseRadius/2 := by
    have htend : Tendsto (fun b : ℝ => R*(2*b⁻¹^4)) atTop (nhds 0) := by simpa using (hq.const_mul 2).const_mul R
    exact (htend.eventually (gt_mem_nhds (by have := phaseRadius_pos; positivity : (0:ℝ)<phaseRadius/2))).mono (fun _ h => h.le)
  have ht : ∀ᶠ b : ℝ in atTop, T*(2*b⁻¹^4) ≤ pressureRadius/64 := by
    have htend : Tendsto (fun b : ℝ => T*(2*b⁻¹^4)) atTop (nhds 0) := by simpa using (hq.const_mul 2).const_mul T
    exact (htend.eventually (gt_mem_nhds (by have := pressureRadius_pos; positivity : (0:ℝ)<pressureRadius/64))).mono (fun _ h => h.le)
  have he : ∀ᶠ b : ℝ in atTop, 2*(k+2*D*b⁻¹^4/k+2*C*l/k+phaseRadius)<p := by
    have htend : Tendsto (fun b : ℝ => 2*(k+2*D*b⁻¹^4/k+2*C*l/k+phaseRadius)) atTop
        (nhds (2*(k+2*C*l/k+phaseRadius))) := by
      convert ((((hq.const_mul (2*D)).div_const k).const_add k).add_const (2*C*l/k) |>.add_const phaseRadius).const_mul 2 using 1; simp
    exact htend.eventually (gt_mem_nhds hgap)
  obtain ⟨b,⟨⟨⟨⟨⟨hb,hbK⟩,hbs⟩,hbr⟩,hbt⟩,hbe⟩⟩ :=
    (eventually_ge_atTop (2:ℝ) |>.and (eventually_ge_atTop (2*K)) |>.and hs |>.and hr |>.and ht |>.and he).exists
  refine ⟨b,k,l,hb,hbK,hk,hl,?_,?_,?_,?_⟩
  · intro n
    exact (mul_le_mul_of_nonneg_left (sum_scaleTail_le hb n) hS).trans hbs
  · intro n
    have heq (j : ℕ) : 2*(D*(scaleTail b j)^2)/(l*scaleTail b j)+scaleTail b j*U^2/2=R*scaleTail b j := by
      have ha := scaleTail_pos (by linarith : (0:ℝ)<b) j
      dsimp [R]
      field_simp
    simp_rw [heq,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_scaleTail_le hb n) hR).trans hbr
  · intro n
    have ha := scaleTail_pos (by linarith : (0:ℝ)<b) n
    have heq : 2*(D*(scaleTail b n)^2)/(k*scaleTail b n)=2*D*scaleTail b n/k := by field_simp
    rw [heq]
    have hbound := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (scaleTail_le (by linarith : (1:ℝ)≤b) n) (by positivity : (0:ℝ)≤2*D)) hk.le
    linarith
  · intro n
    have hpoint (j : ℕ) : D*(scaleTail b j)^2+C₀*scaleTail b j ≤ T*scaleTail b j := by
      have ha := scaleTail_pos (by linarith : (0:ℝ)<b) j
      have ha1 := scaleTail_le_one (by linarith : (1:ℝ)≤b) j
      dsimp [T]
      nlinarith [mul_nonneg hD.le (show 0 ≤ scaleTail b j*(1-scaleTail b j) by positivity)]
    apply le_trans (Finset.sum_le_sum (fun j _ => hpoint j))
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_scaleTail_le hb n) hT).trans hbt

end RadialTransition
end

end OAI
