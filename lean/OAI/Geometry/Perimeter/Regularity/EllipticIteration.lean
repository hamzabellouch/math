import OAI.Geometry.Perimeter.Regularity.EllipticContraction

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem linear_iteration_scalar {K H a B s Q E E' d : ℝ}
    (hK : 1 ≤ K) (hH : 0 ≤ H) (ha : 0 ≤ a) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hsmall : 32*K^2*a ≤ 1) (hforce : 16*K*B ≤ H)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2*K*H) (hE : E ≤ H^2*s^2)
    (hd0 : 0 ≤ d) (hd : d^2 ≤ K*E)
    (hnext : E' ≤ E/16+K*(a*s*Q+B*s)^2) :
    d ≤ K*H*s ∧ E' ≤ H^2*(s/2)^2 := by
  have hK0 : 0 ≤ K := by linarith
  have hKH : 0 ≤ K*H*s := by positivity
  have hdE := mul_le_mul_of_nonneg_left hE hK0
  have hKK : K ≤ K^2 := by nlinarith
  have hdE' := mul_le_mul_of_nonneg_right hKK (mul_nonneg (sq_nonneg H) (sq_nonneg s))
  have hd' : d ≤ K*H*s := (sq_le_sq₀ hd0 hKH).mp (by nlinarith)
  have hsmallH := mul_le_mul_of_nonneg_right hsmall hH
  have hAQ := mul_le_mul_of_nonneg_left hQ (mul_nonneg hK0 ha)
  have hbase : K*(a*Q+B) ≤ H/8 := by nlinarith
  have hb : K*(a*s*Q+B*s) ≤ H*s/8 := by
    have hh := mul_le_mul_of_nonneg_right hbase hs
    nlinarith
  have hb0 : 0 ≤ K*(a*s*Q+B*s) := by positivity
  have hb2 := pow_le_pow_left₀ hb0 hb 2
  have hb3 := mul_le_mul_of_nonneg_right hKK (sq_nonneg (a*s*Q+B*s))
  refine ⟨hd',?_⟩
  nlinarith [sq_nonneg (H*s)]

theorem linear_energy_iteration {θ δ K a B H R : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hH : 0 ≤ H) (hR : 0 < R)
    (hsmall : 32*K^2*a ≤ 1) (hforce : 16*K*B ≤ H)
    {A : Euc n → Euc n →L[ℝ] Euc n} (hA : Continuous A)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) {F : Euc n → Euc n} (hF : Continuous F)
    (p : Euc n) (h : WeakLinearEquation A f F (Metric.ball p R))
    (hnear : ∀ x∈Metric.ball p R, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖ ≤ δ)
    (hosc : ∀ j x, x∈Metric.ball p (θ^j*R) →
      ‖A p-A x‖ ≤ a*(1/2)^j ∧ ‖F x-F p‖ ≤ B*(1/2)^j)
    (hinit : scaledGradientEnergy f p R 0 ≤ H^2) :
    ∃ q : ℕ → Euc n, q 0=0 ∧
      (∀ j, ‖q j‖ ≤ 2*K*H*(1-(1/2)^j)) ∧
      (∀ j, scaledGradientEnergy f p (θ^j*R) (q j) ≤ H^2*((1/2)^j)^2) ∧
      (∀ j, ‖q (j+1)-q j‖ ≤ K*H*(1/2)^j) := by
  have hball (j : ℕ) : Metric.ball p (θ^j*R) ⊆ Metric.ball p R :=
    Metric.ball_subset_ball (by nlinarith [pow_le_one₀ (n := j) hθ.le hθ1.le])
  have hstep (j : ℕ) (q : Euc n) : ∃ q' : Euc n,
      ‖q'-q‖^2 ≤ K*scaledGradientEnergy f p (θ^j*R) q ∧
      scaledGradientEnergy f p (θ^(j+1)*R) q' ≤ scaledGradientEnergy f p (θ^j*R) q/16+
        K*(a*(1/2)^j*‖q‖+B*(1/2)^j)^2 := by
    have hh := hc A hA f hf F hF p (θ^j*R) (by positivity) (h.mono (hball j))
      (A p) (F p) q (a*(1/2)^j) (B*(1/2)^j) (by positivity) (by positivity)
      (fun x hx ↦ ⟨hnear x (hball j hx),(hosc j x hx).1,(hosc j x hx).2⟩)
    simpa only [pow_succ, mul_assoc,mul_left_comm,mul_comm] using hh
  choose next hnext using hstep
  let q : ℕ → Euc n := fun j ↦ Nat.rec 0 (fun j z ↦ next j z) j
  have hq0 : q 0=0 := rfl
  have hqnext (j : ℕ) : q (j+1)=next j (q j) := rfl
  have hbounds : ∀ j, ‖q j‖ ≤ 2*K*H*(1-(1/2)^j) ∧
      scaledGradientEnergy f p (θ^j*R) (q j) ≤ H^2*((1/2)^j)^2 ∧
      ‖q (j+1)-q j‖ ≤ K*H*(1/2)^j := by
    intro j
    induction j with
    | zero =>
      have hinit' : scaledGradientEnergy f p (θ^0*R) (q 0) ≤ H^2*((1/2)^0)^2 := by
        simpa only [hq0,pow_zero,one_pow,one_mul,mul_one] using hinit
      obtain ⟨hd,_⟩ := linear_iteration_scalar hK hH ha hB (by positivity : 0 ≤ (1/2:ℝ)^0)
        hsmall hforce (norm_nonneg (q 0)) (by simp only [hq0,norm_zero]; positivity) hinit'
        (norm_nonneg (next 0 (q 0)-q 0)) (hnext 0 (q 0)).1 (hnext 0 (q 0)).2
      exact ⟨by simp only [hq0,norm_zero,pow_zero,sub_self,mul_zero,le_refl],hinit',by simpa only [hqnext] using hd⟩
    | succ j ih =>
      have hqnorm : ‖q j‖ ≤ 2*K*H := ih.1.trans (by
        have hh : 0 ≤ 2*K*H*(1/2)^j := by positivity
        nlinarith)
      obtain ⟨_,hE⟩ := linear_iteration_scalar hK hH ha hB (by positivity : 0 ≤ (1/2:ℝ)^j)
        hsmall hforce (norm_nonneg (q j)) hqnorm ih.2.1
        (norm_nonneg (next j (q j)-q j)) (hnext j (q j)).1 (hnext j (q j)).2
      have hE' : scaledGradientEnergy f p (θ^(j+1)*R) (q (j+1)) ≤ H^2*((1/2)^(j+1))^2 := by
        simpa only [hqnext,pow_succ,div_eq_mul_inv,one_div,one_mul] using hE
      have hn : ‖q (j+1)‖ ≤ 2*K*H*(1-(1/2)^(j+1)) := by
        have htri := norm_add_le (q j) (q (j+1)-q j)
        have he : q j + (q (j+1)-q j) = q (j+1) := by abel
        rw [he] at htri
        rw [pow_succ]
        nlinarith [ih.1,ih.2.2]
      have hn' : ‖q (j+1)‖ ≤ 2*K*H := hn.trans (by
        have hh : 0 ≤ 2*K*H*(1/2)^(j+1) := by positivity
        nlinarith)
      obtain ⟨hd,_⟩ := linear_iteration_scalar hK hH ha hB (by positivity : 0 ≤ (1/2:ℝ)^(j+1))
        hsmall hforce (norm_nonneg (q (j+1))) hn' hE'
        (norm_nonneg (next (j+1) (q (j+1))-q (j+1))) (hnext (j+1) (q (j+1))).1 (hnext (j+1) (q (j+1))).2
      exact ⟨hn,hE',by simpa only [hqnext] using hd⟩
  exact ⟨q,hq0,fun j ↦ (hbounds j).1,fun j ↦ (hbounds j).2.1,fun j ↦ (hbounds j).2.2⟩

end RPISingularHarnack

end

end OAI
