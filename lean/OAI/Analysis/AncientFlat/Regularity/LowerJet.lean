import OAI.Analysis.AncientFlat.Regularity.BallInterpolation

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff
namespace ParabolicInterpolation
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma lower_jet_bound (j : ℕ) (hj : j≤3) (f : V → E) (hf : ContDiff ℝ 4 f)
    (x : V) (R q U M : ℝ) (hq : 0<q) (hU : 0≤U) (hM : 0≤M)
    (hx : ‖x‖+6*q<R) (hu : ∀ y, ‖y‖<R → ‖f y‖≤U)
    (hD : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ 4 f y‖≤M) :
    ‖iteratedFDeriv ℝ j f x‖≤22*(U/q^j+q^(4-j)*M) := by
  obtain ⟨h3,h2,h1⟩ := lower_jet_bounds f hf R q U M hq hU hM hu hD
  interval_cases j
  · rw [norm_iteratedFDeriv_zero]
    have h := hu x (by linarith)
    norm_num
    nlinarith [mul_nonneg (pow_nonneg hq.le 4) hM]
  · have h := h1 x hx
    norm_num at h ⊢
    have h' : 0≤q^3*M := by positivity
    have : 0≤U/q := by positivity
    calc
      _≤22/q*U+6*q^3*M := h
      _≤22*(U/q+q^3*M) := by simp only [div_eq_mul_inv] at *; nlinarith
  · have h := h2 x (by linarith)
    norm_num at h ⊢
    have h' : 0≤q^2*M := by positivity
    have h'' : 0≤U/q^2 := by positivity
    calc
      _≤20/q^2*U+6*q^2*M := h
      _≤22*(U/q^2+q^2*M) := by simp only [div_eq_mul_inv] at *; nlinarith
  · have h := h3 x (by linarith)
    norm_num at h ⊢
    have h' : 0≤q*M := by positivity
    have h'' : 0≤U/q^3 := by positivity
    calc
      _≤8/q^3*U+3*q*M := h
      _≤22*(U/q^3+q*M) := by simp only [div_eq_mul_inv] at *; nlinarith
omit [NormedSpace ℝ V] [CompleteSpace E] in
lemma time_difference_bound (u ut : ℝ → V → E) (s t R M : ℝ)
    (hdt : ∀ r∈uIcc s t, ∀ x, ‖x‖<R → HasDerivAt (fun r => u r x) (ut r x) r)
    (ht : ∀ r∈uIcc s t, ∀ x, ‖x‖<R → ‖ut r x‖≤M) :
    ∀ x, ‖x‖<R → ‖u t x-u s x‖≤|t-s| *M := by
  intro x hx
  have h := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hdt r hr x hx).hasDerivWithinAt)
    (fun r hr => ht r hr x hx) (left_mem_uIcc) (right_mem_uIcc)
  simpa only [Real.norm_eq_abs,mul_comm] using h

lemma time_lower_jet (j : ℕ) (hj : j≤3) (u ut : ℝ → V → E)
    (s t R q M : ℝ) (hq : 0<q) (hM : 0≤M)
    (hs : ContDiff ℝ 4 (u s)) (ht : ContDiff ℝ 4 (u t))
    (hdt : ∀ r∈uIcc s t, ∀ x, ‖x‖<R → HasDerivAt (fun r => u r x) (ut r x) r)
    (hUt : ∀ r∈uIcc s t, ∀ x, ‖x‖<R → ‖ut r x‖≤M)
    (hDs : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ 4 (u s) y‖≤M)
    (hDt : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ 4 (u t) y‖≤M)
    (x : V) (hx : ‖x‖+6*q<R) :
    ‖iteratedFDeriv ℝ j (u t) x-iteratedFDeriv ℝ j (u s) x‖≤
      22*(|t-s| /q^j+2*q^(4-j))*M := by
  have hd : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ 4 (fun y => u t y-u s y) y‖≤2*M := by
    intro y hy
    change ‖iteratedFDeriv ℝ 4 (u t-u s) y‖≤2*M
    rw [iteratedFDeriv_sub ht hs]
    simp only [Pi.sub_apply]
    exact (norm_sub_le _ _).trans (by linarith [hDt y hy,hDs y hy])
  have hb := lower_jet_bound j hj (fun y => u t y-u s y) (ht.sub hs) x R q (|t-s| *M) (2*M)
    hq (by positivity) (by positivity) hx (time_difference_bound u ut s t R M hdt hUt) hd
  change ‖iteratedFDeriv ℝ j (u t-u s) x‖≤_ at hb
  rw [iteratedFDeriv_sub (ht.of_le (by exact_mod_cast hj.trans (by norm_num : 3≤4)))
    (hs.of_le (by exact_mod_cast hj.trans (by norm_num : 3≤4)))] at hb
  simp only [Pi.sub_apply] at hb
  convert hb using 1
  ring
end ParabolicInterpolation

end

end OAI
