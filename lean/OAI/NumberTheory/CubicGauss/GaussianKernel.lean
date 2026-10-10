import Mathlib

namespace OAI

/-! Gaussian lattice decay, shell bounds and integral estimates. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.SieveKernel

lemma norm_weighted_pair_sum {ι : Type*} (s : Finset ι) (f g w : ι → ℂ)
    {C P Q : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ C)
    (hf : ∑ i ∈ s, ‖f i‖^2 ≤ P^2) (hg : ∑ i ∈ s, ‖g i‖^2 ≤ Q^2) :
    ‖∑ i ∈ s, w i * f i * star (g i)‖ ≤ C * P * Q := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun i => ‖g i‖)
  have hc' : (∑ i ∈ s, ‖f i‖ * ‖g i‖)^2 ≤ (P*Q)^2 := by
    apply hc.trans
    calc
      _ ≤ P^2 * Q^2 := mul_le_mul hf hg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg P)
      _ = _ := by ring
  have hn : 0 ≤ ∑ i ∈ s, ‖f i‖ * ‖g i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (_root_.norm_nonneg (f i)) (_root_.norm_nonneg (g i))
  have hc'' := (sq_le_sq₀ hn (mul_nonneg hP hQ)).mp hc'
  calc
    _ ≤ ∑ i ∈ s, ‖w i * f i * star (g i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, C * (‖f i‖ * ‖g i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [norm_mul, norm_star]
      nlinarith [mul_le_mul_of_nonneg_right (hw i hi) (mul_nonneg (_root_.norm_nonneg (f i)) (_root_.norm_nonneg (g i)))]
    _ = C * ∑ i ∈ s, ‖f i‖ * ‖g i‖ := (Finset.mul_sum ..).symm
    _ ≤ C * P * Q := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hc'' hC

abbrev Index := ℕ × (ℕ × ℕ)
def coefficient (r : ℝ) (v : Index) : ℂ :=
  Complex.exp (-(r : ℂ)) * ((r : ℂ)^v.1 / v.1.factorial) *
    ((r : ℂ)^v.2.1 / v.2.1.factorial) * ((-(r : ℂ))^v.2.2 / v.2.2.factorial)

def majorant (L R δ : ℝ) (v : Index) : ℝ :=
  Real.exp (-L) * ((R*δ)^v.1 / v.1.factorial) *
    ((R*δ)^v.2.1 / v.2.1.factorial) * ((R*δ^2)^v.2.2 / v.2.2.factorial)

lemma exp_series_complex (z : ℂ) : HasSum (fun n : ℕ => z^n / n.factorial) (Complex.exp z) := by
  simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z

lemma exp_series_real (z : ℝ) : HasSum (fun n : ℕ => z^n / n.factorial) (Real.exp z) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp z

lemma hasSum_mul_complex {ι κ : Type*} {f : ι → ℂ} {g : κ → ℂ} {a b : ℂ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun v : ι × κ => f v.1 * g v.2) (a*b) := by
  apply hf.mul hg
  exact summable_mul_of_summable_norm (f := f) (g := g) hf.summable.norm hg.summable.norm

lemma hasSum_mul_real {ι κ : Type*} {f : ι → ℝ} {g : κ → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun v : ι × κ => f v.1 * g v.2) (a*b) := by
  apply hf.mul hg
  exact summable_mul_of_summable_norm (f := f) (g := g) hf.summable.norm hg.summable.norm

lemma kernel_hasSum (r x y : ℝ) :
    HasSum (fun v : Index => coefficient r v * (x : ℂ)^(v.1+v.2.2) *
      (y : ℂ)^(v.2.1+v.2.2))
      (Complex.exp (-(r : ℂ)*(1-x)*(1-y))) := by
  have hy := exp_series_complex ((r : ℂ)*y)
  have hxy := exp_series_complex (-(r : ℂ)*x*y)
  have h2 := hasSum_mul_complex hy hxy
  have hx := exp_series_complex ((r : ℂ)*x)
  have h3 := hasSum_mul_complex hx h2
  have h4 := h3.mul_left (Complex.exp (-(r : ℂ)))
  have he : Complex.exp (-(r : ℂ)) *
      (Complex.exp ((r : ℂ)*x) * (Complex.exp ((r : ℂ)*y) * Complex.exp (-(r : ℂ)*x*y))) =
      Complex.exp (-(r : ℂ)*(1-x)*(1-y)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [he] at h4
  exact h4.congr_fun fun v => by simp only [coefficient, pow_add, mul_pow]; ring

lemma majorant_hasSum (L R δ : ℝ) :
    HasSum (majorant L R δ) (Real.exp (-L+(2*δ+δ^2)*R)) := by
  have h1 := exp_series_real (R*δ)
  have h2 := exp_series_real (R*δ^2)
  have h3 := hasSum_mul_real h1 h2
  have h4 := hasSum_mul_real h1 h3
  have h5 := h4.mul_left (Real.exp (-L))
  have he : Real.exp (-L)*(Real.exp (R*δ)*(Real.exp (R*δ)*Real.exp (R*δ^2))) =
      Real.exp (-L+(2*δ+δ^2)*R) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he] at h5
  exact h5.congr_fun fun v => by unfold majorant; ring

lemma coefficient_norm_le {L R r : ℝ} (hr : 0 ≤ r) (hL : L ≤ r) (hR : r ≤ R) (v : Index) :
    ‖coefficient r v‖ ≤ Real.exp (-L) * (R^v.1 / v.1.factorial) *
      (R^v.2.1 / v.2.1.factorial) * (R^v.2.2 / v.2.2.factorial) := by
  simp only [coefficient, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr, Complex.norm_natCast, Complex.norm_exp,
    Complex.neg_re, Complex.ofReal_re]
  have hR0 : 0 ≤ R := hr.trans hR
  gcongr

lemma power_coefficient_energy {ι θ : Type*} (H : Finset ι) (S : Finset θ)
    (χ : ι → θ → ℂ) (u : θ → ℂ) (x : θ → ℝ) {δ K : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hx : ∀ a ∈ S, |x a| ≤ δ)
    (hop : ∀ v : θ → ℂ, ∑ h ∈ H, ‖∑ a ∈ S, v a * χ h a‖^2 ≤ K * ∑ a ∈ S, ‖v a‖^2)
    (j : ℕ) :
    ∑ h ∈ H, ‖∑ a ∈ S, (u a * (x a : ℂ)^j) * χ h a‖^2 ≤
      (Real.sqrt (K * ∑ a ∈ S, ‖u a‖^2) * δ^j)^2 := by
  apply (hop _).trans
  have he : ∑ a ∈ S, ‖u a * (x a : ℂ)^j‖^2 ≤
      (∑ a ∈ S, ‖u a‖^2) * (δ^j)^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (pow_nonneg (abs_nonneg _) _) (pow_nonneg hδ _)).2
        (pow_le_pow_left₀ (abs_nonneg _) (hx a ha) j)) (sq_nonneg _)
  calc
    _ ≤ K * ((∑ a ∈ S, ‖u a‖^2) * (δ^j)^2) := mul_le_mul_of_nonneg_left he hK
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hK (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
      ring

 

theorem gaussian_gram_bound {ι θ : Type*} (H : Finset ι) (S : Finset θ)
    (χ : ι → θ → ℂ) (u : θ → ℂ) (x : θ → ℝ) (r : ι → ℝ)
    {L R δ K : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hx : ∀ a ∈ S, |x a| ≤ δ)
    (hr : ∀ h ∈ H, 0 ≤ r h ∧ L ≤ r h ∧ r h ≤ R) (hR : 0 ≤ R)
    (hop : ∀ v : θ → ℂ, ∑ h ∈ H, ‖∑ a ∈ S, v a * χ h a‖^2 ≤ K * ∑ a ∈ S, ‖v a‖^2) :
    ‖∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S,
      (u a * χ h a) * star (u b * χ h b) *
        Complex.exp (-(r h : ℂ)*(1-x a)*(1-x b))‖ ≤
      Real.exp (-L+(2*δ+δ^2)*R) * K * ∑ a ∈ S, ‖u a‖^2 := by
  let D := K * ∑ a ∈ S, ‖u a‖^2
  have hD : 0 ≤ D := mul_nonneg hK (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  let F : Index → ℂ := fun v => ∑ h ∈ H, coefficient (r h) v *
    (∑ a ∈ S, (u a * (x a : ℂ)^(v.1+v.2.2)) * χ h a) *
    star (∑ a ∈ S, (u a * (x a : ℂ)^(v.2.1+v.2.2)) * χ h a)
  have hs : HasSum F (∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S,
      (u a * χ h a) * star (u b * χ h b) *
        Complex.exp (-(r h : ℂ)*(1-x a)*(1-x b))) := by
    have hs := hasSum_sum (s := H) fun h _ => hasSum_sum (s := S) fun a _ =>
      hasSum_sum (s := S) fun b _ =>
        (kernel_hasSum (r h) (x a) (x b)).mul_left ((u a * χ h a) * star (u b * χ h b))
    apply hs.congr_fun
    intro v
    unfold F
    apply Finset.sum_congr rfl
    intro h hh
    rw [star_sum, mul_assoc, Finset.sum_mul_sum]
    simp only [Finset.mul_sum, star_mul, star_pow, Complex.star_def, Complex.conj_ofReal]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hf (v : Index) : ‖F v‖ ≤ majorant L R δ v * D := by
    let C := Real.exp (-L) * (R^v.1 / v.1.factorial) *
      (R^v.2.1 / v.2.1.factorial) * (R^v.2.2 / v.2.2.factorial)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hb := norm_weighted_pair_sum H
      (fun h => ∑ a ∈ S, (u a * (x a : ℂ)^(v.1+v.2.2)) * χ h a)
      (fun h => ∑ a ∈ S, (u a * (x a : ℂ)^(v.2.1+v.2.2)) * χ h a)
      (fun h => coefficient (r h) v) hC
      (show 0 ≤ Real.sqrt D * δ^(v.1+v.2.2) by positivity)
      (show 0 ≤ Real.sqrt D * δ^(v.2.1+v.2.2) by positivity)
      (fun h hh => coefficient_norm_le (hr h hh).1 (hr h hh).2.1 (hr h hh).2.2 v)
      (power_coefficient_energy H S χ u x hδ hK hx hop _)
      (power_coefficient_energy H S χ u x hδ hK hx hop _)
    apply hb.trans_eq
    calc
      _ = (Real.sqrt D)^2 * C * δ^(v.1+v.2.2) * δ^(v.2.1+v.2.2) := by ring
      _ = _ := by
        rw [Real.sq_sqrt hD]
        simp only [C, majorant, pow_add, mul_pow]
        ring
  have hb := hs.norm_le_of_bounded ((majorant_hasSum L R δ).mul_right D) hf
  simpa only [D, mul_assoc] using hb

 

lemma gaussian_gram_envelope (T : ℝ) :
    Real.exp (-T+(2*(1/10 : ℝ)+(1/10 : ℝ)^2)*(2*T)) = Real.exp (-(29/50 : ℝ)*T) := by
  congr 1
  ring

end CubicFirstMoment.SieveKernel
end

end OAI
