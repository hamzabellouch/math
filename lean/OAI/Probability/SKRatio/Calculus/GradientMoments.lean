import Mathlib
import OAI.Probability.SKRatio.Calculus.FieldTails

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma integral_exp_decay_le {κ d : ℝ} (hκ : 0 < κ) :
    (∫ r in (0:ℝ)..d, Real.exp (-κ*r)) ≤ 1/κ := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => -Real.exp (-κ*r)/κ)
      (Real.exp (-κ*r)) r := by
    have h := (((hasDerivAt_id r).const_mul (-κ)).exp.neg).div_const κ
    apply h.congr_deriv
    simp only [mul_one, id_eq]
    field_simp
  have hi : IntervalIntegrable (fun r : ℝ => Real.exp (-κ*r)) volume 0 d :=
    (by fun_prop : Continuous (fun r : ℝ => Real.exp (-κ*r))).intervalIntegrable 0 d
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
  simp only [mul_zero, Real.exp_zero, neg_div]
  have hp := div_nonneg (Real.exp_nonneg (-κ*d)) hκ.le
  linarith

lemma gradient_envelope_bounds {κ C E R d : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hE : E ≤ 1) (hdE : d*E ≤ 1) :
    (∀ r ∈ Set.Icc (0:ℝ) d, R*(C*Real.exp (-κ*r)+E) ≤ R*(C+1)) ∧
    (∫ r in (0:ℝ)..d, R*(C*Real.exp (-κ*r)+E)) ≤ R*(C/κ+1) := by
  refine ⟨?_,?_⟩
  · intro r hr
    apply mul_le_mul_of_nonneg_left _ hR
    have he : Real.exp (-κ*r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hκ,hr.1])
    have hc := mul_le_mul_of_nonneg_left he hC
    linarith
  · have hi : IntervalIntegrable (fun r : ℝ => C*Real.exp (-κ*r)) volume 0 d :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hd).mpr
        (by fun_prop : Continuous (fun r : ℝ => C*Real.exp (-κ*r))).integrableOn_Icc
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ hR
    have hu := mul_le_mul_of_nonneg_left (integral_exp_decay_le (d := d) hκ) hC
    simpa only [mul_one_div] using add_le_add hu hdE

lemma moments_of_gradient_envelope {n : ℕ} (J : Interaction n) (f : Observables n)
    {κ C E R d : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hE : E ≤ 1) (hdE : d*E ≤ 1)
    (henv : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ x,
      unweightedGradient (semigroup J r f) x ≤ R*(C*Real.exp (-κ*r)+E)) :
    (∀ x, FiniteLaw.variance (continuousKernel J d x) f ≤ 4*(R*(C/κ+1))) ∧
    (∀ θ x, semigroup J d (fun y => Real.exp (θ*(f y-semigroup J d f x))) x ≤
      Real.exp (2*θ^2*Real.exp (2*|θ| *Real.sqrt (R*(C+1)))*(R*(C/κ+1)))) := by
  have hb : IntervalIntegrable (fun r : ℝ => R*(C*Real.exp (-κ*r)+E)) volume 0 d :=
    (by fun_prop : Continuous (fun r : ℝ => R*(C*Real.exp (-κ*r)+E))).intervalIntegrable 0 d
  have ⟨hB,hI⟩ := gradient_envelope_bounds hκ hC hR hd hE hdE
  constructor
  · intro x
    rw [FiniteLaw.variance_eq _ _ (continuousKernel_sum J d x), ← semigroup_eq_kernel,
      ← semigroup_eq_kernel]
    exact (semigroup_variance_le J f d hd _ hb henv x).trans
      (mul_le_mul_of_nonneg_left hI (by norm_num))
  · intro θ x
    exact (semigroup_jump_mgf J f d hd _ (R*(C+1)) θ hb hB henv x).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hI (by positivity)))

lemma gradient_envelope_of_small_set {n : ℕ} (J : Interaction n)
    (f : Observables n) (bad : Set (Spin n)) {κ A d₀ T q R : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hinit : ∀ y, unweightedGradient f y ≤ R)
    (hdrift : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ y,
      deriv (fun v => unweightedGradient (semigroup J v f) y) r -
        generator J (unweightedGradient (semigroup J r f)) y ≤
          (-κ + if y ∈ bad then A else 0)*unweightedGradient (semigroup J r f) y)
    (havoid : ∀ u ∈ Set.Icc d₀ T, ∀ x,
      semigroup J u (fun y => if y ∈ bad then 1 else 0) x ≤ q)
    (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) T) (x : Spin n) :
    unweightedGradient (semigroup J r f) x ≤
      R*(Real.exp (A*d₀)*Real.exp (-κ*r)+A*Real.exp (A*d₀)*T*Real.exp (A*T)*q) := by
  have h := gradient_propagation_small_set J f bad hκ hA hd₀ hr.1 le_rfl hr.2 hq hR
    (fun v hv => hdrift v ⟨hv.1,hv.2.trans hr.2⟩) havoid
    (by simpa only [sub_self,semigroup_zero,one_apply_eq_self] using hinit) x
  simp only [sub_self,semigroup_zero,one_apply_eq_self] at h
  calc
    _ ≤ _ := h
    _ ≤ Real.exp (A*d₀)*Real.exp (-κ*r)*R +
        A*Real.exp (A*d₀)*T*Real.exp (A*T)*q*R :=
      add_le_add (mul_le_mul_of_nonneg_left
        (semigroup_le_const J r hr.1 hinit x) (by positivity)) le_rfl
    _ = _ := by ring

theorem uniform_gradient_moments_of_small_set
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n)
    {D R : ℝ} (hD : 0 < D) (hR : 0 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      (∀ y, unweightedGradient f y ≤ R) → ∀ d ∈ Set.Icc (0:ℝ) (D*Real.log n),
      (∀ x, FiniteLaw.variance (continuousKernel (coupling g) d x) f ≤
        4*(R*(Real.exp (A*d₀)/κ+1))) ∧
      (∀ θ x, semigroup (coupling g) d (fun y => Real.exp
        (θ*(f y-semigroup (coupling g) d f x))) x ≤
          Real.exp (2*θ^2*Real.exp (2*|θ| *Real.sqrt (R*(Real.exp (A*d₀)+1)))*
            (R*(Real.exp (A*d₀)/κ+1)))) := by
  let C := Real.exp (A*d₀)
  let E (n : ℕ) := A*C*D*(Real.log n)*dimensionDecay 4 n
  have hEn : Tendsto E atTop (𝓝 0) := by
    have h := (log_pow_mul_dimensionDecay_tendsto_zero 1 (by norm_num : (0:ℝ)<4)).const_mul (A*C*D)
    simpa only [pow_one, mul_zero, mul_assoc, E] using h
  have hTEn : Tendsto (fun n : ℕ => (D*Real.log n)*E n) atTop (𝓝 0) := by
    have h := (log_pow_mul_dimensionDecay_tendsto_zero 2 (by norm_num : (0:ℝ)<4)).const_mul (A*C*D^2)
    simp only [mul_zero] at h
    convert h using 1
    funext n
    dsimp only [E]
    ring
  have hm : 0 < A*D+4 := by positivity
  filter_upwards [hdrift D hD,havoid D (A*D+4) hD hm,
    hEn.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hTEn.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),eventually_ge_atTop 1]
    with n hndrift hnavoid hnE hnTE hn
  intro g hg f hf d hd
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hE0 : 0 ≤ E n := by dsimp [E,C,dimensionDecay]; positivity
  have herror : A*Real.exp (A*d₀)*(D*Real.log n)*Real.exp (A*(D*Real.log n))*
      dimensionDecay (A*D+4) n = E n := by
    have hprod : Real.exp (A*(D*Real.log n))*dimensionDecay (A*D+4) n = dimensionDecay 4 n := by
      unfold dimensionDecay
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc (A*Real.exp (A*d₀)*(D*Real.log n)),hprod]
    dsimp only [E,C]
    ring
  apply moments_of_gradient_envelope (coupling g) f hκ (Real.exp_nonneg _) hR hd.1 hnE.le
    ((mul_le_mul_of_nonneg_right hd.2 hE0).trans hnTE.le)
  intro r hr x
  have h := gradient_envelope_of_small_set (coupling g) f (bad n g)
    hκ.le hA hd₀ (dimensionDecay_pos (A*D+4) n).le hR hf
    (hndrift g hg f) (hnavoid g hg) r ⟨hr.1,hr.2.trans hd.2⟩ x
  rwa [herror] at h

lemma row_squares_le_opNorm {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) {K : ℝ}
    (hK : 0 ≤ K)
    (hop : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) (i : Fin n) :
    ∑ j, J i j ^ 2 ≤ K^2 := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J).le_opNorm e
  rw [he,mul_one] at h
  have hsq := sq_le_sq₀ (norm_nonneg _) hK |>.mpr (h.trans hop)
  rw [EuclideanSpace.real_norm_sq_eq] at hsq
  have happly (j : Fin n) :
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J e).ofLp j = J i j := by
    change (∑ coordinate, J j coordinate * e.ofLp coordinate) = J i j
    simp only [e, EuclideanSpace.single, PiLp.single_apply,
      mul_ite, mul_one, mul_zero]
    simp [hsymm j i]
  simpa only [happly] using hsq

theorem uniform_field_tails_of_small_set
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ γ R : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hγ : 0 < γ) (hR : 0 ≤ R)
    (hrow : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ i, ∑ j, coupling g i j ^ 2 ≤ R)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n) :
    ∀ ε δ D m : ℝ, 0 < ε → 0 < δ → 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t ∈ Set.Icc (0:ℝ) (D*Real.log n),
      continuousDistance g t ≤ 1-ε → ∀ x, semigroup (coupling g) t
        (fun y => if ∃ i, δ*Real.log n < |field (coupling g) y i| then 1 else 0) x ≤
          dimensionDecay m n := by
  have hmom {D : ℝ} (hD : 0 < D) :=
    uniform_gradient_moments_of_small_set G bad hκ hA hd₀ hdrift havoid hD hR
  apply uniform_field_tails_of_moments (V := 4*(R*(Real.exp (A*d₀)/κ+1)))
    (W := 2*R/γ) G
  · filter_upwards [hrow,hgap] with n hnrow hngap
    intro g hg i
    exact stationary_field_variance_le g hγ (hnrow g hg) (hngap g hg) i
  · intro D hD
    filter_upwards [hrow,hmom hD] with n hnrow hnmom
    intro g hg t ht x i
    exact (hnmom g hg (fun y => field (coupling g) y i)
      (fun y => by rw [unweightedGradient_field]; exact hnrow g hg i) t ht).1 x
  · intro D θ hD hθ
    refine ⟨Real.exp (2*θ^2*Real.exp (2*θ*Real.sqrt (R*(Real.exp (A*d₀)+1)))*
      (R*(Real.exp (A*d₀)/κ+1))),?_⟩
    filter_upwards [hrow,hmom hD] with n hnrow hnmom
    intro g hg t ht x i σ hσ
    have h := (hnmom g hg (fun y => field (coupling g) y i)
      (fun y => by rw [unweightedGradient_field]; exact hnrow g hg i) t ht).2 (σ*θ) x
    rcases hσ with hσ | hσ <;> rcases hσ with rfl
    · simpa only [neg_one_mul, neg_sq, abs_neg, abs_of_pos hθ] using h
    · simpa only [one_mul, abs_of_pos hθ] using h

end SKRatio.Calculus

end
end

end OAI
