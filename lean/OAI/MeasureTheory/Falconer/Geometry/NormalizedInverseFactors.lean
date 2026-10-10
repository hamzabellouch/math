import OAI.MeasureTheory.Falconer.Geometry.FactorChartControl
import OAI.MeasureTheory.Falconer.Geometry.SeparationOrder
import OAI.MeasureTheory.Falconer.Fourier.StationaryScales

namespace OAI

/-! # Size-one endpoint factors with the exact total derivative cost

Positive upper sizes are selected before the scale label. Division by
those sizes retains all zero sets and chart bounds; their product costs
only the sum of the original endpoint derivative orders.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def normalizedEndpoint {d : ℕ} (a : ℝ)
    (b : Space d → Sphere d → ℂ) (x : Space d) (w : Sphere d) : ℂ :=
  (a⁻¹ : ℝ)*b x w

theorem normalizedEndpoint_ne_zero {d : ℕ} (a : ℝ)
    (b : Space d → Sphere d → ℂ) (x : Space d) (w : Sphere d)
    (h : normalizedEndpoint a b x w ≠ 0) : b x w ≠ 0 :=
  (mul_ne_zero_iff.mp h).2

theorem normalizedEndpoint_restore {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Space d → Sphere d → ℂ) (x : Space d) (w : Sphere d) :
    (a : ℂ)*normalizedEndpoint a b x w = b x w := by
  simp only [normalizedEndpoint,← mul_assoc,← Complex.ofReal_mul,mul_inv_cancel₀ ha.ne',
    Complex.ofReal_one,one_mul]

theorem ChartSymbolControl.normalized {n K : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D a : ℝ}
    (h : ChartSymbolControl K b B D) (ha : 0 < a) (hBa : B ≤ a) (hD : 0 ≤ D) :
    ChartSymbolControl K (normalizedEndpoint a b) 1 D := by
  have hn : ‖(a⁻¹ : ℝ)‖ = a⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr ha.le)
  refine ⟨measurable_const.mul h.measurable,?_,?_,?_⟩
  · intro x w
    simp only [normalizedEndpoint,norm_mul,Complex.norm_real,hn]
    exact (mul_le_mul_of_nonneg_left ((h.bound x w).trans hBa)
      (inv_nonneg.mpr ha.le)).trans_eq (inv_mul_cancel₀ ha.ne')
  · intro x e y
    exact contDiff_const.mul (h.smooth x e y)
  · intro e k hk x y hy u hu
    change ‖iteratedDeriv k (fun v => (a⁻¹ : ℝ)*rotatedChartAmplitude e (b x) y v) u‖ ≤ _
    rw [iteratedDeriv_const_mul _ ((h.smooth x e y).of_le (by simp)).contDiffAt,
      norm_mul,Complex.norm_real,hn]
    calc
      _ ≤ a⁻¹*(B*D^k) := mul_le_mul_of_nonneg_left
        (h.derivative e k hk x y hy u hu) (inv_nonneg.mpr ha.le)
      _ ≤ a⁻¹*(a*D^k) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hBa (pow_nonneg hD _)) (inv_nonneg.mpr ha.le)
      _ = 1*D^k := by rw [← mul_assoc,inv_mul_cancel₀ ha.ne']

theorem ChartSymbolControl.conj {n K : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D : ℝ}
    (h : ChartSymbolControl K b B D) :
    ChartSymbolControl K (fun x w => star (b x w)) B D := by
  refine ⟨continuous_star.measurable.comp h.measurable,?_,?_,?_⟩
  · intro x w
    simpa only [norm_star] using h.bound x w
  · intro x e y
    exact Complex.conjCLE.contDiff.comp (h.smooth x e y)
  · intro e k hk x y hy u hu
    have hn := Complex.conjLIE.norm_iteratedFDeriv_comp_left
      (rotatedChartAmplitude e (b x) y) u k
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hn
    exact hn.le.trans (h.derivative e k hk x y hy u hu)

theorem normalizedEndpoint_product_restore {d : ℕ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (b f : Space d → Sphere d → ℂ) (x y : Space d) (w : Sphere d) :
    b x w*f y w = ((a*c : ℝ) : ℂ)*
      (normalizedEndpoint a b x w*normalizedEndpoint c f y w) := by
  rw [Complex.ofReal_mul]
  calc
    _ = ((a : ℂ)*normalizedEndpoint a b x w)*
      ((c : ℂ)*normalizedEndpoint c f y w) := by
        rw [normalizedEndpoint_restore ha,normalizedEndpoint_restore hc]
    _ = _ := by ring

theorem endpoint_order_product_le {p q N : ℕ} (hpq : p+q ≤ N)
    {A B C E D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E) (hD : 1 ≤ D) :
    (A*C*D^p)*(B*E*D^q) ≤ A*B*C*E*D^N := by
  calc
    _ = A*B*C*E*D^(p+q) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hpq) (by positivity)

theorem stationary_normalized_coefficient_le {p q j : ℕ} (hpq : p+q ≤ 2*j)
    {Λ D : ℝ} (hΛ : 0 < Λ) (hD : 1 ≤ D) (h : ℝ) :
    Λ^h*(Λ^j)⁻¹*D^(p+q) ≤ Λ^h*(D^2/Λ)^j := by
  calc
    _ ≤ Λ^h*(Λ^j)⁻¹*D^(2*j) := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD hpq) (by positivity)
    _ = _ := by rw [div_pow,div_eq_mul_inv,pow_mul]; ring

theorem stationary_normalized_coefficient_scale {p q j : ℕ} (hpq : p+q ≤ 2*j)
    {Λ D R κ : ℝ} (hΛ : 0 < Λ) (hD : 1 ≤ D) (hR : 1 ≤ R)
    (hratio : D^2/Λ ≤ R^(-κ)) (h : ℝ) :
    Λ^h*(Λ^j)⁻¹*D^(p+q) ≤ Λ^h*R^(-κ*(j : ℝ)) := by
  apply (stationary_normalized_coefficient_le hpq hΛ hD h).trans
  rw [Real.rpow_mul_natCast (zero_le_one.trans hR)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio j)
    (Real.rpow_nonneg hΛ.le _)

theorem SmoothSeparation.HasOrder.normalizedChartFamily {I : Type*} [MeasurableSpace I]
    {n N : ℕ}
    {S : SmoothSeparation (I × Space (n+2)) (I × Space (n+2)) (Space (n+2))}
    {B C : I × Space (n+2) → Space (n+2) → ℂ}
    (h : S.HasOrder B C N)
    (hmeas : ∀ k : S.index, Measurable (Function.uncurry (S.left k)) ∧
      Measurable (Function.uncurry (S.right k))) (K : ℕ) :
    ∃ p q : S.index → ℕ, ∃ A E : S.index → ℝ,
      (∀ k, p k+q k ≤ N ∧ 1 ≤ A k ∧ 1 ≤ E k) ∧
      ∀ (a : I) (Cb Cc D : ℝ), 1 ≤ Cb → 1 ≤ Cc → 1 ≤ D →
        (∀ x l, l ≤ K+N → ∀ z, ‖iteratedFDeriv ℝ l (B (a,x)) z‖ ≤ Cb*D^l) →
        (∀ x l, l ≤ K+N → ∀ z, ‖iteratedFDeriv ℝ l (C (a,x)) z‖ ≤ Cc*D^l) →
        ∀ k : S.index,
          ChartSymbolControl K
            (normalizedEndpoint (A k*Cb*D^(p k)) (fun x w => S.left k (a,x) w)) 1 D ∧
          ChartSymbolControl K
            (normalizedEndpoint (E k*Cc*D^(q k)) (fun x w => S.right k (a,x) w)) 1 D ∧
          (A k*Cb*D^(p k))*(E k*Cc*D^(q k)) ≤ A k*E k*Cb*Cc*D^N := by
  obtain ⟨p,q,hpq⟩ := h
  choose A hA hAb using fun k => (hpq k).2.1.chartControlFamily (hmeas k).1 K
  choose E hE hEb using fun k => (hpq k).2.2.chartControlFamily (hmeas k).2 K
  let A' := fun k => max 1 (A k)
  let E' := fun k => max 1 (E k)
  have hA' (k) : 1 ≤ A' k := le_max_left _ _
  have hE' (k) : 1 ≤ E' k := le_max_left _ _
  refine ⟨p,q,A',E',fun k => ⟨(hpq k).1,hA' k,hE' k⟩,?_⟩
  intro a Cb Cc D hCb hCc hD hb hc k
  have hp : p k ≤ N := by have := (hpq k).1; omega
  have hq : q k ≤ N := by have := (hpq k).1; omega
  have hl := hAb k a Cb D (zero_le_one.trans hCb) hD
    (fun x l hl z => hb x l (by omega) z)
  have hr := hEb k a Cc D (zero_le_one.trans hCc) hD
    (fun x l hl z => hc x l (by omega) z)
  refine ⟨hl.normalized (by positivity) ?_ (zero_le_one.trans hD),
    hr.normalized (by positivity) ?_ (zero_le_one.trans hD),
    endpoint_order_product_le (hpq k).1 (by positivity) (by positivity)
      (zero_le_one.trans hCb) (zero_le_one.trans hCc) hD⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hCb))
      (pow_nonneg (zero_le_one.trans hD) _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hCc))
      (pow_nonneg (zero_le_one.trans hD) _)

end Falconer

end OAI
