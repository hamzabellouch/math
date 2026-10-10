import OAI.MeasureTheory.Falconer.Angular.CapLocalization
import OAI.MeasureTheory.Falconer.Angular.QuantitativeCaps

namespace OAI

/-!
# Decay away from the two stationary poles

The actual normalized cap partition reduces a full-sphere amplitude to
the proved capwise integration-by-parts estimate. The only published
input is the gnomonic surface formula. Constants depend on the fixed
distance from the poles, dimension, and differentiation order.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem offPole_center_gap {d : ℕ} (v : Space d) (hv : ‖v‖ = 1)
    (c z : Sphere d) {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ≤ ε/64)
    (hnear : ‖(z : Space d)-(c : Space d)‖ ≤ δ)
    (hgap : ε ≤ ‖perpendicularPart (z : Space d) v‖) :
    ε/4 < ‖perpendicularPart (c : Space d) v‖ := by
  have he := perpendicularPart_test_error (sphere_norm c) (sphere_norm z) v v
  simp only [sub_self,norm_zero,hv,mul_one,zero_add] at he
  rw [norm_sub_rev (c : Space d) (z : Space d)] at he
  have ht : ‖perpendicularPart (z : Space d) v‖ ≤
      ‖perpendicularPart (c : Space d) v‖ +
        ‖perpendicularPart (c : Space d) v-perpendicularPart (z : Space d) v‖ := by
    calc
      _ = ‖perpendicularPart (c : Space d) v -
          (perpendicularPart (c : Space d) v-perpendicularPart (z : Space d) v)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  nlinarith

/-- Uniform full-sphere integration by parts for an amplitude separated
from both poles. Its hypotheses are ordinary chart derivative bounds on
the original amplitude, before cap localization. -/
theorem sphere_offPole_decay (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (v : Space (n+2)) (b : Sphere (n+2) → ℂ),
      ‖v‖ = 1 → Measurable b →
      (∀ w, b w ≠ 0 → ε ≤ ‖perpendicularPart (w : Space (n+2)) v‖) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n, ‖y‖ ≤ 1 →
        ContDiff ℝ ∞ (rotatedChartAmplitude e b y)) →
      ∀ (M C D Λ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ →
      (∀ w, ‖b w‖ ≤ M) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n, ‖y‖ ≤ 1 →
        ∀ k ≤ m, ∀ u ∈ Icc (-1 : ℝ) 1,
          ‖iteratedDeriv k (rotatedChartAmplitude e b y) u‖ ≤ C*D^k) →
      ‖∫ w : Sphere (n+2),
        Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ))*b w
        ∂sphereMeasure (n+2)‖ ≤ K*C*(D/Λ)^m := by
  classical
  let δ := min (ε/64) (1/4 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε/64 := min_le_left _ _
  have hδsmall : δ ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨H,hH,hpartition⟩ := quantitative_smooth_cap_partition n m
  obtain ⟨S,η,_hcard,_hoverlap,hηmeas,hηsum,hηnorm,hηcap,hηsmooth,hηder⟩ :=
    hpartition δ hδ (hδsmall.trans (by norm_num))
  obtain ⟨A,hA,hestimate⟩ := failed_cap_sphere_nonstationary hpublished n m hn
  let τ := ε/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let q := max 1 (max δ⁻¹ (4/τ))
  have hq : 1 ≤ q := le_max_left _ _
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hqδ : δ⁻¹ ≤ q := (le_max_left _ _).trans (le_max_right _ _)
  have hqτ : 4/τ ≤ q := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨(S.card : ℝ)*A*(2^m*H)*(q/(τ/4))^m,by positivity,?_⟩
  intro v b hv hb hgap hsmooth M C D Λ hC hD hΛ hM hder
  let bcap : Sphere (n+2) → Sphere (n+2) → ℂ :=
    fun c w => (η c w : ℂ)*b w
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hqD : 1 ≤ q*D := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hD)]
  have hqD0 : 0 ≤ q*D := zero_le_one.trans hqD
  have hDb : D ≤ q*D := le_mul_of_one_le_left hD0 hq
  have hDδ : δ⁻¹ ≤ q*D := hqδ.trans (le_mul_of_one_le_right hq0 hD)
  have hDτ : 1 ≤ (τ/4)*(q*D) := by
    have hbound : 4/τ ≤ q*D := hqτ.trans (le_mul_of_one_le_right hq0 hD)
    have hh := (div_le_iff₀ hτ).mp hbound
    nlinarith
  have hbcMeas (c : Sphere (n+2)) : Measurable (bcap c) :=
    (Complex.measurable_ofReal.comp (hηmeas c)).mul hb
  have hbcCap (c : Sphere (n+2)) (hc : c ∈ S) :
      ∀ w, bcap c w ≠ 0 → ‖(w : Space (n+2))-(c : Space (n+2))‖ ≤ δ := by
    intro w hw
    apply hηcap c hc w
    intro hz
    exact hw (by simp [bcap,hz])
  have hbcNorm (c : Sphere (n+2)) (hc : c ∈ S) (w : Sphere (n+2)) :
      ‖bcap c w‖ ≤ M := by
    have he := hηnorm c hc w
    calc
      _ = |η c w| * ‖b w‖ := by simp only [bcap,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ 1*‖b w‖ := mul_le_mul_of_nonneg_right
        (by simpa only [abs_of_nonneg he.1] using he.2) (norm_nonneg _)
      _ ≤ M := by simpa only [one_mul] using hM w
  have hbcSmooth (c : Sphere (n+2))
      (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (hy : ‖y‖ ≤ 1) :
      ContDiff ℝ ∞ (rotatedChartAmplitude e (bcap c) y) :=
    (hηsmooth c e y).mul (hsmooth e y hy)
  let F : Sphere (n+2) → ℂ := fun w =>
    Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ))
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hFnorm (w : Sphere (n+2)) : ‖F w‖ = 1 := by
    simp only [F,Complex.norm_exp,Complex.mul_re,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero,Real.exp_zero]
  have hbcInt (c : Sphere (n+2)) (hc : c ∈ S) :
      Integrable (fun w => F w*bcap c w) (sphereMeasure (n+2)) :=
    Integrable.of_bound (hFm.mul (hbcMeas c)).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun w => by
        simpa only [norm_mul,hFnorm,one_mul] using hbcNorm c hc w))
  have hbcEst (c : Sphere (n+2)) (hc : c ∈ S) :
      ‖∫ w, F w*bcap c w ∂sphereMeasure (n+2)‖ ≤
        A*(2^m*H*C)*((q*D)/(Λ*(τ/4)))^m := by
    by_cases hz : ∀ w, bcap c w = 0
    · simp only [hz,mul_zero,integral_zero,norm_zero]
      positivity
    · obtain ⟨z,hz⟩ := not_forall.mp hz
      have hbz : b z ≠ 0 := by
        intro hh
        exact hz (by simp only [bcap,hh,mul_zero])
      have hbad := offPole_center_gap v hv c z hε hδε (hbcCap c hc z hz) (hgap z hbz)
      obtain ⟨e,he,heEst⟩ := hestimate c v τ δ (sphere_norm c) hτ hδ.le hδsmall hbad
      have hcap : ∀ w, bcap c w ≠ 0 →
          ‖(w : Space (n+2))-e (chartPole n)‖ ≤ δ := by
        simpa only [he] using hbcCap c hc
      have hsupport := (cap_amplitude_chart_support e (bcap c) hδ.le hδsmall hcap).2.2
      apply heEst v (bcap c) (hbcMeas c) (hbcCap c hc) (hbcSmooth c e)
        M (2^m*H*C) (q*D) Λ (by positivity) hqD hΛ (hbcNorm c hc)
        (by simpa only [hv] using hDτ) ?_ ?_
      · simp only [sub_self,norm_zero,hv,mul_one,zero_add]
        dsimp [τ]
        linarith
      · intro k hk y hy u hu
        have hui := hsupport y hu
        have hbound := PlanarFalconer.complex_product_derivative_bound
          (hηsmooth c e y) (hsmooth e y hy) hH hC hqD0 k u
          (fun j hj => (hηder c e y hy u hui j (hj.trans hk)).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hDδ j) hH))
          (fun j hj => (hder e y hy j (hj.trans hk) u hui).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hDb j) hC))
        apply hbound.trans
        change (2 : ℝ)^k*H*C*(q*D)^k ≤ (2^m*H*C)*(q*D)^k
        gcongr
        norm_num
  have hsplit (w : Sphere (n+2)) : F w*b w = ∑ c ∈ S, F w*bcap c w := by
    have hs : (∑ c ∈ S, (η c w : ℂ)) = 1 := by exact_mod_cast hηsum w
    calc
      _ = (F w*(∑ c ∈ S, (η c w : ℂ)))*b w := by rw [hs,mul_one]
      _ = ∑ c ∈ S, F w*((η c w : ℂ)*b w) := by
        rw [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := rfl
  change ‖∫ w, F w*b w ∂sphereMeasure (n+2)‖ ≤ _
  simp_rw [hsplit]
  rw [integral_finsetSum S hbcInt]
  calc
    _ ≤ ∑ c ∈ S, ‖∫ w, F w*bcap c w ∂sphereMeasure (n+2)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ S, A*(2^m*H*C)*((q*D)/(Λ*(τ/4)))^m :=
      Finset.sum_le_sum hbcEst
    _ = (S.card : ℝ)*(A*(2^m*H*C)*((q*D)/(Λ*(τ/4)))^m) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ = _ := by
      have hr : (q*D)/(Λ*(τ/4)) = (q/(τ/4))*(D/Λ) := by ring
      rw [hr,mul_pow]
      ring

end Falconer

end OAI
