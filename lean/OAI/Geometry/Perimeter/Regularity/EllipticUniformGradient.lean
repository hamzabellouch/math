import OAI.Geometry.Perimeter.Regularity.EllipticPointwise
import OAI.Geometry.Perimeter.Regularity.EllipticSlopeComparison

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem gradient_modulus_from_slopes {θ R K H L : ℝ}
    (hθ : 0<θ) (hR : 0<R) (hH : 0≤H) (hL : 0≤L)
    (hLbig : 2^(n+2)≤volume.real (Metric.ball (0:Euc n) 1)*L^2)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    {U : Set (Euc n)} {q : Euc n → ℕ → Euc n}
    (he : ∀ p∈U, ∀ j, ‖q p j-gradient f p‖≤2*K*H*(1/2)^j)
    (hE : ∀ p∈U, ∀ j, scaledGradientEnergy f p (θ^j*R) (q p j)≤H^2*((1/2)^j)^2) :
    ∀ j p, p∈U → ∀ p', p'∈U → dist p p'≤θ^j*R/2 →
       ‖gradient f p-gradient f p'‖≤(4*K+L)*H*(1/2)^j := by
  intro j p hp p' hp' hd
  have hV : 0<volume.real (Metric.ball (0:Euc n) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
  have hh := scaled_slope_comparison hf p p' (by positivity : 0<θ^j*R) hd (q p j) (q p' j)
  have hEp := hE p hp j
  have hEp' := hE p' hp' j
  have hbound : ‖q p j-q p' j‖≤L*H*(1/2)^j := by
    have h1 := mul_le_mul_of_nonneg_left (add_le_add hEp hEp') (by positivity : 0≤(2:ℝ)^(n+1))
    have h2 := mul_le_mul_of_nonneg_right hLbig (by positivity : 0≤H^2*((1/2:ℝ)^j)^2)
    have heq : (2:ℝ)^(n+2)* (H^2*((1/2:ℝ)^j)^2)=
        2^(n+1)*(H^2*((1/2:ℝ)^j)^2+H^2*((1/2:ℝ)^j)^2) := by
      rw [show n+2=(n+1)+1 by omega,pow_succ]; ring
    rw [heq] at h2
    have hs : ‖q p j-q p' j‖^2≤(L*H*(1/2)^j)^2 := by
      apply (mul_le_mul_iff_right₀ hV).mp
      nlinarith [hh.trans (h1.trans h2)]
    nlinarith [norm_nonneg (q p j-q p' j),show 0≤L*H*(1/2:ℝ)^j by positivity]
  have ht := norm_sub_le_norm_sub_add_norm_sub (gradient f p) (q p j) (gradient f p')
  have ht' := norm_sub_le_norm_sub_add_norm_sub (q p j) (q p' j) (gradient f p')
  rw [norm_sub_rev (gradient f p) (q p j)] at ht
  have hep := he p hp j
  have hep' := he p' hp' j
  nlinarith

 theorem linear_uniform_gradient {θ δ K a B H R : ℝ}
    (hθ : 0<θ) (hθ1 : θ<1) (hK : 1≤K)
    (hc : LinearContractionProperty n θ δ K)
    (ha : 0≤a) (hB : 0≤B) (hH : 0≤H) (hR : 0<R)
    (hsmall : 32*K^2*a≤1) (hforce : 16*K*B≤H)
    {A : Euc n → Euc n →L[ℝ] Euc n} (hA : Continuous A)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) {F : Euc n → Euc n} (hF : Continuous F)
    {U : Set (Euc n)}
    (h : ∀ p∈U, WeakLinearEquation A f F (Metric.ball p R))
    (hnear : ∀ p∈U, ∀ x∈Metric.ball p R, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖≤δ)
    (hosc : ∀ p∈U, ∀ j x, x∈Metric.ball p (θ^j*R) →
      ‖A p-A x‖≤a*(1/2)^j ∧ ‖F x-F p‖≤B*(1/2)^j)
    (hinit : ∀ p∈U, scaledGradientEnergy f p R 0≤H^2) :
    ∃ C : ℝ, 0<C ∧ (∀ p∈U, ‖gradient f p‖≤2*K*H) ∧
      ∀ j p, p∈U → ∀ p', p'∈U → dist p p'≤θ^j*R/2 →
        ‖gradient f p-gradient f p'‖≤C*H*(1/2)^j := by
  have hex (p : Euc n) : ∃ q : ℕ → Euc n, p∈U →
      (∀ j, ‖q j-gradient f p‖≤2*K*H*(1/2)^j) ∧
      (∀ j, scaledGradientEnergy f p (θ^j*R) (q j)≤H^2*((1/2)^j)^2) ∧
      ‖gradient f p‖≤2*K*H := by
    by_cases hp : p∈U
    · obtain ⟨q,hq⟩ := linear_pointwise_iteration hθ hθ1 hK hc ha hB hH hR hsmall hforce
        hA hf hF p (h p hp) (hnear p hp) (hosc p hp) (hinit p hp)
      exact ⟨q,fun _ ↦ hq⟩
    · exact ⟨fun _ ↦ 0,fun hh ↦ (hp hh).elim⟩
  choose q hq using hex
  have hV : 0<volume.real (Metric.ball (0:Euc n) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
  let L := Real.sqrt (2^(n+2)/volume.real (Metric.ball (0:Euc n) 1))
  have hL : 0≤L := Real.sqrt_nonneg _
  have hLbig : 2^(n+2)≤volume.real (Metric.ball (0:Euc n) 1)*L^2 := by
    dsimp [L]
    rw [Real.sq_sqrt (by positivity)]
    rw [mul_div_cancel₀ _ hV.ne']
  refine ⟨4*K+L,by linarith,fun p hp ↦ (hq p hp).2.2,?_⟩
  exact gradient_modulus_from_slopes hθ hR hH hL hLbig hf
    (fun p hp ↦ (hq p hp).1) (fun p hp ↦ (hq p hp).2.1)

end RPISingularHarnack

end

end OAI
