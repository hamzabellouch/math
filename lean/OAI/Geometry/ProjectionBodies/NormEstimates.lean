import OAI.Geometry.ProjectionBodies.ScalarCalculus

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma mean_add {n : ℕ} [NeZero n] {f g : Sphere n → ℝ} (hf : Continuous f) (hg : Continuous g) :
    mean (fun u => f u + g u) = mean f + mean g :=
  integral_add (continuous_integrable hf) (continuous_integrable hg)

lemma mean_sub {n : ℕ} [NeZero n] {f g : Sphere n → ℝ} (hf : Continuous f) (hg : Continuous g) :
    mean (fun u => f u - g u) = mean f - mean g :=
  integral_sub (continuous_integrable hf) (continuous_integrable hg)

lemma mean_const_mul {n : ℕ} (c : ℝ) (f : Sphere n → ℝ) :
    mean (fun u => c * f u) = c * mean f := integral_const_mul c f

lemma mean_mul_const {n : ℕ} (c : ℝ) (f : Sphere n → ℝ) :
    mean (fun u => f u * c) = mean f * c := integral_mul_const c f

lemma mean_div_const {n : ℕ} (c : ℝ) (f : Sphere n → ℝ) :
    mean (fun u => f u / c) = mean f / c := integral_div c f

lemma mean_mono {n : ℕ} [NeZero n] {f g : Sphere n → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ u, f u ≤ g u) : mean f ≤ mean g :=
  integral_mono (continuous_integrable hf) (continuous_integrable hg) h

lemma mean_nonneg {n : ℕ} {f : Sphere n → ℝ} (h : ∀ u, 0 ≤ f u) : 0 ≤ mean f :=
  integral_nonneg h

lemma mean_centered_square {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) :
    mean (fun u => (f u - mean f) ^ 2) = variance f := by
  have hi : (fun u => (f u - mean f) ^ 2) =
      (fun u => (f u) ^ 2 - 2 * mean f * f u + (mean f) ^ 2) := by
    funext u; ring
  rw [hi, mean_add (f := fun u => (f u)^2 - 2 * mean f * f u)
      (g := fun _ => (mean f)^2)
      ((f.continuous.pow 2).sub (continuous_const.mul f.continuous)) continuous_const,
    mean_sub (f := fun u => (f u)^2) (g := fun u => 2 * mean f * f u)
      (f.continuous.pow 2) (continuous_const.mul f.continuous),
    mean_const_mul, mean_const, variance]
  ring

lemma norm_Q_le_variance {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) :
    ‖Q n (toH n f)‖ ^ 2 ≤ variance f := by
  simpa only [mean_centered_square] using norm_Q_le_centered n f (mean f)

lemma weighted_square_bound {a b w : ℝ} (hw : 0 < w) (hw1 : w < 1) :
    (a+b)^2 ≤ a^2/w + b^2/(1-w) := by
  have h1 : 0 < 1-w := sub_pos.mpr hw1
  apply (mul_le_mul_iff_of_pos_right (mul_pos hw h1)).mp
  have he : (a^2/w + b^2/(1-w)) * (w*(1-w)) = a^2*(1-w)+b^2*w := by
    field_simp
  rw [he]
  nlinarith only [sq_nonneg ((1-w)*a-w*b)]

lemma weighted_norm_bound {E : Type uE} [SeminormedAddCommGroup E] (a b : E)
    {w : ℝ} (hw : 0 < w) (hw1 : w < 1) :
    ‖a+b‖^2 ≤ ‖a‖^2/w + ‖b‖^2/(1-w) :=
  (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (norm_add_le a b) |>.trans (weighted_square_bound hw hw1)

lemma scalar_correction {n : ℕ} (hn : 4 ≤ n) {m t : ℝ}
    (hm : 0 ≤ m) (ht : 0 ≤ t) (htb : t ≤ Scalar.beta n * m) :
    Scalar.coefficient n * ((2*n : ℝ) * t^2 / (Scalar.weight n * (2*n+8)) -
      (m-t)^2/(1-Scalar.weight n)) ≤
      (2*(Scalar.exponent n : ℝ)-1)/(Scalar.exponent n : ℝ)^2 * m^2 := by
  have hb := (Scalar.beta_pos n).le
  have hb1 := (Scalar.beta_lt_one n).le
  have hw := Scalar.weight_pos n
  have hw1 := Scalar.weight_lt_one n
  have hden : 0 < Scalar.weight n * (2*n+8 : ℝ) := mul_pos hw (by positivity)
  have hs1 : t^2 ≤ (Scalar.beta n)^2 * m^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ ht (mul_nonneg hb hm)).mpr htb
  have ht1 : t ≤ m := htb.trans (by nlinarith)
  have hs2 : (1-Scalar.beta n)^2*m^2 ≤ (m-t)^2 := by
    have hle : (1-Scalar.beta n)*m ≤ m-t := by nlinarith
    simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg (sub_nonneg.mpr hb1) hm)
      (sub_nonneg.mpr ht1)).mpr hle
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ (2*n : ℝ))) hden.le
  have h2 := div_le_div_of_nonneg_right hs2 (sub_nonneg.mpr hw1.le)
  have h3 := mul_le_mul_of_nonneg_left (sub_le_sub h1 h2) (Scalar.coefficient_pos n).le
  have h4 := mul_le_mul_of_nonneg_right (Scalar.mean_bound n hn) (sq_nonneg m)
  apply h3.trans
  convert h4 using 1; ring

lemma scalar_curvature {n : ℕ} (hn : 4 ≤ n) [NeZero n] (g : Seminorm ℝ (Space n)) :
    (2 * n : ℝ) * variance (fun u : Sphere n => Scalar.G n (g u)) + (2 * n + 8 : ℝ) *
      ‖Q n (toH n (restrictContinuous (Scalar.G n ∘ g)
        ((Scalar.contDiff_G hn).continuous.comp (seminorm_continuous n g))))‖ ^ 2 ≤
      ((n : ℝ) - 1) * Scalar.beta n ^ 2 *
        mean (fun u : Sphere n => Scalar.I n (g u) * g u) :=
  seminorm_curvature (by omega) g (Scalar.contDiff_G hn) (Scalar.contDiff_I hn)
    (Scalar.I_nonneg hn) (Scalar.derivative_relation hn)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma continuous_e_comp {n : ℕ} (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u) :
    Continuous (fun u => e n (f u)) :=
  (((f.continuous.inv₀ (fun u => (hf u).ne')).pow n).sub continuous_const).div_const _

lemma continuous_M_comp {n : ℕ} (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u) :
    Continuous (fun u => M n (f u)) :=
  ((f.continuous.pow _).sub continuous_const).add
    (continuous_const.mul (continuous_e_comp f hf))

lemma mean_e_zero {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) : mean (fun u => e n (f u)) = 0 := by
  unfold e
  rw [mean_div_const, mean_sub (f := fun u => (f u)⁻¹^n) (g := fun _ => 1) ((f.continuous.inv₀ (fun u => (hf u).ne')).pow n)
    continuous_const, mean_const, hnorm, sub_self, zero_div]

lemma mean_M_of_normalized {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) :
    mean (fun u => M n (f u)) = mean (fun u => (f u) ^ exponent n) - 1 := by
  unfold M
  rw [mean_add (f := fun u => (f u)^exponent n - 1)
      (g := fun u => (exponent n : ℝ) * e n (f u))
      ((f.continuous.pow _).sub continuous_const) (continuous_const.mul (continuous_e_comp f hf)),
    mean_sub (f := fun u => (f u)^exponent n) (g := fun _ => 1) (f.continuous.pow _) continuous_const, mean_const, mean_const_mul,
    mean_e_zero f hf hnorm, mul_zero, add_zero]

lemma mean_W_of_normalized {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) :
    mean (fun u => W n (f u)) = mean (fun u => (f u)^exponent n) -
      mean (fun u => (f u)^(exponent n-1)) := by
  unfold W
  rw [mean_add (f := fun u => (f u)^exponent n - (f u)^(exponent n-1))
      (g := fun u => e n (f u)) ((f.continuous.pow _).sub (f.continuous.pow _))
      (continuous_e_comp f hf),
    mean_sub (f := fun u => (f u)^exponent n) (g := fun u => (f u)^(exponent n-1)) (f.continuous.pow _) (f.continuous.pow _), mean_e_zero f hf hnorm, add_zero]

lemma mean_first_power_ge_one {n : ℕ} (hn : 0 < n) [NeZero n]
    (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) : 1 ≤ mean f := by
  have hi := mean_mono (f := fun u => 1-f u) (g := fun u => e n (f u)) (continuous_const.sub f.continuous) (continuous_e_comp f hf)
    (fun u => e_lower hn (hf u))
  rw [mean_sub (f := fun _ => 1) (g := f) continuous_const f.continuous, mean_const, mean_e_zero f hf hnorm] at hi
  linarith

lemma norm_mean_ranges {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) :
    let m := mean (fun u => (f u) ^ exponent n) - 1
    let ell := mean (fun u => (f u) ^ (exponent n - 1)) - 1
    let t := mean (fun u => G n (f u))
    0 ≤ m ∧ 0 ≤ ell ∧ ell ≤ ((exponent n : ℝ) - 1) / exponent n * m ∧
      0 ≤ t ∧ t ≤ beta n * m := by
  dsimp only
  have hm : 0 ≤ mean (fun u => (f u)^exponent n) - 1 := by
    rw [← mean_M_of_normalized f hf hnorm]
    exact mean_nonneg (fun u => M_nonneg (by omega) (hf u))
  have ht : 0 ≤ mean (fun u => G n (f u)) :=
    mean_nonneg (fun u => (G_bounds (by omega) (hf u)).1)
  have htb := mean_mono (f := fun u => G n (f u)) (g := fun u => beta n*M n (f u)) ((contDiff_G hn).continuous.comp f.continuous)
    (continuous_const.mul (continuous_M_comp f hf)) (fun u => (G_bounds (by omega) (hf u)).2)
  rw [mean_const_mul, mean_M_of_normalized f hf hnorm] at htb
  refine ⟨hm, ?_, ?_, ht, htb⟩
  · by_cases hn4 : n = 4
    · simp [exponent, hn4, mean_const]
    · simpa only [exponent, ite_eq_right hn4, Nat.reduceSub, pow_one, sub_nonneg] using
        mean_first_power_ge_one (by omega) f hf hnorm
  · by_cases hn4 : n = 4
    · simp [exponent, hn4, mean_const]
    · simp only [exponent, ite_eq_right hn4, Nat.reduceSub, Nat.cast_ofNat, pow_one]
      have h := mean_mono (f := fun u => 2*f u) (g := fun u => (f u)^2+1)
        (continuous_const.mul f.continuous) ((f.continuous.pow 2).add continuous_const)
        (fun u => by nlinarith only [sq_nonneg (f u - 1)])
      rw [mean_const_mul, mean_add (f := fun u =>(f u)^2) (g := fun _ => 1) (f.continuous.pow 2) continuous_const, mean_const] at h
      linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma continuous_D {n : ℕ} (hn : 4 ≤ n) : Continuous (D n) :=
  ((continuous_id.pow _).sub continuous_const).sub (contDiff_G hn).continuous

lemma continuous_L {n : ℕ} (hn : 4 ≤ n) : Continuous (L n) :=
  continuous_const.mul (((((continuous_const.mul continuous_id).mul
    (contDiff_I hn).continuous).sub (continuous_const.mul ((contDiff_G hn).continuous.pow 2))).div_const _).add
      (((continuous_D hn).pow 2).div_const _))

lemma continuous_W_comp {n : ℕ} (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u) :
    Continuous (fun u => W n (f u)) :=
  ((f.continuous.pow _).sub (f.continuous.pow _)).add (continuous_e_comp f hf)

lemma mean_D {n : ℕ} (hn : 4 ≤ n) [NeZero n] (f : C(Sphere n, ℝ)) :
    mean (fun u => D n (f u)) = mean (fun u => (f u)^exponent n) - 1 -
      mean (fun u => G n (f u)) := by
  unfold D
  rw [mean_sub (f := fun u => (f u)^exponent n - 1) (g := fun u => G n (f u))
    ((f.continuous.pow _).sub continuous_const) ((contDiff_G hn).continuous.comp f.continuous),
    mean_sub (f := fun u => (f u)^exponent n) (g := fun _ => 1)
      (f.continuous.pow _) continuous_const, mean_const]

lemma mean_L {n : ℕ} (hn : 4 ≤ n) [NeZero n] (f : C(Sphere n, ℝ)) :
    mean (fun u => L n (f u)) = coefficient n *
      ((((n : ℝ)-1)*beta n^2 * mean (fun u => I n (f u)*f u) -
        2*n*mean (fun u => (G n (f u))^2))/(weight n*(2*n+8)) +
          mean (fun u => (D n (f u))^2)/(1-weight n)) := by
  have hG := (contDiff_G hn).continuous.comp f.continuous
  have hI := (contDiff_I hn).continuous.comp f.continuous
  have hD := (continuous_D hn).comp f.continuous
  unfold L
  rw [mean_const_mul,
    mean_add (f := fun u => (((n : ℝ)-1)*beta n^2*f u*I n (f u)-2*n*(G n (f u))^2)/(weight n*(2*n+8)))
      (g := fun u => (D n (f u))^2/(1-weight n))
      (((continuous_const.mul f.continuous).mul hI |>.sub (continuous_const.mul (hG.pow 2))).div_const _)
      ((hD.pow 2).div_const _),
    mean_div_const, mean_div_const,
    mean_sub (f := fun u => ((n : ℝ)-1)*beta n^2*f u*I n (f u))
      (g := fun u => 2*n*(G n (f u))^2)
      ((continuous_const.mul f.continuous).mul hI) (continuous_const.mul (hG.pow 2)),
    mean_const_mul]
  congr 2
  congr 1
  have he : (fun u : Sphere n => ((n : ℝ)-1)*beta n^2*f u*I n (f u)) =
      (fun u => ((n : ℝ)-1)*beta n^2*(I n (f u)*f u)) := by funext u; ring
  rw [he, mean_const_mul]

lemma Q_power_split {n : ℕ} (hn : 4 ≤ n) [NeZero n] (f : C(Sphere n, ℝ)) :
    Q n (toH n ⟨fun u => (f u)^exponent n, f.continuous.pow _⟩) =
      Q n (toH n ⟨fun u => G n (f u), (contDiff_G hn).continuous.comp f.continuous⟩) +
      Q n (toH n ⟨fun u => D n (f u), (continuous_D hn).comp f.continuous⟩) := by
  have he : (⟨fun u => (f u)^exponent n, f.continuous.pow _⟩ : C(Sphere n, ℝ)) =
      ContinuousMap.const (Sphere n) 1 +
      (⟨fun u => G n (f u), (contDiff_G hn).continuous.comp f.continuous⟩ : C(Sphere n, ℝ)) +
      ⟨fun u => D n (f u), (continuous_D hn).comp f.continuous⟩ := by
    ext u; simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.coe_mk, D]; ring
  rw [he, map_add, map_add, map_add, map_add, Q_constant, zero_add]

/-- Exact expectation reduction in the proof of the norm theorem. -/
lemma norm_reduction {n : ℕ} (hn : 4 ≤ n) [NeZero n] (g : Seminorm ℝ (Space n)) :
    coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x ^ exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      mean (fun u : Sphere n => L n (g u)) + coefficient n *
        (2*n*(mean (fun u : Sphere n => G n (g u)))^2/(weight n*(2*n+8)) -
          (mean (fun u : Sphere n => D n (g u)))^2/(1-weight n)) := by
  let f := restrictContinuous g (seminorm_continuous n g)
  let F : C(Sphere n, ℝ) := ⟨fun u => (f u)^exponent n, f.continuous.pow _⟩
  let GG : C(Sphere n, ℝ) := ⟨fun u => G n (f u), (contDiff_G hn).continuous.comp f.continuous⟩
  let DD : C(Sphere n, ℝ) := ⟨fun u => D n (f u), (continuous_D hn).comp f.continuous⟩
  have hs : Q n (toH n F) = Q n (toH n GG) + Q n (toH n DD) := Q_power_split hn f
  have hq := weighted_norm_bound (Q n (toH n GG)) (Q n (toH n DD))
    (weight_pos n) (weight_lt_one n)
  rw [← hs] at hq
  have hd := norm_Q_le_variance DD
  have hc := scalar_curvature hn g
  change (2*n : ℝ)*variance GG + (2*n+8 : ℝ)*‖Q n (toH n GG)‖^2 ≤
    ((n : ℝ)-1)*beta n^2 * mean (fun u => I n (f u)*f u) at hc
  have hp : 0 < (2*n+8 : ℝ) := by positivity
  have hcg : ‖Q n (toH n GG)‖^2 ≤
      (((n : ℝ)-1)*beta n^2 * mean (fun u => I n (f u)*f u) -
        (2*n : ℝ)*variance GG)/(2*n+8) := (le_div_iff₀ hp).mpr (by linarith)
  have hbound := hq.trans (add_le_add (div_le_div_of_nonneg_right hcg (weight_pos n).le)
    (div_le_div_of_nonneg_right hd (sub_nonneg.mpr (weight_lt_one n).le)))
  have hbound' := mul_le_mul_of_nonneg_left hbound (coefficient_pos n).le
  change coefficient n * ‖Q n (toH n F)‖^2 ≤ _
  refine hbound'.trans_eq ?_
  rw [show mean (fun u : Sphere n => L n (g u)) = mean (fun u => L n (f u)) from rfl,
    mean_L hn f]
  change coefficient n *
      (((((n : ℝ)-1)*beta n^2 * mean (fun u => I n (f u)*f u) -
        (2*n : ℝ)*(mean (fun u => (G n (f u))^2) - (mean (fun u => G n (f u)))^2)) /
        (2*n+8))/weight n +
      (mean (fun u => (D n (f u))^2) - (mean (fun u => D n (f u)))^2)/(1-weight n)) = _
  dsimp only [f, restrictContinuous, ContinuousMap.coe_mk]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma mean_square_remainder {k : ℝ} (hk : 0 < k) {m ell : ℝ}
    (hm : 0 ≤ m) (hl : 0 ≤ ell) (hkm : 0 ≤ k-1) (h : ell ≤ (k-1)/k*m) :
    (2*k-1)/k^2*m^2 ≤ m^2-ell^2 := by
  have hs : ell^2 ≤ ((k-1)/k*m)^2 :=
    (sq_le_sq₀ hl (mul_nonneg (div_nonneg hkm hk.le) hm)).mpr h
  have he : (2*k-1)/k^2*m^2 = m^2-((k-1)/k*m)^2 := by field_simp; ring
  rw [he]; linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma scalar_expectation {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u) :
    mean (fun u => L n (f u)) ≤ 2*mean (fun u => W n (f u)) ∧
      (mean (fun u => L n (f u)) = 2*mean (fun u => W n (f u)) ↔ ∀ u, f u = 1) := by
  have hL := (continuous_L hn).comp f.continuous
  have hW : Continuous (fun u => 2*W n (f u)) := continuous_const.mul (continuous_W_comp f hf)
  have hp : ∀ u, L n (f u) ≤ 2*W n (f u) := fun u => (pointwise n hn (hf u)).1
  have hm := mean_mono (f := fun u => L n (f u)) (g := fun u => 2*W n (f u)) hL hW hp
  rw [mean_const_mul] at hm
  refine ⟨hm, ?_, ?_⟩
  · intro he
    have hae : (fun u => L n (f u)) =ᵐ[sigma n] (fun u => 2*W n (f u)) := by
      apply (integral_eq_iff_of_ae_le (continuous_integrable hL) (continuous_integrable hW)
        (Eventually.of_forall hp)).mp
      change mean (fun u => L n (f u)) = mean (fun u => 2*W n (f u))
      rw [mean_const_mul]; exact he
    have heq := (hL.ae_eq_iff_eq (sigma n) hW).mp hae
    intro u
    exact (pointwise n hn (hf u)).2.mp (congrFun heq u)
  · intro he
    have heq : (fun u => L n (f u)) = (fun u => 2*W n (f u)) := by
      funext u; exact (pointwise n hn (hf u)).2.mpr (he u)
    rw [heq, mean_const_mul]

/-- The full arbitrary-norm estimate, including strictness.
It uses the actual spherical measure and the actual quadratic-removing Q. -/
theorem norm_estimate {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1) :
    coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x ^ exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 ∧
    (coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x ^ exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 =
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 ↔ ∀ u : Sphere n, g u = 1) := by
  let f := restrictContinuous g (seminorm_continuous n g)
  let m := mean (fun u => (f u)^exponent n)-1
  let ell := mean (fun u => (f u)^(exponent n-1))-1
  let t := mean (fun u => G n (f u))
  obtain ⟨hm, hl, hlm, ht, htb⟩ := norm_mean_ranges hn f hg hnorm
  have hcorr := scalar_correction hn hm ht htb
  have hk : 0 < (exponent n : ℝ) := by unfold exponent; split_ifs <;> norm_num
  have hkm : 0 ≤ (exponent n : ℝ)-1 := by unfold exponent; split_ifs <;> norm_num
  have hrem := mean_square_remainder hk hm hl hkm hlm
  have hred := norm_reduction hn g
  have hred' : coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x^exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      mean (fun u => L n (f u)) + m^2-ell^2 := by
    have hd : mean (fun u : Sphere n => D n (g u)) = m-t := mean_D hn f
    rw [hd] at hred
    exact hred.trans (by dsimp only [m, ell, t, f, restrictContinuous, ContinuousMap.coe_mk] at *; linarith)
  obtain ⟨hsc, hsce⟩ := scalar_expectation hn f hg
  have hw : mean (fun u => W n (f u)) = m-ell := by
    rw [mean_W_of_normalized f hg hnorm]
    dsimp only [m, ell]; ring
  have hend : 2*(m-ell)+m^2-ell^2 =
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 := by
    dsimp only [m, ell, f, restrictContinuous, ContinuousMap.coe_mk]; ring
  have hfinal : coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x^exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 :=
    hred'.trans (by rw [← hend]; rw [hw] at hsc; linarith)
  refine ⟨hfinal, ?_, ?_⟩
  · intro he
    apply hsce.mp
    rw [hw]
    rw [← hend] at he
    linarith
  · intro he
    have hpow : restrictContinuous (fun x => g x^exponent n) ((seminorm_continuous n g).pow _) =
        ContinuousMap.const (Sphere n) 1 := by ext u; simp [restrictContinuous, he u]
    rw [hpow, Q_constant, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    have hem : (fun u : Sphere n => (g u)^exponent n) = (fun _ => (1 : ℝ)) := by
      funext u; simp [he u]
    have hel : (fun u : Sphere n => (g u)^(exponent n-1)) = (fun _ => (1 : ℝ)) := by
      funext u; simp [he u]
    rw [hem, hel, sub_self]

end PettyProjection.Spherical
end

end OAI
