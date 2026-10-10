import OAI.Probability.CubeShuffle.Basic

namespace OAI

namespace CubeShuffle
namespace DensityTransfer
open scoped BigOperators

noncomputable def applyKernel {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => ∑ y, (P x y : ℂ)*v y)

lemma applyKernel_apply {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) (x : X) :
    applyKernel P v x = ∑ y, (P x y : ℂ)*v y := rfl

lemma applyKernel_add {X : Type*} [Fintype X] (P Q : X → X → ℝ)
    (v : EuclideanSpace ℂ X) :
    applyKernel (fun x y => P x y+Q x y) v = applyKernel P v+applyKernel Q v := by
  ext x
  simp only [applyKernel_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib]
  rfl

lemma kernel_component_sq {X : Type*} [Fintype X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (v : EuclideanSpace ℂ X) (x : X) :
    ‖applyKernel P v x‖^2 ≤ (∑ y, P x y) * ∑ y, P x y*‖v y‖^2 := by
  have hs : ‖applyKernel P v x‖ ≤ ∑ y, P x y*‖v y‖ := by
    rw [applyKernel_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro y _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hP x y)]
  apply (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun y _ => hP x y) (fun y _ => mul_nonneg (hP x y) (sq_nonneg _))
    (fun y _ => by ring_nf; exact le_rfl)

/-- The finite Schur test, proved directly with the actual row/column sums. -/
lemma schur_bound {X : Type*} [Fintype X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrow : ∀ x, ∑ y, P x y ≤ δ) (hcol : ∀ y, ∑ x, P x y ≤ δ)
    (v : EuclideanSpace ℂ X) : ‖applyKernel P v‖ ≤ δ*‖v‖ := by
  have hsq : ‖applyKernel P v‖^2 ≤ δ^2*‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ x, δ * ∑ y, P x y*‖v y‖^2 := by
        apply Finset.sum_le_sum
        intro x _
        apply (kernel_component_sq P hP v x).trans
        exact mul_le_mul_of_nonneg_right (hrow x)
          (Finset.sum_nonneg (fun y _ => mul_nonneg (hP x y) (sq_nonneg _)))
      _ = δ * ∑ y, (∑ x, P x y)*‖v y‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        exact (Finset.sum_mul Finset.univ _ _).symm
      _ ≤ δ * ∑ y, δ*‖v y‖^2 := by
        apply mul_le_mul_of_nonneg_left _ hδ
        exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _))
      _ = _ := by rw [←Finset.mul_sum]; ring
  have hn := norm_nonneg (applyKernel P v)
  have hr := mul_nonneg hδ (norm_nonneg v)
  nlinarith

/-- Bessel's inequality controls the total stretch of any orthonormal family
by the squared Hilbert--Schmidt norm of the finite real kernel. -/
lemma hilbert_schmidt_family {X I : Type*} [Fintype X] [Fintype I]
    (P : X → X → ℝ) (v : I → EuclideanSpace ℂ X) (hv : Orthonormal ℂ v) :
    (∑ i, ‖applyKernel P (v i)‖^2) ≤ ∑ x, ∑ y, (P x y)^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  let w : EuclideanSpace ℂ X := WithLp.toLp 2 (fun y => (P x y : ℂ))
  have he (i : I) : ‖applyKernel P (v i) x‖ = ‖inner ℂ (v i) w‖ := by
    rw [norm_inner_symm]
    congr 1
    simp only [applyKernel_apply,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro y _
    simp [w,RCLike.inner_apply,mul_comm]
  simp_rw [he]
  have h := hv.sum_inner_products_le (s := Finset.univ) w
  apply h.trans_eq
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro y _
  simp [w,Complex.norm_real,Real.norm_eq_abs,sq_abs]

end DensityTransfer
end CubeShuffle

namespace CubeShuffle
namespace DensityTransfer
open scoped BigOperators

lemma tail_density_pointwise (t a z : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hz : 0 < z) :
    (if z < t then t else 0) ≤ t^(1+a)*z^(-a) := by
  split_ifs with h
  · rw [Real.rpow_neg hz.le,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz a)).mpr
    rw [Real.rpow_add (lt_trans hz h),Real.rpow_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.le h.le ha) ht
  · positivity

lemma tail_density_mean {X : Type*} [Fintype X] (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (a z : ℝ) (ha : 0 ≤ a) (hz : 0 < z) :
    finiteMean (fun x => if z < f x then f x else 0) ≤ finiteMean (fun x => f x^(1+a))*z^(-a) := by
  rw [←finiteMean_mul_const]
  exact finiteMean_mono (fun x => tail_density_pointwise (f x) a z (hf x) ha hz)

noncomputable def tailKernel {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) : X → X → ℝ :=
  fun x y => if z < (Fintype.card X:ℝ)*P x y then P x y else 0

noncomputable def headKernel {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) : X → X → ℝ :=
  fun x y => if z < (Fintype.card X:ℝ)*P x y then 0 else P x y

lemma tail_add_head {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) :
    (fun x y => tailKernel P z x y+headKernel P z x y) = P := by
  funext x y
  unfold tailKernel headKernel
  split_ifs <;> simp

lemma tailKernel_nonneg {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (x y : X) : 0 ≤ tailKernel P z x y := by
  unfold tailKernel
  split_ifs <;> simp only [hP,le_refl]

lemma tailKernel_row {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M) (x : X) :
    ∑ y, tailKernel P z x y ≤ M*z^(-a) := by
  have hn : (Fintype.card X:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : finiteMean (fun y => if z < (Fintype.card X:ℝ)*P x y then
      (Fintype.card X:ℝ)*P x y else 0) = ∑ y, tailKernel P z x y := by
    unfold finiteMean
    calc
      _ = (∑ y, (Fintype.card X:ℝ)*tailKernel P z x y)/(Fintype.card X:ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : z < (Fintype.card X:ℝ)*P x y
        · simp only [tailKernel,hy,↓reduceIte]
        · simp only [tailKernel,hy,↓reduceIte,mul_zero]
      _ = _ := by rw [←Finset.mul_sum]; field_simp
  rw [←he]
  exact (tail_density_mean _ (fun y => mul_nonneg (Nat.cast_nonneg _) (hP x y)) a z ha hz).trans
    (mul_le_mul_of_nonneg_right (hM x) (Real.rpow_nonneg hz.le _))

lemma tailKernel_schur {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hsym : ∀ x y, P x y = P y x)
    (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z) (hM0 : 0 ≤ M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M)
    (v : EuclideanSpace ℂ X) :
    ‖applyKernel (tailKernel P z) v‖ ≤ (M*z^(-a))*‖v‖ := by
  apply schur_bound _ (tailKernel_nonneg P z hP) _ (by positivity)
    (tailKernel_row P hP a z M ha hz hM)
  intro y
  have hs : (fun x => tailKernel P z x y) = (fun x => tailKernel P z y x) := by
    funext x
    simp only [tailKernel,hsym x y]
  rw [hs]
  exact tailKernel_row P hP a z M ha hz hM y

lemma headKernel_hs {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (z : ℝ) (hz : 0 ≤ z) :
    (∑ x, ∑ y, (headKernel P z x y)^2) ≤ z := by
  have hn : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have he (x y : X) : (headKernel P z x y)^2 ≤ (z/(Fintype.card X:ℝ))*P x y := by
    unfold headKernel
    split_ifs with h
    · simp only [zero_pow (by omega : (2:ℕ) ≠ 0)]
      exact mul_nonneg (div_nonneg hz hn.le) (hP x y)
    · have h' : (Fintype.card X:ℝ)*P x y ≤ z := le_of_not_gt h
      have hh := mul_le_mul_of_nonneg_right h' (hP x y)
      rw [show (z/(Fintype.card X:ℝ))*P x y = (z*P x y)/(Fintype.card X:ℝ) by ring]
      apply (le_div_iff₀ hn).mpr
      nlinarith
  calc
    _ ≤ ∑ x, ∑ y, (z/(Fintype.card X:ℝ))*P x y :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => he x y))
    _ = z := by
      simp only [←Finset.mul_sum,hrow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp

end DensityTransfer
end CubeShuffle

namespace CubeShuffle
namespace DensityTransfer
open scoped BigOperators

/-- Source FAC.7: multiplicity amplification in a finite symmetric kernel.
The orthonormal family is the exact linear-algebra meaning of the `m` equivalent
maximizing singular vectors; no spectral producer for the shuffle is assumed. -/
theorem multiplicity_amplification {X I : Type*} [Fintype X] [Nonempty X]
    [Fintype I] [Nonempty I] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hsym : ∀ x y, P x y = P y x)
    (hrow : ∀ x, ∑ y, P x y = 1) (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z) (hM0 : 0 ≤ M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M)
    (v : I → EuclideanSpace ℂ X) (hv : Orthonormal ℂ v)
    (μ : ℝ) (hvμ : ∀ i, μ ≤ ‖applyKernel P (v i)‖) :
    μ ≤ M*z^(-a)+Real.sqrt (z/(Fintype.card I:ℝ)) := by
  let δ : ℝ := M*z^(-a)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hm : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  change μ ≤ δ+_
  by_cases hμ : μ ≤ δ
  · exact hμ.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hmd : 0 ≤ μ-δ := by linarith
  have hsmall (i : I) : μ-δ ≤ ‖applyKernel (headKernel P z) (v i)‖ := by
    have hr := tailKernel_schur P hP hsym a z M ha hz hM0 hM (v i)
    rw [hv.norm_eq_one i,mul_one] at hr
    have he := applyKernel_add (tailKernel P z) (headKernel P z) (v i)
    rw [tail_add_head] at he
    have hn := norm_add_le (applyKernel (tailKernel P z) (v i)) (applyKernel (headKernel P z) (v i))
    rw [←he] at hn
    have hh := hvμ i
    change ‖applyKernel (tailKernel P z) (v i)‖ ≤ δ at hr
    linarith
  have hsum : (Fintype.card I:ℝ)*(μ-δ)^2 ≤ z := by
    calc
      _ = ∑ i : I, (μ-δ)^2 := by simp
      _ ≤ ∑ i : I, ‖applyKernel (headKernel P z) (v i)‖^2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hmd (hsmall i) 2)
      _ ≤ ∑ x, ∑ y, (headKernel P z x y)^2 := hilbert_schmidt_family _ v hv
      _ ≤ z := headKernel_hs P hP hrow z hz.le
  have hsq : (μ-δ)^2 ≤ z/(Fintype.card I:ℝ) := (le_div_iff₀ hm).mpr (by nlinarith)
  have hs := (Real.le_sqrt hmd (div_nonneg hz.le hm.le)).mpr hsq
  linarith

end DensityTransfer
end CubeShuffle

end OAI
