import Mathlib
import OAI.Probability.SKRatio.FiniteChain.DiscreteDistanceNonneg
import OAI.Probability.SKRatio.Matrices.GaussianTails
import OAI.Probability.SKRatio.Gaussian.Planted

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma sum_edges_spin (x : Spin n) :
    2*∑ e : Edge n, spin x e.1.1*spin x e.1.2 = (∑ i,spin x i)^2-n := by
  have h (i j : Fin n) : spin x i*coupling (fun _ : Edge n => 1) i j*spin x j =
      spin x i*spin x j - if i=j then 1 else 0 := by
    by_cases hij : i=j
    · subst j
      simp only [coupling_diag,mul_zero,zero_mul,↓reduceIte]
      nlinarith [spin_sq x i]
    · simp only [coupling]
      split_ifs <;> simp_all only [mul_one,sub_zero]
      omega
  have hs := hamiltonian_edges (fun _ : Edge n => 1) x
  have hss : (∑ i,spin x i)^2 = ∑ i : Fin n, ∑ j : Fin n, spin x i*spin x j := by
    rw [pow_two,Finset.sum_mul_sum]
  simp only [hamiltonian,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] at hs
  change (1/2:ℝ)*(∑ i,∑ j,spin x i*coupling (fun _ : Edge n => 1) i j*spin x j) =
    ∑ e : Edge n,spin x e.1.1*1*spin x e.1.2 at hs
  simp only [h,Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hs
  rw [hss]
  linarith

lemma weight_pair_linear (g : Disorder n) (x y : Spin n) :
    weight g 0 x*weight g 0 y = exp (∑ e : Edge n,
      (spin x e.1.1*spin x e.1.2+spin y e.1.1*spin y e.1.2)*g e) := by
  rw [weight_linear,weight_linear,←exp_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  change _ = (spinValue (x e.1.1)*spinValue (x e.1.2)+
    spinValue (y e.1.1)*spinValue (y e.1.2))*g e
  ring

lemma weight_pair_integrable (β : ℝ) (x y : Spin n) :
    Integrable (fun g => weight g 0 x*weight g 0 y) (disorderLaw β n) := by
  simp_rw [weight_pair_linear]
  exact integrable_exp_linear _ _ _

lemma integral_weight_pair (β : ℝ) (x y : Spin n) :
    (∫ g, weight g 0 x*weight g 0 y ∂disorderLaw β n) =
      exp (2*normalizingExponent β n + (β^2/n)*
        ∑ e : Edge n, spin (signProduct x y) e.1.1*spin (signProduct x y) e.1.2) := by
  simp_rw [weight_pair_linear]
  rw [disorderLaw,integral_exp_linear]
  congr 1
  have hv : (Real.toNNReal (β^2/(n:ℝ)) : ℝ) = β^2/n :=
    Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have he (e : Edge n) : (spin x e.1.1*spin x e.1.2+spin y e.1.1*spin y e.1.2)^2 =
      2+2*(spin (signProduct x y) e.1.1*spin (signProduct x y) e.1.2) := by
    rw [add_sq,mul_pow,mul_pow,spin_sq,spin_sq,spin_sq,spin_sq,spin_signProduct,spin_signProduct]
    ring
  simp only [mul_zero,zero_add,hv,he,
    show ∀ a b : ℝ, a*(2+2*b)/2 = a+a*b from by intros; ring,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,
    normalizingExponent]
  ring

lemma partition_square_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun g : Disorder n => (partition g 0)^2) (disorderLaw β n) := by
  have he (g : Disorder n) : partition g 0^2 =
      ∑ x : Spin n, ∑ y : Spin n,weight g 0 x*weight g 0 y := by
    rw [pow_two,partition,Finset.sum_mul_sum]
  simp_rw [he]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => weight_pair_integrable β x y))

lemma sign_sum_exp (t : ℝ) (n : ℕ) :
    (∑ x : Spin n, exp (t*∑ i,spin x i)) = (2*cosh t)^n := by
  simp_rw [Finset.mul_sum,exp_sum]
  have he : (∑ x : Spin n, ∏ i, exp (t*spin x i)) =
      ∏ _i : Fin n, ∑ b : Bool, exp (t*spinValue b) := by
    simpa only [spin,spinValue] using
      (Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => exp (t*spinValue b))).symm
  rw [he]
  have hB : (∑ b : Bool, exp (t*spinValue b)) = 2*cosh t := by
    simp [spinValue,cosh_eq]
    ring
  simp only [hB,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma sign_square_exp_bound {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    (∑ x : Spin n, exp ((β^2/(2*n))*(∑ i,spin x i)^2)) ≤ 2*(2:ℝ)^n := by
  by_cases hn : n=0
  · subst n
    norm_num [Spin]
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let a := β/sqrt n
  have ha : a^2 = β^2/n := by
    dsimp [a]
    rw [div_pow,sq_sqrt hnR.le]
  have he (x : Spin n) : exp ((β^2/(2*n))*(∑ i,spin x i)^2) =
       ∫ z : ℝ, exp ((a*∑ i,spin x i)*z) ∂gaussianReal 0 1 := by
    have hm := mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1)
      (by simp) (a*∑ i,spin x i)
    simp only [mgf,id_eq,NNReal.coe_one,one_mul] at hm
    rw [hm,mul_pow,ha]
    congr 1
    ring
  simp_rw [he]
  rw [←integral_finsetSum _ (fun x _ => integrable_exp_mul_gaussianReal (a*∑ i,spin x i))]
  have he' (z : ℝ) : (∑ x : Spin n, exp ((a*∑ i,spin x i)*z)) = (2*cosh (a*z))^n := by
    have hh (x : Spin n) : (a*∑ i,spin x i)*z = (a*z)*∑ i,spin x i := by ring
    simp_rw [hh]
    exact sign_sum_exp _ _
  simp_rw [he']
  have hb (z : ℝ) : (2*cosh (a*z))^n ≤ (2:ℝ)^n*exp (z^2/4) := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      cosh (a*z)^n ≤ exp ((a*z)^2/2)^n := pow_le_pow_left₀ (cosh_pos _).le (cosh_le_exp_half_sq _) n
      _ = exp (β^2*z^2/2) := by
        rw [←exp_nat_mul,mul_pow,ha]
        congr 1
        field_simp
      _ ≤ exp (z^2/4) := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hβ (sq_nonneg z)])
  have hi : Integrable (fun z : ℝ => (2*cosh (a*z))^n) (gaussianReal 0 1) := by
    have hh := integrable_finsetSum Finset.univ
      (fun (x : Spin n) _ => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a*∑ i,spin x i))
    simpa only [he'] using hh
  calc
    _ ≤ ∫ z : ℝ, (2:ℝ)^n*exp (z^2/4) ∂gaussianReal 0 1 :=
      integral_mono hi (SKRatioGaussian.gaussian_square_exp_integrable.const_mul _) hb
    _ ≤ (2:ℝ)^n*2 := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left SKRatioGaussian.gaussian_square_exp_integral (by positivity)
    _ = _ := mul_comm _ _

lemma partition_second_moment {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    (∫ g : Disorder n, (partition g 0)^2 ∂disorderLaw β n) ≤
      2*((2:ℝ)^n*exp (normalizingExponent β n))^2 := by
  have he (g : Disorder n) : partition g 0^2 =
      ∑ x : Spin n, ∑ y : Spin n,weight g 0 x*weight g 0 y := by
    rw [pow_two,partition,Finset.sum_mul_sum]
  simp_rw [he]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => weight_pair_integrable β x y))]
  simp_rw [integral_finsetSum _ (fun y _ => weight_pair_integrable β _ y),integral_weight_pair]
  let f : Spin n → ℝ := fun z => exp (2*normalizingExponent β n +(β^2/n)*
      ∑ e : Edge n,spin z e.1.1*spin z e.1.2)
  have heq (x : Spin n) : (∑ y : Spin n,f (signProduct x y)) = ∑ z : Spin n,f z :=
    Equiv.sum_comp ((signProduct_involutive x).toPerm) f
  change (∑ x : Spin n, ∑ y : Spin n,f (signProduct x y)) ≤ _
  simp only [heq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  have hb (z : Spin n) : f z ≤ exp (2*normalizingExponent β n)*
      exp ((β^2/(2*n))*(∑ i,spin z i)^2) := by
    dsimp [f]
    rw [←exp_add]
    apply exp_le_exp.mpr
    have hv := div_nonneg (sq_nonneg β) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hsum := sum_edges_spin z
    have hle : ∑ e : Edge n,spin z e.1.1*spin z e.1.2 ≤ (∑ i,spin z i)^2/2 := by
      linarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]
    have hh := mul_le_mul_of_nonneg_left hle hv
    have hid : (β^2/n)*((∑ i,spin z i)^2/2) = (β^2/(2*n))*(∑ i,spin z i)^2 := by ring
    rw [hid] at hh
    linarith
  calc
    _ ≤ (2:ℝ)^n * (exp (2*normalizingExponent β n)*
        ∑ z : Spin n, exp ((β^2/(2*n))*(∑ i,spin z i)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun z _ => hb z)
    _ ≤ (2:ℝ)^n*(exp (2*normalizingExponent β n)*(2*(2:ℝ)^n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sign_square_exp_bound hβ n)
        (exp_pos _).le) (by positivity)
    _ = _ := by
      rw [show (2:ℝ)*normalizingExponent β n = normalizingExponent β n+normalizingExponent β n by ring,
        exp_add]
      ring

lemma partition_lower_positive_probability {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    (1/8:ℝ) ≤ (disorderLaw β n).real
      {g : Disorder n | ((2:ℝ)^n*exp (normalizingExponent β n))/2 ≤ partition g 0} := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  have hM : 0 < M := by dsimp [M]; positivity
  let A := {g : Disorder n | M/2 ≤ partition g 0}
  have hA : MeasurableSet A := measurableSet_le measurable_const (continuous_partition 0).measurable
  let I : Disorder n → ℝ := A.indicator 1
  have hI : Integrable I (disorderLaw β n) := (integrable_const (1:ℝ)).indicator hA
  have hi : (∫ g, I g ∂disorderLaw β n) = (disorderLaw β n).real A := integral_indicator_one hA
  have hp (g : Disorder n) : partition g 0 ≤ M/2+(partition g 0)^2/(8*M)+2*M*I g := by
    by_cases hg : g ∈ A
    · have he : I g=1 := Set.indicator_of_mem hg 1
      rw [he,mul_one]
      have hsq := sq_nonneg (partition g 0-4*M)
      have hb : partition g 0-2*M ≤ partition g 0^2/(8*M) := by
        apply (le_div_iff₀ (show 0 < 8*M by positivity)).mpr
        nlinarith only [hsq]
      linarith only [hb,hM]
    · have he : I g=0 := Set.indicator_of_notMem hg 1
      rw [he,mul_zero,add_zero]
      have hz : partition g 0 < M/2 := lt_of_not_ge hg
      exact hz.le.trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by positivity)))
  have hineq := integral_mono (partition_integrable β n)
    (((integrable_const (M/2)).add ((partition_square_integrable β n).div_const (8*M))).add
      (hI.const_mul (2*M))) hp
  simp only [Pi.add_apply] at hineq
  have hsum : Integrable (fun g : Disorder n => M/2+partition g 0^2/(8*M))
      (disorderLaw β n) := (integrable_const _).add ((partition_square_integrable β n).div_const _)
  rw [integral_add hsum (hI.const_mul (2*M)),
    integral_add (integrable_const (M/2)) ((partition_square_integrable β n).div_const (8*M)),
    integral_const,probReal_univ,smul_eq_mul,one_mul,integral_div,integral_const_mul,hi,
    integral_partition] at hineq
  have hs := partition_second_moment hβ n
  change _ ≤ 2*M^2 at hs
  change M ≤ M/2+_+2*M*(disorderLaw β n).real A at hineq
  have hdiv : (∫ g : Disorder n, partition g 0^2 ∂disorderLaw β n)/(8*M) ≤ M/4 := by
    apply (div_le_iff₀ (show 0 < 8*M by positivity)).mpr
    nlinarith only [hs]
  change (1/8:ℝ) ≤ (disorderLaw β n).real A
  nlinarith only [hineq,hdiv,hM]

end SKRatio.Planted

end
end

end OAI
