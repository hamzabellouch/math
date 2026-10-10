import Mathlib

namespace OAI

section
section
section

section

noncomputable section
open MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace

namespace TamingCompatibility.EuclideanEnergy
abbrev V := EuclideanSpace ℝ (Fin 4)
abbrev S := 𝓢(V,ℝ)
def e (i : Fin 4) : V := EuclideanSpace.single i 1

def coordinateDeriv (i : Fin 4) (f : S) : S := ∂_{e i} f

lemma second_partial_comm (i j : Fin 4) (f : S) :
    coordinateDeriv i (coordinateDeriv j f) = coordinateDeriv j (coordinateDeriv i f) := by
  ext x
  simp only [coordinateDeriv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((f.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  change (fderiv ℝ (fun y => fderiv ℝ f y (e j)) x) (e i) =
    (fderiv ℝ (fun y => fderiv ℝ f y (e i)) x) (e j)
  rw [fderiv_clm_apply hf (differentiableAt_const _),
    fderiv_clm_apply hf (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact ((f.smooth 2).contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num) _ _

lemma partial_mul_integral_swap (i j : Fin 4) (f g : S) :
    (∫ x, coordinateDeriv i f x * coordinateDeriv j g x) = ∫ x, coordinateDeriv j f x * coordinateDeriv i g x := by
  have hi := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) f (coordinateDeriv j g) (e i)
  have hj := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) f (coordinateDeriv i g) (e j)
  change (∫ x, f x * coordinateDeriv i (coordinateDeriv j g) x) = -(∫ x, coordinateDeriv i f x * coordinateDeriv j g x) at hi
  change (∫ x, f x * coordinateDeriv j (coordinateDeriv i g) x) = -(∫ x, coordinateDeriv j f x * coordinateDeriv i g x) at hj
  rw [second_partial_comm] at hi
  linarith

def codifferential (A B : S) (x : V) : V := WithLp.toLp 2
  ![-coordinateDeriv 2 A x - coordinateDeriv 3 B x, -coordinateDeriv 2 B x + coordinateDeriv 3 A x,
    coordinateDeriv 0 A x + coordinateDeriv 1 B x, coordinateDeriv 0 B x - coordinateDeriv 1 A x]

def gradientEnergy (A B : S) (x : V) : ℝ :=
  ∑ i : Fin 4, ((coordinateDeriv i A x)^2 + (coordinateDeriv i B x)^2)

lemma schwartz_mul_integrable (f g : S) : Integrable (fun x => f x * g x) := by
  exact (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) g.hasTemperateGrowth f).integrable

lemma schwartz_sq_integrable (f : S) : Integrable (fun x => (f x)^2) := by
  simpa only [pow_two] using schwartz_mul_integrable f f

lemma gradientEnergy_integrable (A B : S) : Integrable (gradientEnergy A B) := by
  exact integrable_finsetSum Finset.univ fun i _ =>
    (schwartz_sq_integrable (coordinateDeriv i A)).add (schwartz_sq_integrable (coordinateDeriv i B))

lemma codifferential_energy_pointwise (A B : S) (x : V) :
    ‖codifferential A B x‖^2 = gradientEnergy A B x +
      2 * (coordinateDeriv 2 A x * coordinateDeriv 3 B x - coordinateDeriv 3 A x * coordinateDeriv 2 B x +
        coordinateDeriv 0 A x * coordinateDeriv 1 B x - coordinateDeriv 1 A x * coordinateDeriv 0 B x) := by
  simp [codifferential, EuclideanSpace.real_norm_sq_eq, gradientEnergy, Fin.sum_univ_succ]
  ring

theorem codifferential_energy (A B : S) :
    (∫ x, ‖codifferential A B x‖^2) = ∫ x, gradientEnergy A B x := by
  have hm (i j : Fin 4) := schwartz_mul_integrable (coordinateDeriv i A) (coordinateDeriv j B)
  simp_rw [codifferential_energy_pointwise]
  have hC : Integrable (fun x =>
      coordinateDeriv 2 A x * coordinateDeriv 3 B x - coordinateDeriv 3 A x * coordinateDeriv 2 B x +
      coordinateDeriv 0 A x * coordinateDeriv 1 B x - coordinateDeriv 1 A x * coordinateDeriv 0 B x) :=
    (((hm 2 3).sub (hm 3 2)).add (hm 0 1)).sub (hm 1 0)
  calc
    _ = (∫ x, gradientEnergy A B x) +
        ∫ x, 2 * (coordinateDeriv 2 A x * coordinateDeriv 3 B x - coordinateDeriv 3 A x * coordinateDeriv 2 B x +
          coordinateDeriv 0 A x * coordinateDeriv 1 B x - coordinateDeriv 1 A x * coordinateDeriv 0 B x) :=
      integral_add (gradientEnergy_integrable A B) (hC.const_mul 2)
    _ = _ := by
      have hsub := integral_sub (((hm 2 3).sub (hm 3 2)).add (hm 0 1)) (hm 1 0)
      have hadd := integral_add ((hm 2 3).sub (hm 3 2)) (hm 0 1)
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hadd
      rw [integral_const_mul, hsub, hadd, integral_sub (hm 2 3) (hm 3 2),
        partial_mul_integral_swap 2 3 A B, partial_mul_integral_swap 0 1 A B]
      ring

end TamingCompatibility.EuclideanEnergy

namespace TamingCompatibility.EuclideanEnergy
abbrev Pair := EuclideanSpace ℝ (Fin 2)
def pair (a b : ℝ) : Pair := WithLp.toLp 2 ![a,b]
lemma pair_norm_sq (a b : ℝ) : ‖pair a b‖^2 = a^2 + b^2 := by
  simp [pair, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

def variableCodifferential (a : Fin 4 → V → Pair →L[ℝ] V)
    (b : V → Pair →L[ℝ] V) (A B : S) (x : V) : V :=
  codifferential A B x +
    (∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x))) +
    b x (pair (A x) (B x))

lemma norm_add_sq_le {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    ‖u + v‖^2 ≤ 2 * ‖u‖^2 + 2 * ‖v‖^2 := by
  have h := norm_add_le u v
  have hs := sq_nonneg (‖u‖ - ‖v‖)
  nlinarith [norm_nonneg (u+v), norm_nonneg u, norm_nonneg v]

lemma norm_sum_four_sq_le {E : Type*} [SeminormedAddCommGroup E] (f : Fin 4 → E) :
    ‖∑ i, f i‖^2 ≤ 4 * ∑ i, ‖f i‖^2 := by
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.reduceSucc, Fin.fin_one_eq_zero,
    Fin.sum_univ_zero, add_zero]
  have h := norm_add_sq_le (f 0 + f 1) (f 2 + f 3)
  have h1 := norm_add_sq_le (f 0) (f 1)
  have h2 := norm_add_sq_le (f 2) (f 3)
  simp only [add_assoc] at h
  linarith

lemma principalError_bound (a : Fin 4 → V → Pair →L[ℝ] V)
    (A B : S) (x : V) {δ : ℝ} (ha : ∀ i, ‖a i x‖ ≤ δ) :
    ‖∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x))‖^2 ≤
      4 * δ^2 * gradientEnergy A B x := by
  refine (norm_sum_four_sq_le _).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [gradientEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (a i x).le_opNorm (pair (coordinateDeriv i A x) (coordinateDeriv i B x))
  have hm := mul_le_mul_of_nonneg_right (ha i)
    (norm_nonneg (pair (coordinateDeriv i A x) (coordinateDeriv i B x)))
  have hh := pow_le_pow_left₀ (norm_nonneg _) (h.trans hm) 2
  rw [mul_pow, pair_norm_sq] at hh
  exact hh

lemma lowerError_bound (b : V → Pair →L[ℝ] V) (A B : S) (x : V) {C : ℝ}
    (hb : ‖b x‖ ≤ C) :
    ‖b x (pair (A x) (B x))‖^2 ≤ C^2 * ((A x)^2 + (B x)^2) := by
  have h := (b x).le_opNorm (pair (A x) (B x))
  have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg (pair (A x) (B x)))
  have hh := pow_le_pow_left₀ (norm_nonneg _) (h.trans hm) 2
  simpa only [mul_pow, pair_norm_sq] using hh

lemma variableCodifferential_pointwise (a : Fin 4 → V → Pair →L[ℝ] V)
    (b : V → Pair →L[ℝ] V) (A B : S) (x : V) {δ C : ℝ}
    (ha : ∀ i, ‖a i x‖ ≤ δ) (hb : ‖b x‖ ≤ C) :
    ‖codifferential A B x‖^2 ≤ 2 * ‖variableCodifferential a b A B x‖^2 +
      16 * δ^2 * gradientEnergy A B x + 4 * C^2 * ((A x)^2 + (B x)^2) := by
  let U : V := ∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x))
  let W : V := b x (pair (A x) (B x))
  have hid : codifferential A B x = variableCodifferential a b A B x + -(U+W) := by
    dsimp [variableCodifferential, U, W]
    abel
  have h := norm_add_sq_le (variableCodifferential a b A B x) (-(U+W))
  rw [← hid, norm_neg] at h
  have he := norm_add_sq_le U W
  have hu := principalError_bound a A B x ha
  have hw := lowerError_bound b A B x hb
  change ‖U‖^2 ≤ _ at hu
  change ‖W‖^2 ≤ _ at hw
  nlinarith

lemma codifferential_continuous (A B : S) : Continuous (codifferential A B) := by
  unfold codifferential
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
  fun_prop

lemma pair_continuous {D : Type*} [TopologicalSpace D] {f g : D → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => pair (f x) (g x)) := by
  unfold pair
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  fun_prop

lemma codifferential_integrable_sq (A B : S) :
    Integrable (fun x => ‖codifferential A B x‖^2) := by
  have hm (i j : Fin 4) := schwartz_mul_integrable (coordinateDeriv i A) (coordinateDeriv j B)
  simp_rw [codifferential_energy_pointwise]
  exact (gradientEnergy_integrable A B).add
    (((((hm 2 3).sub (hm 3 2)).add (hm 0 1)).sub (hm 1 0)).const_mul 2)

lemma variableCodifferential_integrable (a : Fin 4 → V → Pair →L[ℝ] V)
    (b : V → Pair →L[ℝ] V) (A B : S) {δ C : ℝ}
    (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) :
    Integrable (fun x => ‖variableCodifferential a b A B x‖^2) := by
  have hcont : Continuous (variableCodifferential a b A B) := by
    apply ((codifferential_continuous A B).add _).add
      (hbc.clm_apply (pair_continuous A.continuous B.continuous))
    apply continuous_finsetSum
    intro i _
    exact (hac i).clm_apply (pair_continuous (coordinateDeriv i A).continuous
      (coordinateDeriv i B).continuous)
  have hdom := (((codifferential_integrable_sq A B).const_mul 4).add
    ((gradientEnergy_integrable A B).const_mul (16*δ^2))).add
    (((schwartz_sq_integrable A).add (schwartz_sq_integrable B)).const_mul (2*C^2))
  refine hdom.mono' (hcont.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  dsimp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖variableCodifferential a b A B x‖))]
  let U : V := ∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x))
  let W : V := b x (pair (A x) (B x))
  have h := norm_add_sq_le (codifferential A B x + U) W
  have h' := norm_add_sq_le (codifferential A B x) U
  have hu := principalError_bound a A B x (ha x)
  have hw := lowerError_bound b A B x (hb x)
  change ‖U‖^2 ≤ _ at hu
  change ‖W‖^2 ≤ _ at hw
  change ‖(codifferential A B x + U) + W‖^2 ≤ _
  nlinarith

theorem local_garding (a : Fin 4 → V → Pair →L[ℝ] V)
    (b : V → Pair →L[ℝ] V) (A B : S) (C : ℝ)
    (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x‖ ≤ 1/8) (hb : ∀ x, ‖b x‖ ≤ C) :
    (∫ x, gradientEnergy A B x) ≤
      4 * (∫ x, ‖variableCodifferential a b A B x‖^2) +
      8 * C^2 * (∫ x, (A x)^2 + (B x)^2) := by
  have hint := variableCodifferential_integrable a b A B hac hbc ha hb
  have hpoint (x : V) := variableCodifferential_pointwise a b A B x
    (δ := 1/8) (ha x) (hb x)
  have hscalar := (schwartz_sq_integrable A).add (schwartz_sq_integrable B)
  have hc := codifferential_integrable_sq A B
  have h := integral_mono hc
    (((hint.const_mul 2).add ((gradientEnergy_integrable A B).const_mul (16*(1/8:ℝ)^2))).add
      (hscalar.const_mul (4*C^2))) hpoint
  dsimp only [Pi.add_apply] at h hscalar
  erw [integral_add ((hint.const_mul 2).add
    ((gradientEnergy_integrable A B).const_mul (16*(1/8:ℝ)^2))) (hscalar.const_mul (4*C^2)),
    integral_add (hint.const_mul 2) ((gradientEnergy_integrable A B).const_mul (16*(1/8:ℝ)^2)),
    integral_const_mul, integral_const_mul, integral_const_mul, codifferential_energy] at h
  simp only [Pi.add_apply] at h
  have hg : 0 ≤ ∫ x, gradientEnergy A B x := integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc0 : 0 ≤ C^2 * (∫ x, (A x)^2 + (B x)^2) :=
    mul_nonneg (sq_nonneg C) (integral_nonneg fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))
  nlinarith

end TamingCompatibility.EuclideanEnergy

end
end

end
end
end

end OAI
