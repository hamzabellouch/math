import OAI.Geometry.ProjectionBodies.NormEstimates

namespace OAI

noncomputable section
open Set Filter Topology Function
namespace PettyProjection.Spherical

/-- Positive part to a natural power; the endpoint is fixed to zero. -/
def posPower (r : ℕ) (x : ℝ) : ℝ := if 0 < x then x^r else 0

lemma posPower_hasDerivAt {r : ℕ} (hr : 2 ≤ r) (x : ℝ) :
    HasDerivAt (posPower r) ((r : ℝ)*posPower (r-1) x) x := by
  have hd (z : ℝ) : HasDerivAt (fun a : ℝ => (a-1)^r) ((r : ℝ)*(z-1)^(r-1)) z := by
    convert! ((hasDerivAt_id z).sub_const 1).pow r using 1
    simp
  have hp := Scalar.paste_hasDerivAt (fun z _ => hd z)
    (by simp [show r ≠ 0 by omega]) (by simp [show r-1 ≠ 0 by omega]) (x+1)
  have h := hp.comp x ((hasDerivAt_id x).add_const 1)
  convert! h using 1
  · funext z; simp [posPower]
  · simp [posPower, mul_ite]

lemma posPower_contDiff_one {r : ℕ} (hr : 2 ≤ r) : ContDiff ℝ 1 (posPower r) := by
  have hd (z : ℝ) : HasDerivAt (fun a : ℝ => (a-1)^r) ((r : ℝ)*(z-1)^(r-1)) z := by
    convert! ((hasDerivAt_id z).sub_const 1).pow r using 1
    simp
  have h := Scalar.paste_contDiff_one (fun z _ => hd z)
    (by simp [show r ≠ 0 by omega]) (by simp [show r-1 ≠ 0 by omega])
    (by fun_prop)
  have hc := h.comp (contDiff_id.add contDiff_const : ContDiff ℝ 1 (fun x : ℝ => x+1))
  convert! hc using 1
  ext x
  simp [posPower]

lemma posPower_contDiff_two {r : ℕ} (hr : 3 ≤ r) : ContDiff ℝ 2 (posPower r) := by
  have he : deriv (posPower r) = fun x => (r : ℝ)*posPower (r-1) x :=
    funext fun x => (posPower_hasDerivAt (by omega) x).deriv
  change ContDiff ℝ (1+1) (posPower r)
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (posPower_hasDerivAt (by omega) x).differentiableAt, ?_, ?_⟩
  · simp
  · rw [he]
    exact contDiff_const.mul (posPower_contDiff_one (by omega))

lemma abs_pow_posPower {r : ℕ} (hr : 0 < r) (x : ℝ) :
    |x|^r = posPower r x + posPower r (-x) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [posPower, abs_of_neg hx, not_lt.mpr hx.le, neg_pos.mpr hx]
  · simp [posPower, hr.ne']
  · simp [posPower, abs_of_pos hx, hx, not_lt.mpr (neg_nonpos.mpr hx.le)]

lemma abs_pow_contDiff_two {r : ℕ} (hr : 3 ≤ r) : ContDiff ℝ 2 (fun x : ℝ => |x|^r) := by
  have he : (fun x : ℝ => |x|^r) = fun x => posPower r x+posPower r (-x) :=
    funext (abs_pow_posPower (by omega))
  rw [he]
  exact (posPower_contDiff_two hr).add ((posPower_contDiff_two hr).comp contDiff_neg)

lemma abs_pow_hasDerivAt {r : ℕ} (hr : 2 ≤ r) (x : ℝ) :
    HasDerivAt (fun x : ℝ => |x|^r) ((r : ℝ)*x*|x|^(r-2)) x := by
  have h := (posPower_hasDerivAt hr x).add ((posPower_hasDerivAt hr (-x)).comp x (hasDerivAt_neg x))
  have he : (fun x : ℝ => |x|^r) = fun x => posPower r x+posPower r (-x) :=
    funext (abs_pow_posPower (by omega))
  rw [he]
  convert! h using 1
  have hp : r-1 = (r-2)+1 := by omega
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp only [posPower, ite_eq_right (not_lt.mpr hx.le), ite_eq_left (neg_pos.mpr hx),
      abs_of_neg hx, hp, pow_succ]
    ring
  · simp [posPower]
  · simp only [posPower, ite_eq_left hx, ite_eq_right (not_lt.mpr (neg_nonpos.mpr hx.le)),
      abs_of_pos hx, hp, pow_succ]
    ring

lemma abs_pow_second_deriv {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (r : ℝ)*x*|x|^(r-2))
      ((r : ℝ)*((r : ℝ)-1)*|x|^(r-2)) x := by
  have he : (fun x : ℝ => (r : ℝ)*x*|x|^(r-2)) =
      fun x => (r : ℝ)*(posPower (r-1) x - posPower (r-1) (-x)) := by
    funext z
    have hp : r-1 = (r-2)+1 := by omega
    rcases lt_trichotomy z 0 with hz | rfl | hz
    · simp only [posPower, ite_eq_right (not_lt.mpr hz.le), ite_eq_left (neg_pos.mpr hz),
        abs_of_neg hz, hp, pow_succ]; ring
    · simp [posPower]
    · simp only [posPower, ite_eq_left hz, ite_eq_right (not_lt.mpr (neg_nonpos.mpr hz.le)),
        abs_of_pos hz, hp, pow_succ]; ring
  rw [he]
  have h := ((posPower_hasDerivAt (show 2 ≤ r-1 by omega) x).sub
    ((posPower_hasDerivAt (show 2 ≤ r-1 by omega) (-x)).comp x (hasDerivAt_neg x))).const_mul (r : ℝ)
  convert! h using 1
  rw [show r-1-1 = r-2 by omega, Nat.cast_sub (by omega), Nat.cast_one,
    abs_pow_posPower (show 0 < r-2 by omega)]
  ring

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma inner_generator {n : ℕ} (u x : Space n) (i j : Fin n) :
    ⟪u, generator n i j x⟫ = x i*u j-x j*u i := by
  simp [generator_apply, inner_sub_right, inner_smul_right,
    EuclideanSpace.inner_single_right]

lemma sum_inner_generator_sq {n : ℕ} (u x : Space n) :
    ∑ i : Fin n, ∑ j : Fin n, ⟪u, generator n i j x⟫^2 =
      2*(‖u‖^2*‖x‖^2-⟪u,x⟫^2) := by
  simp_rw [inner_generator]
  have he (i j : Fin n) : (x i*u j-x j*u i)^2 =
      x i^2*u j^2+x j^2*u i^2-2*(x i*u i)*(x j*u j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
  simp only [← Finset.mul_sum]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hi : ⟪u,x⟫ = ∑ i, x i*u i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [hi]
  ring

lemma rotDeriv_scalar_linear {n : ℕ} (T : Space n →L[ℝ] Space n)
    (L : Space n →L[ℝ] ℝ) {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (x : Space n) :
    rotDeriv T (f ∘ L) x = f' (L x)*L (T x) := by
  have h := (hf (L x)).comp_hasFDerivAt x L.hasFDerivAt
  simp only [rotDeriv, h.fderiv, smul_apply, smul_eq_mul]

lemma rotDeriv_scalar_linear_twice {n : ℕ} (T : Space n →L[ℝ] Space n)
    (L : Space n →L[ℝ] ℝ) {f f' f'' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (x : Space n) :
    rotDeriv T (rotDeriv T (f ∘ L)) x =
      f'' (L x)*(L (T x))^2+f' (L x)*L (T (T x)) := by
  have he : rotDeriv T (f ∘ L) = fun y => f' (L y)*L (T y) :=
    funext (rotDeriv_scalar_linear T L hf)
  rw [he]
  have hd := ((hf' (L x)).comp_hasFDerivAt x L.hasFDerivAt).mul
    (L.comp T).hasFDerivAt
  change fderiv ℝ ((f' ∘ L) * (fun y => (L.comp T) y)) x (T x) = _
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, comp_apply]
  ring

lemma casimir_scalar_inner {n : ℕ} (u x : Space n) {f f' f'' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) :
    casimir (fun y => f ⟪u,y⟫) x =
      f'' ⟪u,x⟫*(‖u‖^2*‖x‖^2-⟪u,x⟫^2)-
        ((n : ℝ)-1)*f' ⟪u,x⟫*⟪u,x⟫ := by
  change casimir (f ∘ (innerSL ℝ u)) x = _
  unfold casimir
  simp_rw [rotDeriv_scalar_linear_twice _ (innerSL ℝ u) hf hf',
    innerSL_apply_apply, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_inner_generator_sq]
  simp_rw [← inner_sum, sum_generator_square, inner_smul_right]
  ring

lemma posPower_mul {r : ℕ} (x : ℝ) :
    posPower r x*x = posPower (r+1) x := by
  by_cases hx : 0 < x <;> simp [posPower, hx, pow_succ]

lemma posPower_mul_sq {r : ℕ} (x : ℝ) :
    posPower r x*x^2 = posPower (r+2) x := by
  rw [pow_two, ← mul_assoc, posPower_mul, posPower_mul]

lemma casimir_posPower_inner {n r : ℕ} (hr : 3 ≤ r) (u x : Sphere n) :
    casimir (fun y => posPower r ⟪(u : Space n),y⟫) x =
      (r : ℝ)*((r : ℝ)-1)*posPower (r-2) ⟪(u : Space n),(x : Space n)⟫ -
      eigenvalue n r*posPower r ⟪(u : Space n),(x : Space n)⟫ := by
  have hd (t : ℝ) : HasDerivAt (fun z => (r : ℝ)*posPower (r-1) z)
      ((r : ℝ)*((r : ℝ)-1)*posPower (r-2) t) t := by
    convert! (posPower_hasDerivAt (show 2 ≤ r-1 by omega) t).const_mul (r : ℝ) using 1
    rw [show r-1-1 = r-2 by omega, Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [casimir_scalar_inner _ _ (posPower_hasDerivAt (by omega)) hd,
    norm_coe, norm_coe]
  simp only [one_pow, mul_one]
  have h₁ := posPower_mul (r := r-1) ⟪(u : Space n),(x : Space n)⟫
  have h₂ := posPower_mul_sq (r := r-2) ⟪(u : Space n),(x : Space n)⟫
  rw [show r-1+1 = r by omega] at h₁
  rw [show r-2+2 = r by omega] at h₂
  unfold eigenvalue
  calc
    _ = (r : ℝ)*((r : ℝ)-1)*posPower (r-2) ⟪(u : Space n),(x : Space n)⟫ -
      (r : ℝ)*((r : ℝ)-1)*(posPower (r-2) ⟪(u : Space n),(x : Space n)⟫ * ⟪(u : Space n),(x : Space n)⟫^2) -
      ((n : ℝ)-1)*(r : ℝ)*(posPower (r-1) ⟪(u : Space n),(x : Space n)⟫ * ⟪(u : Space n),(x : Space n)⟫) := by ring
    _ = _ := by rw [h₁, h₂]; ring

lemma mean_casimir_comm {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    mean (fun u : Sphere n => f u*casimir g u) =
      mean (fun u : Sphere n => g u*casimir f u) := by
  rw [mean_casimir (hf.of_le (by norm_num)) hg,
    mean_casimir (hg.of_le (by norm_num)) hf, energy_symm]

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma sum_inner_generator_mul {n : ℕ} (u w x : Space n) :
    ∑ i : Fin n, ∑ j : Fin n, ⟪u,generator n i j x⟫*⟪w,generator n i j x⟫ =
      2*(‖x‖^2*⟪u,w⟫-⟪u,x⟫*⟪w,x⟫) := by
  simp_rw [inner_generator]
  have he (i j : Fin n) : (x i*u j-x j*u i)*(x i*w j-x j*w i) =
      x i^2*(u j*w j)+x j^2*(u i*w i)-(x i*w i)*(x j*u j)-(x i*u i)*(x j*w j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  have hi (a b : Space n) : ⟪a,b⟫ = ∑ i, a i*b i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [hi u w, hi u x, hi w x, EuclideanSpace.real_norm_sq_eq]
  simp_rw [mul_comm (u _) (x _), mul_comm (w _) (x _)]
  simp only [← Finset.mul_sum]
  ring

/-- Genuine tangential gradient on the unit sphere, expressed ambiently. -/
def sphereGradient {n : ℕ} (f : Space n → ℝ) (x : Space n) : Space n :=
  ∇ f x - (fderiv ℝ f x x) • x

lemma continuous_gradient_of_contDiff {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.comp (hf.continuous_fderiv (by norm_num))

lemma sphereGradient_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (sphereGradient f) := by
  exact (continuous_gradient_of_contDiff hf).sub
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_id).smul continuous_id)

lemma sphereGradient_inner {n : ℕ} (f : Space n → ℝ) (x w : Space n) :
    ⟪sphereGradient f x,w⟫ = fderiv ℝ f x w - fderiv ℝ f x x*⟪x,w⟫ := by
  simp only [sphereGradient, inner_sub_left, inner_smul_left, inner_gradient_left, starRingEnd_apply, star_trivial]

lemma sphereGradient_tangent {n : ℕ} (f : Space n → ℝ) (x : Sphere n) :
    ⟪sphereGradient f x,(x : Space n)⟫ = 0 := by
  rw [sphereGradient_inner, real_inner_self_eq_norm_sq, norm_coe]
  simp

lemma sum_rotDeriv_inner {n : ℕ} (f : Space n → ℝ) (x : Sphere n) (w : Space n) :
    (1/2 : ℝ)*(∑ i : Fin n, ∑ j : Fin n,
      rotDeriv (generator n i j) f x*⟪w,generator n i j x⟫) = ⟪sphereGradient f x,w⟫ := by
  simp only [rotDeriv, ← inner_gradient_left]
  rw [sum_inner_generator_mul, norm_coe, sphereGradient_inner,
    inner_gradient_left, inner_gradient_left, real_inner_comm w (x : Space n)]
  ring

lemma mean_gradient_casimir {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    mean (fun x : Sphere n => ⟪sphereGradient f x,sphereGradient g x⟫) =
      -mean (fun x : Sphere n => f x*casimir g x) := by
  rw [mean_casimir hf hg, neg_neg]
  have hs (x : Sphere n) : ⟪sphereGradient f x,sphereGradient g x⟫ =
      (1/2 : ℝ)*∑ i : Fin n, ∑ j : Fin n,
        rotDeriv (generator n i j) f x*rotDeriv (generator n i j) g x := by
    have h := sum_rotDeriv_inner f x (∇ g x)
    simp only [inner_gradient_left] at h
    change ⟪sphereGradient f x, ∇ g x - (fderiv ℝ g x x) • (x : Space n)⟫ = _
    rw [inner_sub_right, inner_smul_right, sphereGradient_tangent, mul_zero, sub_zero]
    exact h.symm
  simp_rw [hs]
  rw [mean, integral_const_mul]
  congr 1
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => continuous_integrable
      (((continuous_rotDeriv _ hf).comp continuous_subtype_val).mul
        ((continuous_rotDeriv _ (hg.of_le (by norm_num))).comp continuous_subtype_val)))
  · intro i _
    apply continuous_integrable
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_rotDeriv _ hf).comp continuous_subtype_val).mul
        ((continuous_rotDeriv _ (hg.of_le (by norm_num))).comp continuous_subtype_val)

end PettyProjection.Spherical
end

end OAI
