import OAI.Geometry.ProjectionBodies.SignCalculus

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma posPower_eq_max_pow {r : ℕ} (hr : 0 < r) (x : ℝ) :
    posPower r x = max x 0 ^ r := by
  by_cases hx : 0 < x
  · simp [posPower, hx, max_eq_left hx.le]
  · simp [posPower, hx, max_eq_right (not_lt.mp hx), hr.ne']

/-- Positive-hemisphere power kernel, including the constant zeroth power. -/
def higherKernel {n : ℕ} (r : ℕ) (u : Sphere n) (f : Sphere n → ℝ) : ℝ :=
  mean (fun x => (max ⟪(u : Space n),(x : Space n)⟫ 0)^r*f x)

lemma higherKernel_const_pos {n : ℕ} [NeZero n] (r : ℕ) (u : Sphere n) :
    0 < higherKernel r u (fun _ => 1) := by
  have hc : Continuous (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r) := by
    fun_prop
  simp only [higherKernel, mul_one, mean]
  exact integral_pos_of_integrable_nonneg_nonzero hc (continuous_integrable hc)
    (fun x => pow_nonneg (le_max_right _ _) _) (x := u)
    (by rw [real_inner_self_eq_norm_sq, norm_coe]; norm_num)

lemma higherKernel_recurrence {n r d : ℕ} [NeZero n] (hr : 3 ≤ r)
    (u : Sphere n) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (heig : ∀ x : Sphere n, casimir f x = -eigenvalue n d*f x) :
    (eigenvalue n r-eigenvalue n d)*higherKernel r u (fun x => f x) =
      (r : ℝ)*((r : ℝ)-1)*higherKernel (r-2) u (fun x => f x) := by
  let g : Space n → ℝ := fun y => posPower r ⟪(u : Space n),y⟫
  have hg : ContDiff ℝ 2 g := (posPower_contDiff_two hr).comp (innerSL ℝ (u : Space n)).contDiff
  have h := mean_casimir_comm hf hg
  have he (x : Sphere n) : f x*casimir g x =
      (r : ℝ)*((r : ℝ)-1)*((max ⟪(u : Space n),(x : Space n)⟫ 0)^(r-2)*f x) -
      eigenvalue n r*((max ⟪(u : Space n),(x : Space n)⟫ 0)^r*f x) := by
    rw [show casimir g x = _ from casimir_posPower_inner hr u x,
      posPower_eq_max_pow (show 0 < r-2 by omega), posPower_eq_max_pow (show 0 < r by omega)]
    ring
  simp_rw [he, heig, g, posPower_eq_max_pow (show 0 < r by omega)] at h
  have hct (r : ℕ) : Continuous (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r * f x) := by
    exact ((continuous_const.inner continuous_subtype_val).max continuous_const |>.pow r).mul
      (hf.continuous.comp continuous_subtype_val)
  have hh : (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r *
      (-eigenvalue n d*f x)) = fun x : Sphere n => -eigenvalue n d*
      (max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r*f x) := by funext x; ring
  rw [hh, mean, integral_sub
    ((continuous_integrable (hct (r-2))).const_mul _) ((continuous_integrable (hct r)).const_mul _),
    integral_const_mul, integral_const_mul, mean, integral_const_mul] at h
  change (r : ℝ)*((r : ℝ)-1)*higherKernel (r-2) u (fun x => f x) -
    eigenvalue n r*higherKernel r u (fun x => f x) =
    -eigenvalue n d*higherKernel r u (fun x => f x) at h
  linarith

lemma higherKernel_const_recurrence {n r : ℕ} [NeZero n] (hr : 3 ≤ r) (u : Sphere n) :
    eigenvalue n r*higherKernel r u (fun _ => 1) =
      (r : ℝ)*((r : ℝ)-1)*higherKernel (r-2) u (fun _ => 1) := by
  have he (x : Sphere n) : casimir (fun _ : Space n => (1 : ℝ)) x = -eigenvalue n 0*1 := by
    have hc (T : Space n →L[ℝ] Space n) : rotDeriv T (fun _ : Space n => (1 : ℝ)) = fun _ => 0 :=
      funext (rotDeriv_const T 1)
    simp [casimir, hc, rotDeriv_const, eigenvalue]
  simpa [eigenvalue] using higherKernel_recurrence hr u contDiff_const he

lemma higherKernel_peak {n : ℕ} [NeZero n] (u : Sphere n) {f : Sphere n → ℝ}
    (hf : Continuous f) :
    Tendsto (fun r : ℕ => higherKernel r u f / higherKernel r u (fun _ => 1))
      atTop (𝓝 (f u)) := by
  have hc : Continuous (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0) := by fun_prop
  have hmax (x : Sphere n) (_ : x ∈ (univ : Set (Sphere n))) (hne : x ≠ u) :
      max ⟪(u : Space n),(x : Space n)⟫ 0 < max ⟪(u : Space n),(u : Space n)⟫ 0 := by
    rw [real_inner_self_eq_norm_sq, norm_coe]
    norm_num only [one_pow, max_eq_left zero_le_one]
    apply max_lt
    · exact (inner_lt_one_iff_real_of_norm_eq_one (norm_coe u) (norm_coe x)).mpr
        (by intro h; exact hne (Subtype.ext h.symm))
    · norm_num
  have h := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := sigma n) isCompact_univ hc.continuousOn hmax
    (fun x _ => le_max_right _ _) (by rw [real_inner_self_eq_norm_sq, norm_coe]; norm_num)
    (by simp) hf.continuousOn
  simpa [smul_eq_mul, div_eq_mul_inv, higherKernel, mean, mul_comm] using h

end PettyProjection.Spherical
end

noncomputable section
open Filter Topology
namespace PettyProjection.Spherical

/-- Normalized multiplier of the positive-power kernel on degree `2*j`. -/
def higherFactor (n j : ℕ) (s : ℝ) : ℝ :=
  ∏ a ∈ Finset.range j, (s-2*a)/(s+n+2*a)

lemma higherFactor_zero (n : ℕ) (s : ℝ) : higherFactor n 0 s = 1 := by
  simp [higherFactor]

lemma higherFactor_succ (n j : ℕ) (s : ℝ) :
    higherFactor n (j+1) s = higherFactor n j s*((s-2*j)/(s+n+2*j)) := by
  simp only [higherFactor, Finset.prod_range_succ]

lemma higherFactor_odd_ne_zero {n : ℕ} (hn : 2 ≤ n) (j m : ℕ) :
    higherFactor n j (2*m+1) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  apply div_ne_zero
  · apply sub_ne_zero.mpr
    have h : (2*m+1 : ℕ) ≠ 2*a := by omega
    exact_mod_cast h
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith

lemma higherFactor_step {n : ℕ} (hn : 2 ≤ n) (j : ℕ) {s : ℝ} (hs : 3 ≤ s) :
    (s-2*j)*(s+2*j+n-2)*higherFactor n j s =
      s*(s+n-2)*higherFactor n j (s-2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  induction j with
  | zero => simp [higherFactor]
  | succ j ih =>
    rw [higherFactor_succ, higherFactor_succ]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have h₁ : s+n+2*j ≠ 0 := by linarith
    have h₂ : s-2+n+2*j ≠ 0 := by linarith
    push_cast
    field_simp
    linear_combination (s-2*j-2)*(s+n+2*j)*ih

lemma higherFactor_tendsto (n j : ℕ) :
    Tendsto (fun m : ℕ => higherFactor n j (2*m+1)) atTop (𝓝 1) := by
  induction j with
  | zero => simpa only [higherFactor_zero] using tendsto_const_nhds
  | succ j ih =>
    have h : Tendsto (fun m : ℕ => ((2*(m : ℝ)+1)-2*j)/((2*(m : ℝ)+1)+n+2*j)) atTop (𝓝 1) := by
      have h := tendsto_add_mul_div_add_mul_atTop_nhds (1-2*(j : ℝ))
        (1+n+2*(j : ℝ)) (2 : ℝ) (show (2 : ℝ) ≠ 0 by norm_num)
      convert! h using 1
      · funext m; congr 1 <;> ring
      · norm_num
    simpa only [higherFactor_succ, mul_one] using ih.mul h

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma eigenvalue_sub_even {n j : ℕ} (s : ℕ) :
    eigenvalue n s-eigenvalue n (2*j) =
      ((s : ℝ)-2*j)*((s : ℝ)+2*j+n-2) := by
  simp only [eigenvalue, Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma eigenvalue_odd_sub_even_ne_zero {n : ℕ} (hn : 2 ≤ n) (m j : ℕ) :
    eigenvalue n (2*m+1)-eigenvalue n (2*j) ≠ 0 := by
  rw [eigenvalue_sub_even]
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    have h : (2*m+1 : ℕ) ≠ 2*j := by omega
    exact_mod_cast h
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    push_cast
    linarith

lemma higherKernel_normalized_recurrence {n r d : ℕ} [NeZero n] (hr : 3 ≤ r)
    (u : Sphere n) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (heig : ∀ x : Sphere n, casimir f x = -eigenvalue n d*f x) :
    (eigenvalue n r-eigenvalue n d)*(higherKernel r u (fun x => f x)/higherKernel r u (fun _ => 1)) =
      eigenvalue n r*(higherKernel (r-2) u (fun x => f x)/higherKernel (r-2) u (fun _ => 1)) := by
  have h := higherKernel_recurrence hr u hf heig
  have hz := higherKernel_const_recurrence hr u
  have h₁ := (higherKernel_const_pos r u).ne'
  have h₂ := (higherKernel_const_pos (r-2) u).ne'
  field_simp
  linear_combination higherKernel (r-2) u (fun _ => 1)*h -
    higherKernel (r-2) u (fun x => f x)*hz

lemma higherKernel_eigenfunction {n j : ℕ} (hn : 2 ≤ n) [NeZero n]
    (u : Sphere n) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (heig : ∀ x : Sphere n, casimir f x = -eigenvalue n (2*j)*f x) :
    higherKernel 1 u (fun x => f x)/higherKernel 1 u (fun _ => 1) =
      higherFactor n j 1*f u := by
  let A (m : ℕ) := higherKernel (2*m+1) u (fun x => f x)/higherKernel (2*m+1) u (fun _ => 1)
  let F (m : ℕ) := higherFactor n j (2*m+1)
  have hinv (m : ℕ) : A m*F 0 = A 0*F m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      have hc := eigenvalue_odd_sub_even_ne_zero hn (m+1) j
      have hA := higherKernel_normalized_recurrence (show 3 ≤ 2*(m+1)+1 by omega) u hf heig
      rw [show 2*(m+1)+1-2 = 2*m+1 by omega] at hA
      change (eigenvalue n (2*(m+1)+1)-eigenvalue n (2*j))*A (m+1) =
        eigenvalue n (2*(m+1)+1)*A m at hA
      have hF : (eigenvalue n (2*(m+1)+1)-eigenvalue n (2*j))*F (m+1) =
          eigenvalue n (2*(m+1)+1)*F m := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        have h := higherFactor_step hn j (s := 2*(m+1)+1) (by linarith)
        have he : (2*((m : ℝ)+1)+1)-2 = 2*m+1 := by ring
        rw [he] at h
        rw [eigenvalue_sub_even]
        simpa only [F, eigenvalue, Nat.cast_add,
          Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using h
      apply mul_left_cancel₀ hc
      calc
        _ = ((eigenvalue n (2*(m+1)+1)-eigenvalue n (2*j))*A (m+1))*F 0 := by ring
        _ = eigenvalue n (2*(m+1)+1)*(A m*F 0) := by rw [hA]; ring
        _ = eigenvalue n (2*(m+1)+1)*(A 0*F m) := by rw [ih]
        _ = A 0*((eigenvalue n (2*(m+1)+1)-eigenvalue n (2*j))*F (m+1)) := by rw [hF]; ring
        _ = _ := by ring
  have ht : Tendsto (fun m : ℕ => 2*m+1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hA : Tendsto A atTop (𝓝 (f u)) :=
    (higherKernel_peak u (hf.continuous.comp continuous_subtype_val)).comp ht
  have hF : Tendsto F atTop (𝓝 1) := higherFactor_tendsto n j
  have hlim₁ := hA.mul (tendsto_const_nhds (x := F 0))
  have hlim₂ := (tendsto_const_nhds (x := A 0)).mul hF
  have heq : (fun m => A m*F 0) = (fun m => A 0*F m) := funext hinv
  rw [heq] at hlim₁
  have h := tendsto_nhds_unique hlim₁ hlim₂
  simpa [A, F, mul_comm] using h.symm

lemma higherKernel_harmonic {n j : ℕ} (hn : 2 ≤ n) [NeZero n]
    (u : Sphere n) {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous (2*j))
    (hΔ : laplacePolynomial p = 0) :
    higherKernel 1 u (fun x => polynomialFunction p x)/higherKernel 1 u (fun _ => 1) =
      higherFactor n j 1*polynomialFunction p u := by
  exact higherKernel_eigenfunction hn u ((polynomialFunction_contDiff p).of_le (by norm_num))
    (fun x => casimir_harmonic hp hΔ x)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

def pole (n : ℕ) [NeZero n] : Sphere n :=
  ⟨EuclideanSpace.single (0 : Fin n) 1, by simp⟩

lemma higherKernel_const_rotation {n : ℕ} (r : ℕ) (u : Sphere n)
    (U : Space n ≃ₗᵢ[ℝ] Space n) :
    higherKernel r (sphereMap U u) (fun _ => 1) = higherKernel r u (fun _ => 1) := by
  have h := mean_rotation U (fun x : Sphere n => max ⟪U (u : Space n),(x : Space n)⟫ 0 ^ r)
  change mean (fun x : Sphere n => max ⟪U (u : Space n),U (x : Space n)⟫ 0 ^ r) = _ at h
  simp only [U.inner_map_map] at h
  simp only [higherKernel, mul_one]
  change mean (fun x : Sphere n => max ⟪U (u : Space n),(x : Space n)⟫ 0 ^ r) = _
  exact h.symm

lemma higherKernel_const_independent {n : ℕ} (r : ℕ) (u v : Sphere n) :
    higherKernel r u (fun _ => 1) = higherKernel r v (fun _ => 1) := by
  let U := (ℝ ∙ ((u : Space n)-(v : Space n)))ᗮ.reflection
  have h : sphereMap U u = v := by
    apply Subtype.ext
    exact Submodule.reflection_sub ((norm_coe u).trans (norm_coe v).symm)
  rw [← h, higherKernel_const_rotation]

/-- The true normalized cosine kernel's constant, not an assumed multiplier. -/
def cosineConstant (n : ℕ) [NeZero n] : ℝ :=
  2*higherKernel 1 (pole n) (fun _ => 1)

lemma cosineConstant_pos (n : ℕ) [NeZero n] : 0 < cosineConstant n :=
  mul_pos (by norm_num) (higherKernel_const_pos 1 (pole n))

lemma mean_pos_inner_even {n : ℕ} [NeZero n] (u : Sphere n) {f : Space n → ℝ}
    (heven : Function.Even f) (hf : Continuous f) :
    mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫| *f x) =
      2*higherKernel 1 u (fun x => f x) := by
  have h := mean_rotation (LinearIsometryEquiv.neg ℝ : Space n ≃ₗᵢ[ℝ] Space n)
    (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0*f x)
  have he : (fun x : Sphere n => max ⟪(u : Space n),((sphereMap (LinearIsometryEquiv.neg ℝ)) x : Space n)⟫ 0 *
      f (sphereMap (LinearIsometryEquiv.neg ℝ) x)) =
      (fun x : Sphere n => max (-⟪(u : Space n),(x : Space n)⟫) 0*f x) := by
    funext x
    change max ⟪(u : Space n),-(x : Space n)⟫ 0*f (-(x : Space n)) = _
    rw [inner_neg_right, heven]
  rw [he] at h
  have hk (t : ℝ) : |t| = max t 0+max (-t) 0 := by
    rcases le_total 0 t with ht | ht <;> simp [abs_of_nonneg, abs_of_nonpos, ht]
  simp only [higherKernel, pow_one]
  simp_rw [hk, add_mul]
  rw [mean, integral_add]
  · change mean (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0*f x) +
      mean (fun x : Sphere n => max (-⟪(u : Space n),(x : Space n)⟫) 0*f x) = _
    rw [h]
    ring
  · exact continuous_integrable (by fun_prop)
  · exact continuous_integrable (by fun_prop)

lemma mean_abs_inner {n : ℕ} [NeZero n] (u : Sphere n) :
    mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫|) = cosineConstant n := by
  have h := mean_pos_inner_even u (f := fun _ => 1) (fun _ => rfl) continuous_const
  simpa only [mul_one, higherKernel_const_independent 1 u (pole n), cosineConstant] using h

/-- The actual cosine integral, with its constant fixed geometrically. -/
def cosine {n : ℕ} [NeZero n] (f : Sphere n → ℝ) (u : Sphere n) : ℝ :=
  mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫| *f x)/cosineConstant n

lemma cosine_continuous {n : ℕ} [NeZero n] {f : Sphere n → ℝ} (hf : Continuous f) :
    Continuous (cosine f) := by
  apply Continuous.div_const
  have h := continuous_parametric_integral_of_continuous (μ := sigma n)
    (f := fun u x : Sphere n => |⟪(u : Space n),(x : Space n)⟫| *f x)
    (by fun_prop) isCompact_univ
  simpa only [Measure.restrict_univ, mean] using h

lemma cosine_const {n : ℕ} [NeZero n] (c : ℝ) : cosine (fun _ : Sphere n => c) = fun _ => c := by
  funext u
  rw [cosine, mean, integral_mul_const]
  change mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫|)*c/cosineConstant n = c
  rw [mean_abs_inner]
  field_simp [(cosineConstant_pos n).ne']

lemma polynomialFunction_even {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hd : Even d) : Function.Even (polynomialFunction p) := by
  intro x
  simpa only [neg_one_smul, hd.neg_one_pow, one_mul] using
    polynomialFunction_smul_argument hp (-1) x

lemma cosine_harmonic {n j : ℕ} (hn : 2 ≤ n) [NeZero n]
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous (2*j))
    (hΔ : laplacePolynomial p = 0) (u : Sphere n) :
    cosine (fun x => polynomialFunction p x) u = higherFactor n j 1*polynomialFunction p u := by
  rw [cosine, mean_pos_inner_even u (polynomialFunction_even hp (even_two_mul j))
    (polynomialFunction_contDiff p).continuous, cosineConstant,
    ← higherKernel_const_independent 1 u (pole n), mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact higherKernel_harmonic hn u hp hΔ

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

def cosineMap {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) : C(Sphere n, ℝ) :=
  ⟨cosine f, cosine_continuous f.continuous⟩

lemma cosine_selfadj {n : ℕ} [NeZero n] {f g : Sphere n → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    mean (fun u => f u*cosine g u) = mean (fun u => cosine f u*g u) := by
  have hi : Integrable (fun z : Sphere n × Sphere n =>
      f z.1 * (|⟪(z.1 : Space n),(z.2 : Space n)⟫| * g z.2)) ((sigma n).prod (sigma n)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_integral_swap (f := fun u v : Sphere n => f u*(|⟪(u : Space n),(v : Space n)⟫| * g v)) hi
  simp only [cosine, mean, ← mul_div_assoc, div_mul_eq_mul_div, integral_div, ← integral_const_mul]
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with v
  rw [real_inner_comm (u : Space n) (v : Space n)]
  ring

lemma mean_cosine {n : ℕ} [NeZero n] {f : Sphere n → ℝ} (hf : Continuous f) :
    mean (cosine f) = mean f := by
  have h := cosine_selfadj (f := fun _ => 1) continuous_const hf
  simpa only [one_mul, cosine_const] using h

lemma cosine_neg {n : ℕ} [NeZero n] (f : Sphere n → ℝ) (u : Sphere n) :
    cosine f (sphereMap (LinearIsometryEquiv.neg ℝ) u) = cosine f u := by
  unfold cosine
  congr 1
  congr 1
  funext x
  change |⟪-(u : Space n),(x : Space n)⟫| * f x = _
  rw [inner_neg_left, abs_neg]

lemma mean_sphere_even_mul_odd {n d : ℕ} {f : Sphere n → ℝ}
    (heven : ∀ u, f (sphereMap (LinearIsometryEquiv.neg ℝ) u) = f u)
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d) (hd : Odd d) :
    mean (fun u : Sphere n => f u*polynomialFunction p u) = 0 := by
  have h := mean_rotation (LinearIsometryEquiv.neg ℝ : Space n ≃ₗᵢ[ℝ] Space n)
    (fun u : Sphere n => f u*polynomialFunction p u)
  have he : (fun u : Sphere n => f (sphereMap (LinearIsometryEquiv.neg ℝ) u)*
      polynomialFunction p (sphereMap (LinearIsometryEquiv.neg ℝ) u)) =
      (fun u : Sphere n => -(f u*polynomialFunction p u)) := by
    funext u
    rw [heven]
    change f u*polynomialFunction p (-(u : Space n)) = _
    rw [polynomialFunction_odd hp hd, mul_neg]
  rw [he, mean, integral_neg] at h
  change -mean (fun u : Sphere n => f u*polynomialFunction p u) = _ at h
  linarith

lemma cosine_harmonic_odd {n d : ℕ} [NeZero n] {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hd : Odd d) (u : Sphere n) :
    cosine (fun x => polynomialFunction p x) u = 0 := by
  rw [cosine, mean_even_mul_odd (f := fun x => |⟪(u : Space n),x⟫|) _ hp hd, zero_div]
  intro x
  simp only [inner_neg_right, abs_neg]

lemma cosine_projection_even {n j : ℕ} (hn : 2 ≤ n) [NeZero n] (f : C(Sphere n, ℝ)) :
    (harmonicSpace n (2*j)).starProjection (toH n (cosineMap f)) =
      higherFactor n j 1 • (harmonicSpace n (2*j)).starProjection (toH n f) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((harmonicSpace n (2*j)).smul_mem _ ((harmonicSpace n (2*j)).starProjection_apply_mem _))
  rintro v ⟨p, hp, rfl⟩
  rw [inner_sub_left, real_inner_smul_left, Submodule.inner_starProjection_left_eq_right]
  rw [Submodule.starProjection_eq_self_iff.mpr (show polynomialL2 n p ∈ harmonicSpace n (2*j) from ⟨p,hp,rfl⟩)]
  change ⟪toH n (cosineMap f),toH n (polynomialRestriction n p)⟫ -
    higherFactor n j 1 * ⟪toH n f,toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH, inner_toH]
  change mean (fun u : Sphere n => cosine f u*(polynomialRestriction n p) u) - _ = 0
  rw [← cosine_selfadj f.continuous (polynomialRestriction n p).continuous]
  have he : (fun u : Sphere n => f u*cosine (polynomialRestriction n p) u) =
      (fun u : Sphere n => higherFactor n j 1*(f u*polynomialFunction p u)) := by
    funext u
    rw [show cosine (polynomialRestriction n p) u = _ from cosine_harmonic hn hp.1 hp.2 u]
    ring
  rw [he, mean, integral_const_mul]
  change _ - higherFactor n j 1 * (∫ u : Sphere n, f u * polynomialFunction p u ∂sigma n) = 0
  exact sub_self _

lemma cosine_projection_odd {n d : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) (hd : Odd d) :
    (harmonicSpace n d).starProjection (toH n (cosineMap f)) = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  rintro v ⟨p, hp, rfl⟩
  rw [sub_zero]
  change ⟪toH n (cosineMap f),toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH]
  exact mean_sphere_even_mul_odd (cosine_neg f) hp.1 hd

end PettyProjection.Spherical
end

end OAI
