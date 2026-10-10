import OAI.Geometry.ProjectionBodies.Support

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology MvPolynomial
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

def restrictContinuous {n : ℕ} (f : Space n → ℝ) (hf : Continuous f) : C(Sphere n, ℝ) :=
  ⟨fun u => f u, hf.comp continuous_subtype_val⟩

lemma polynomialFunction_odd {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hd : Odd d) : Function.Odd (polynomialFunction p) := by
  intro x
  simpa only [neg_one_smul, hd.neg_one_pow, neg_one_mul] using
    polynomialFunction_smul_argument hp (-1) x

lemma mean_even_mul_odd {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    {f : Space n → ℝ} (heven : Function.Even f) (hp : p.IsHomogeneous d) (hd : Odd d) :
    mean (fun u : Sphere n => f u * polynomialFunction p u) = 0 := by
  have h := mean_rotation (LinearIsometryEquiv.neg ℝ : Space n ≃ₗᵢ[ℝ] Space n)
    (fun u : Sphere n => f u * polynomialFunction p u)
  have hh : (fun u : Sphere n =>
      f (sphereMap (LinearIsometryEquiv.neg ℝ) u) *
        polynomialFunction p (sphereMap (LinearIsometryEquiv.neg ℝ) u)) =
      (fun u : Sphere n => -(f u * polynomialFunction p u)) := by
    funext u
    change f (-↑u) * polynomialFunction p (-↑u) = _
    rw [heven, polynomialFunction_odd hp hd, mul_neg]
  rw [hh, mean, integral_neg] at h
  unfold mean at h ⊢
  linarith

lemma projection_odd_zero {n d : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : Continuous f) (heven : Function.Even f) (hd : Odd d) :
    (harmonicSpace n d).starProjection (toH n (restrictContinuous f hf)) = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  rintro v ⟨p, hp, rfl⟩
  rw [sub_zero]
  change ⟪toH n (restrictContinuous f hf), toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH]
  exact mean_even_mul_odd heven hp.1 hd

/-- A chosen true polynomial representative of a harmonic L² vector. -/
def harmonicRepresentative {n d : ℕ} [NeZero n] (v : harmonicSpace n d) : MvPolynomial (Fin n) ℝ :=
  Classical.choose v.property

lemma harmonicRepresentative_homogeneous {n d : ℕ} [NeZero n] (v : harmonicSpace n d) :
    (harmonicRepresentative v).IsHomogeneous d :=
  (Classical.choose_spec v.property).1.1

lemma harmonicRepresentative_laplace {n d : ℕ} [NeZero n] (v : harmonicSpace n d) :
    laplacePolynomial (harmonicRepresentative v) = 0 :=
  (Classical.choose_spec v.property).1.2

lemma harmonicRepresentative_toH {n d : ℕ} [NeZero n] (v : harmonicSpace n d) :
    polynomialL2 n (harmonicRepresentative v) = (v : H n) :=
  (Classical.choose_spec v.property).2

lemma inner_projection_self {n d : ℕ} [NeZero n] (v : H n) :
    ⟪v, (harmonicSpace n d).starProjection v⟫ = ‖(harmonicSpace n d).starProjection v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Submodule.inner_starProjection_left_eq_right]
  rw [Submodule.starProjection_eq_self_iff.mpr
    ((harmonicSpace n d).starProjection_apply_mem v)]

lemma energy_harmonicRepresentative_right {n d : ℕ} [NeZero n]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (v : harmonicSpace n d) :
    energy f (polynomialFunction (harmonicRepresentative v)) =
      eigenvalue n d * ⟪toH n (restrictContinuous f hf.continuous), (v : H n)⟫ := by
  rw [energy_harmonic_right hf (harmonicRepresentative_homogeneous v)
    (harmonicRepresentative_laplace v)]
  rw [← harmonicRepresentative_toH v]
  change _ = eigenvalue n d * ⟪toH n (restrictContinuous f hf.continuous),
    toH n (polynomialRestriction n (harmonicRepresentative v))⟫
  rw [inner_toH]
  rfl

lemma sum_inner_projection {n : ℕ} (hn : 2 ≤ n) [NeZero n] (s : Finset ℕ)
    (v : H n) {e : ℕ} (he : e ∈ s) :
    ⟪∑ d ∈ s, (harmonicSpace n d).starProjection v,
        (harmonicSpace n e).starProjection v⟫ =
      ‖(harmonicSpace n e).starProjection v‖ ^ 2 := by
  rw [sum_inner]
  rw [Finset.sum_eq_single e]
  · exact real_inner_self_eq_norm_sq _
  · intro d _ hde
    have h := harmonicSpace_orthogonal hn hde
      ((harmonicSpace n d).orthogonalProjectionOnto v)
      ((harmonicSpace n e).orthogonalProjectionOnto v)
    simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype,
      Submodule.coe_orthogonalProjectionOnto_apply] using h
  · exact fun h => False.elim (h he)

/-- The finite Bessel bound, established by subtracting a finite harmonic
polynomial sum. No infinite series is differentiated. -/
lemma energy_bessel_finset {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (s : Finset ℕ) :
    ∑ d ∈ s, eigenvalue n d * ‖(harmonicSpace n d).starProjection
      (toH n (restrictContinuous f hf.continuous))‖ ^ 2 ≤ energy f f := by
  let v := toH n (restrictContinuous f hf.continuous)
  let vs (d : ℕ) := (harmonicSpace n d).orthogonalProjectionOnto v
  let ps (d : ℕ) := harmonicRepresentative (vs d)
  let g : Space n → ℝ := fun x => ∑ d ∈ s, polynomialFunction (ps d) x
  have hpd (d : ℕ) : ContDiff ℝ 1 (polynomialFunction (ps d)) :=
    (polynomialFunction_contDiff _).of_le le_top
  have hg : ContDiff ℝ 1 g := ContDiff.sum fun d _ => hpd d
  have hG : toH n (restrictContinuous g hg.continuous) =
      ∑ d ∈ s, (harmonicSpace n d).starProjection v := by
    have hr : restrictContinuous g hg.continuous = ∑ d ∈ s, polynomialRestriction n (ps d) := by
      ext u
      simp [restrictContinuous, g, polynomialRestriction_apply]
    rw [hr, map_sum]
    apply Finset.sum_congr rfl
    intro d _
    exact (harmonicRepresentative_toH (vs d)).trans
      ((harmonicSpace n d).coe_orthogonalProjectionOnto_apply v)
  have hfg : energy f g =
      ∑ d ∈ s, eigenvalue n d * ‖(harmonicSpace n d).starProjection v‖ ^ 2 := by
    rw [energy_finset_sum_right s hf hpd]
    apply Finset.sum_congr rfl
    intro d _
    rw [energy_harmonicRepresentative_right hf (vs d)]
    exact congrArg (eigenvalue n d * ·) (inner_projection_self v)
  have hgg : energy g g =
      ∑ d ∈ s, eigenvalue n d * ‖(harmonicSpace n d).starProjection v‖ ^ 2 := by
    rw [energy_finset_sum_right s hg hpd]
    apply Finset.sum_congr rfl
    intro d hd
    rw [energy_harmonicRepresentative_right hg (vs d), hG]
    exact congrArg (eigenvalue n d * ·) (sum_inner_projection hn s v hd)
  have hpos := energy_nonneg (fun x => f x - g x)
  rw [energy_sub_self hf hg, hfg, hgg] at hpos
  linarith

lemma eigenvalue_nonneg {n : ℕ} (hn : 2 ≤ n) (d : ℕ) : 0 ≤ eigenvalue n d := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold eigenvalue
  exact mul_nonneg hd (by linarith)

lemma eigenvalue_four_le {n d : ℕ} (hn : 2 ≤ n) (hd : 4 ≤ d) :
    eigenvalue n 4 ≤ eigenvalue n d := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hprod := mul_nonneg (sub_nonneg.mpr hd') (sub_nonneg.mpr hn')
  norm_num [eigenvalue]
  nlinarith

lemma Q_zero_of_mem_lowSpace {n : ℕ} [NeZero n] {v : H n} (hv : v ∈ lowSpace n) :
    Q n v = 0 := by
  rw [Q_eq_sub, Submodule.starProjection_eq_self_iff.mpr hv, sub_self]

lemma projection_zero_mem_lowSpace {n : ℕ} [NeZero n] (v : H n) :
    (harmonicSpace n 0).starProjection v ∈ lowSpace n := by
  obtain ⟨c, hc⟩ := harmonicSpace_zero_constant ((harmonicSpace n 0).starProjection_apply_mem v)
  rw [hc]
  exact constant_mem_lowSpace n c

lemma projection_inner_ne {n : ℕ} (hn : 2 ≤ n) [NeZero n] (v : H n)
    {d e : ℕ} (hde : d ≠ e) :
    ⟪(harmonicSpace n d).starProjection v, (harmonicSpace n e).starProjection v⟫ = 0 := by
  have h := harmonicSpace_orthogonal hn hde
    ((harmonicSpace n d).orthogonalProjectionOnto v)
    ((harmonicSpace n e).orthogonalProjectionOnto v)
  simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype,
    Submodule.coe_orthogonalProjectionOnto_apply] using h

lemma norm_Q_sq_le_remainder {n : ℕ} (hn : 2 ≤ n) [NeZero n] (v : H n) :
    ‖Q n v‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖(harmonicSpace n 0).starProjection v‖ ^ 2 -
      ‖(harmonicSpace n 2).starProjection v‖ ^ 2 := by
  let p0 := (harmonicSpace n 0).starProjection v
  let p2 := (harmonicSpace n 2).starProjection v
  have h0 : Q n p0 = 0 := Q_zero_of_mem_lowSpace (projection_zero_mem_lowSpace v)
  have h2 : Q n p2 = 0 := Q_zero_of_mem_lowSpace
    (harmonicSpace_two_le_lowSpace n ((harmonicSpace n 2).starProjection_apply_mem v))
  have hQ : Q n (v - p0 - p2) = Q n v := by simp only [map_sub, h0, h2, sub_zero]
  have h := norm_Q_le n (v - p0 - p2)
  rw [hQ] at h
  have hsq := sq_le_sq₀ (norm_nonneg (Q n v)) (norm_nonneg (v - p0 - p2)) |>.mpr h
  have hnorm : ‖v - p0 - p2‖ ^ 2 = ‖v‖ ^ 2 - ‖p0‖ ^ 2 - ‖p2‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_left,
      inner_projection_self v, inner_projection_self v,
      projection_inner_ne hn v (by decide : (0 : ℕ) ≠ 2)]
    ring
  exact hsq.trans_eq hnorm

lemma energy_spectral_lower {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (heven : Function.Even f) :
    let v := toH n (restrictContinuous f hf.continuous)
    eigenvalue n 4 * ‖v‖ ^ 2 - eigenvalue n 4 * ‖(harmonicSpace n 0).starProjection v‖ ^ 2 -
      (eigenvalue n 4 - eigenvalue n 2) * ‖(harmonicSpace n 2).starProjection v‖ ^ 2 ≤
        energy f f := by
  let v := toH n (restrictContinuous f hf.continuous)
  let a (d : ℕ) := ‖(harmonicSpace n d).starProjection v‖ ^ 2
  let b (d : ℕ) := eigenvalue n 4 * a d -
    (if d = 0 then eigenvalue n 4 * a 0 else 0) -
    (if d = 2 then (eigenvalue n 4 - eigenvalue n 2) * a 2 else 0)
  have ha : HasSum a (‖v‖ ^ 2) :=
    hilbertSum_hasSum_projection_norm_sq (harmonicSpace_isHilbertSum hn) v
  have hb : HasSum b (eigenvalue n 4 * ‖v‖ ^ 2 - eigenvalue n 4 * a 0 -
      (eigenvalue n 4 - eigenvalue n 2) * a 2) :=
    ((ha.mul_left (eigenvalue n 4)).sub (hasSum_ite_eq 0 _)).sub (hasSum_ite_eq 2 _)
  have hb_le (d : ℕ) : b d ≤ eigenvalue n d * a d := by
    by_cases h0 : d = 0
    · subst d; simp [b, eigenvalue]
    by_cases h2 : d = 2
    · subst d; simp only [b, ite_eq_right (by decide : (2 : ℕ) ≠ 0), ite_true, sub_zero]; ring_nf; exact le_rfl
    by_cases h1 : d = 1
    · subst d
      have hz : a 1 = 0 := by
        simp [a, v, projection_odd_zero hf.continuous heven (by decide : Odd 1)]
      simp [b, hz]
    by_cases h3 : d = 3
    · subst d
      have hz : a 3 = 0 := by
        simp [a, v, projection_odd_zero hf.continuous heven (by decide : Odd 3)]
      simp [b, hz]
    have hd : 4 ≤ d := by omega
    simpa only [b, ite_eq_right h0, ite_eq_right h2, sub_zero] using
      mul_le_mul_of_nonneg_right (eigenvalue_four_le hn hd) (sq_nonneg _)
  apply le_of_tendsto hb
  apply Eventually.of_forall
  intro s
  exact (Finset.sum_le_sum fun d _ => hb_le d).trans (energy_bessel_finset hn hf s)

/-- The mean-subtracted variance in the probability normalization. -/
def variance {n : ℕ} (f : Sphere n → ℝ) : ℝ := mean (fun u => f u ^ 2) - (mean f) ^ 2

/-- The genuine degree-two-removed even spherical spectral gap, under the
canonical probability measure. `energy` is the integrated squared tangential
derivative represented by the coordinate rotation generators. -/
lemma even_spectral_gap {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (heven : Function.Even f) :
    (2 * n : ℝ) * variance (fun u : Sphere n => f u) + (2 * n + 8 : ℝ) *
      ‖Q n (toH n (restrictContinuous f hf.continuous))‖ ^ 2 ≤ energy f f := by
  let F := restrictContinuous f hf.continuous
  let v := toH n F
  have h0 : ‖(harmonicSpace n 0).starProjection v‖ ^ 2 = (mean F) ^ 2 := by
    rw [harmonicSpace_zero_projection n F, norm_toH_sq]
    simpa only [ContinuousMap.const_apply] using mean_const n ((mean F) ^ 2)
  have hvar : variance (fun u : Sphere n => f u) = ‖v‖ ^ 2 - (mean F) ^ 2 := by
    rw [norm_toH_sq]
    rfl
  have h := energy_spectral_lower hn hf heven
  have hQ := norm_Q_sq_le_remainder hn v
  change eigenvalue n 4 * ‖v‖ ^ 2 - eigenvalue n 4 * ‖(harmonicSpace n 0).starProjection v‖ ^ 2 -
    (eigenvalue n 4 - eigenvalue n 2) * ‖(harmonicSpace n 2).starProjection v‖ ^ 2 ≤ energy f f at h
  rw [h0] at h hQ
  rw [hvar]
  have hmul := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 2 * n + 8)
  norm_num [eigenvalue] at h
  nlinarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma line_convex {n : ℕ} {f : Space n → ℝ} (hc : ConvexOn ℝ univ f)
    (x y : Space n) : ConvexOn ℝ univ (fun t : ℝ => f (x + t • y)) := by
  constructor
  · exact convex_univ
  · intro a _ b _ s t hs ht hst
    have h := hc.2 (mem_univ (x + a • y)) (mem_univ (x + b • y)) hs ht hst
    have he : x + (s * a + t * b) • y = s • (x + a • y) + t • (x + b • y) := by
      calc
        _ = (s + t) • x + (s * a + t * b) • y := by rw [hst, one_smul]
        _ = _ := by module
    simpa only [smul_eq_mul, ← he] using h

lemma line_hasDerivAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • y) y t := by
  have h : HasDerivAt (fun s : ℝ => s • y) y t := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const y
  exact h.const_add x

lemma line_second_hasDerivAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x y : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y) y)
      (fderiv ℝ (fderiv ℝ f) x y y) 0 := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hh : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    (hfd.differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • y) y 0 := line_hasDerivAt x y 0
  have hdx : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y))
      (fderiv ℝ (fderiv ℝ f) x y) 0 := by
    have hh' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x + (0 : ℝ) • y) := by
      simpa only [zero_smul, add_zero] using hh
    exact hh'.comp_hasDerivAt 0 hl
  have hd : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y) y)
      (fderiv ℝ (fderiv ℝ f) x y y + fderiv ℝ f (x + (0 : ℝ) • y) 0) 0 :=
    hdx.clm_apply (hasDerivAt_const 0 y)
  simpa only [map_zero, add_zero] using hd

lemma hessian_nonneg_of_convex {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (x y : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x y y := by
  have hdf (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • y))
      (fderiv ℝ f (x + t • y) y) t :=
    (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (line_hasDerivAt x y t)
  have hmono : Monotone (fun t : ℝ => fderiv ℝ f (x + t • y) y) := by
    have h := (line_convex hc x y).monotoneOn_deriv (fun t _ => (hdf t).differentiableAt)
    have heq : deriv (fun t : ℝ => f (x + t • y)) =
        (fun t => fderiv ℝ f (x + t • y) y) := funext fun t => (hdf t).deriv
    rw [heq] at h
    exact monotoneOn_univ.mp h
  rw [← (line_second_hasDerivAt hf x y).deriv]
  exact hmono.deriv_nonneg

lemma rotDeriv_rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Space n) :
    rotDeriv T (rotDeriv T f) x =
      fderiv ℝ (fderiv ℝ f) x (T x) (T x) + fderiv ℝ f x (T (T x)) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd := (hfd.differentiable (by norm_num) x).hasFDerivAt.clm_apply T.hasFDerivAt
  change fderiv ℝ (fun y => fderiv ℝ f y (T y)) x (T x) = _
  rw [hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_comm]

lemma generator_square_coord {n : ℕ} (i j a : Fin n) (x : Space n) :
    (generator n i j (generator n i j x)) a =
      2 * (if i = j then if i = a then x a else 0 else 0) -
        (if j = a then x a else 0) - (if i = a then x a else 0) := by
  by_cases hij : i = j <;> by_cases hia : i = a <;> by_cases hja : j = a <;>
    simp_all [generator_apply_coord, eq_comm]; ring

lemma sum_generator_square {n : ℕ} (x : Space n) :
    ∑ i : Fin n, ∑ j : Fin n, generator n i j (generator n i j x) =
      (-2 * ((n : ℝ) - 1)) • x := by
  ext a
  simp only [WithLp.ofLp_sum, Finset.sum_apply, generator_square_coord, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma convex_casimir_lower {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (x : Space n) :
    -((n : ℝ) - 1) * fderiv ℝ f x x ≤ casimir f x := by
  have h (i j : Fin n) : fderiv ℝ f x (generator n i j (generator n i j x)) ≤
      rotDeriv (generator n i j) (rotDeriv (generator n i j) f) x := by
    rw [rotDeriv_rotDeriv _ hf]
    linarith [hessian_nonneg_of_convex hf hc x (generator n i j x)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  have hh := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [← map_sum, sum_generator_square, map_smul, smul_eq_mul] at hh
  unfold casimir
  nlinarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Pointwise Convolution
namespace PettyProjection.Spherical

lemma seminorm_continuous (n : ℕ) (g : Seminorm ℝ (Space n)) : Continuous g :=
  continuousOn_univ.mp (g.convexOn.continuousOn isOpen_univ)

lemma seminorm_lipschitz (n : ℕ) (g : Seminorm ℝ (Space n)) :
    ∃ C : ℝ≥0, LipschitzWith C g := by
  obtain ⟨C, hC, hbound⟩ := g.bound_of_continuous_normedSpace (seminorm_continuous n g)
  refine ⟨⟨C, hC.le⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change |g x - g y| ≤ C * dist x y
  exact (abs_sub_map_le_sub g x y).trans (by simpa only [dist_eq_norm] using hbound (x - y))

def normSmooth {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    Space n → ℝ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (g : Space n → ℝ)

lemma normSmooth_contDiff {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    ContDiff ℝ 2 (normSmooth g φ) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (seminorm_continuous n g).locallyIntegrable

lemma normSmooth_even {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    Function.Even (normSmooth g φ) := by
  intro x
  exact convolution_neg_of_neg_eq (ContinuousLinearMap.lsmul ℝ ℝ) (Eventually.of_forall φ.normed_neg)
    (Eventually.of_forall (fun x => map_neg_eq_map g x))

lemma normSmooth_integrable {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    (x : Space n) : Integrable (fun y => φ.normed volume y * g (x - y)) volume :=
  φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed.locallyIntegrable (seminorm_continuous n g) x

lemma normSmooth_convex {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    ConvexOn ℝ univ (normSmooth g φ) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    have hi₁ := (normSmooth_integrable g φ x).const_mul a
    have hi₂ := (normSmooth_integrable g φ y).const_mul b
    change (∫ z, φ.normed volume z * g (a • x + b • y - z)) ≤
        a * (∫ z, φ.normed volume z * g (x - z)) + b * (∫ z, φ.normed volume z * g (y - z))
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hi₁ hi₂]
    apply integral_mono (normSmooth_integrable g φ (a • x + b • y)) (hi₁.add hi₂)
    intro z
    have he : a • x + b • y - z = a • (x - z) + b • (y - z) := by
      calc
        _ = a • x + b • y - (a + b) • z := by rw [hab, one_smul]
        _ = _ := by module
    have h := mul_le_mul_of_nonneg_left
      (g.convexOn.2 (mem_univ (x-z)) (mem_univ (y-z)) ha hb hab) (φ.nonneg_normed (μ := volume) z)
    simp only [Pi.add_apply]
    rw [he]
    simpa only [smul_eq_mul, mul_add, mul_left_comm] using h

lemma normSmooth_dist_le {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    {C : ℝ≥0} (hC : LipschitzWith C g) (x : Space n) :
    dist (normSmooth g φ x) (g x) ≤ C * φ.rOut := by
  apply φ.dist_normed_convolution_le (seminorm_continuous n g).aestronglyMeasurable
  intro y hy
  exact (hC.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le C.coe_nonneg)

lemma convex_radial_bounds {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (hc : ConvexOn ℝ univ f) (x : Space n) :
    f x - f 0 ≤ fderiv ℝ f x x ∧ fderiv ℝ f x x ≤ f ((2 : ℝ) • x) - f x := by
  have hd : HasDerivAt (fun t : ℝ => f (x + t • x)) (fderiv ℝ f x x) 0 := by
    have h : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • x) := by
      simpa only [zero_smul, add_zero] using (hf x).hasFDerivAt
    exact h.comp_hasDerivAt 0 (line_hasDerivAt x x 0)
  have hl := (line_convex hc x x).slope_le_of_hasDerivAt (mem_univ (-1 : ℝ)) (mem_univ 0)
    (by norm_num : (-1 : ℝ) < 0) hd
  have hr := (line_convex hc x x).le_slope_of_hasDerivAt (mem_univ 0) (mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hd
  simpa only [slope, vsub_eq_sub, neg_smul, one_smul, add_neg_cancel,
    zero_smul, add_zero, two_smul, zero_sub, neg_neg, sub_zero, inv_one, smul_eq_mul, one_mul] using And.intro hl hr

lemma normSmooth_radial_dist_le {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    {C : ℝ≥0} (hC : LipschitzWith C g) (x : Space n) :
    dist (fderiv ℝ (normSmooth g φ) x x) (g x) ≤ 2 * C * φ.rOut := by
  have h := convex_radial_bounds ((normSmooth_contDiff g φ).differentiable (by norm_num))
    (normSmooth_convex g φ) x
  have hx := normSmooth_dist_le g φ hC x
  have h0 := normSmooth_dist_le g φ hC 0
  have h2 := normSmooth_dist_le g φ hC ((2 : ℝ) • x)
  rw [Real.dist_eq, abs_le] at hx h0 h2 ⊢
  simp only [map_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h0 h2
  constructor <;> linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma sphere_ae_of_radial {n : ℕ} {P : Space n → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure (Space n)), P x)
    (hr : ∀ (u : Sphere n) (r : ℝ), 0 < r → P (r • (u : Space n)) → P u) :
    ∀ᵐ (u : Sphere n) ∂sigma n, P (u : Space n) := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n) - 1)
  have hν : ν ≠ 0 := by
    intro h
    have he := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ (Space n) - 1)
      (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))
    change ν _ = _ at he
    rw [h] at he
    have hp : 0 < (1 : ℝ) ^ (Module.finrank ℝ (Space n) - 1 + 1) /
        ((Module.finrank ℝ (Space n) - 1 : ℕ) + 1) := by positivity
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) he.symm
  let : NeZero ν := ⟨hν⟩
  have hs : ∀ᵐ (x : ({0}ᶜ : Set (Space n))) ∂(volume : Measure (Space n)).comap
      (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n), P (x : Space n) :=
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : Space n)).compl).mp
      (ae_restrict_of_ae hP)
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  have hi := hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hh := hi.quasiMeasurePreserving.ae hs
  have hh' : ∀ᵐ z ∂(surface n).prod ν, P (z.2.1 • (z.1 : Space n)) := by
    change ∀ᵐ z ∂(surface n).prod ν, P (((homeomorphUnitSphereProd (Space n)).symm z : ({0}ᶜ : Set (Space n))) : Space n) at hh
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hh
  apply Measure.ae_smul_measure (μ := surface n) _ ((surface n univ)⁻¹)
  filter_upwards [Measure.ae_ae_of_ae_prod hh'] with u hu
  obtain ⟨r, hr'⟩ := hu.exists
  exact hr u r r.property hr'

lemma seminorm_ae_differentiable_sphere {n : ℕ} (g : Seminorm ℝ (Space n)) :
    ∀ᵐ (u : Sphere n) ∂sigma n, DifferentiableAt ℝ (g : Space n → ℝ) (u : Space n) := by
  obtain ⟨C, hC⟩ := seminorm_lipschitz n g
  apply sphere_ae_of_radial hC.ae_differentiableAt
  intro u r hr hd
  have hc := (hd.comp (u : Space n) (differentiableAt_id.const_smul r)).const_smul r⁻¹
  have he : (r⁻¹ • ((g : Space n → ℝ) ∘ (r • id))) = (g : Space n → ℝ) := by
    ext x
    simp only [Pi.smul_apply, Function.comp_apply, id_eq, map_smul_eq_mul,
      Real.norm_eq_abs, abs_of_pos hr, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  change DifferentiableAt ℝ (r⁻¹ • ((g : Space n → ℝ) ∘ (r • id))) (u : Space n) at hc
  rw [he] at hc
  exact hc

lemma normSmooth_lipschitz {n : ℕ} (g : Seminorm ℝ (Space n))
    (φ : ContDiffBump (0 : Space n)) {C : ℝ≥0} (hC : LipschitzWith C g) :
    LipschitzWith C (normSmooth g φ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖(∫ z, φ.normed volume z * g (x - z)) -
    (∫ z, φ.normed volume z * g (y - z))‖ ≤ _
  rw [← integral_sub (normSmooth_integrable g φ x) (normSmooth_integrable g φ y)]
  calc
    _ ≤ ∫ z, ‖φ.normed volume z * g (x - z) - φ.normed volume z * g (y - z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, φ.normed volume z * (C * dist x y) := by
      apply integral_mono
        ((normSmooth_integrable g φ x).sub (normSmooth_integrable g φ y)).norm
        (φ.integrable_normed.mul_const _)
      intro z
      change ‖φ.normed volume z * g (x-z) - φ.normed volume z * g (y-z)‖ ≤ _
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa [dist_eq_norm] using hC.dist_le_mul (x-z) (y-z)
    _ = C * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

end PettyProjection.Spherical
end

end OAI
