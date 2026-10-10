import OAI.MathematicalPhysics.Elasticity.LocalRegularity
import OAI.MathematicalPhysics.Elasticity.Compact

namespace OAI

noncomputable section

namespace ElasticityRegularity
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A joint smooth compactly spatially supported coefficient yields a genuinely
operator-norm-smooth family of actual L2 multipliers. -/
theorem exists_smooth_lp_multiplier {S : Set E} (hS : IsCompact S)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) :
    ∃ M : P → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ContDiff ℝ (⊤ : ℕ∞) M ∧ ∀ p f,
        (M p f : 𝓢'(E,ℂ))=smulLeftCLM ℂ (fun x => a (p,x)) (f : 𝓢'(E,ℂ)) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨b,hb,hbe⟩ := ElasticityCompact.exists_smooth_linf_family hS.measurableSet
    (volume : Measure E) a ha hs
  let B := (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure E) ∞ 2 2
  refine ⟨fun p => B (b p),(B.restrictScalars ℝ).contDiff.comp hb,fun p f => ?_⟩
  have ha' : ContDiff ℝ (⊤ : ℕ∞) (fun x => a (p,x)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun x => a (p,x)) := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hS.isClosed
    intro x hx
    contrapose! hx
    simpa only [Function.mem_support,not_not] using hs p x hx
  have hm := compact_bounded_multiplier ha' hc
  have hprod : B (b p) f=(hm.toLp (fun x => a (p,x))) • f := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (b p) f,
      Lp.coeFn_lpSMul (r := 2) (hm.toLp _) f,hm.coeFn_toLp,hbe p] with x h₁ h₂ h₃ h₄
    change ((ContinuousLinearMap.mul ℂ ℂ).holder 2 (b p) f) x=_
    rw [h₁,h₂]
    simp only [Pi.smul_apply',h₃,h₄]
    rfl
  rw [hprod,Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth ha') hm]
end ElasticityRegularity
namespace ElasticityPlanar
open MeasureTheory Complex

def testSubmodule : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g at hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := by
    exact ⟨contDiff_const (c := (0 : ℂ)), HasCompactSupport.zero⟩
  smul_mem' := by
    intro a f hf
    change ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f at hf
    constructor
    · exact hf.1.const_smul a
    · change HasCompactSupport (fun z => a * f z)
      exact hf.2.mul_left

abbrev Test := testSubmodule

instance : CoeFun Test (fun _ => ℂ → ℂ) := ⟨fun f => f.val⟩

lemma smooth (f : Test) : ContDiff ℝ (⊤ : ℕ∞) (f : ℂ → ℂ) := f.property.1
lemma compact (f : Test) : HasCompactSupport (f : ℂ → ℂ) := f.property.2

def d (v : ℂ) : Test →ₗ[ℂ] Test where
  toFun f := ⟨fun z => fderiv ℝ (f : ℂ → ℂ) z v, by
    constructor
    · exact ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    · exact (compact f).fderiv_apply ℝ v⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
      (fderiv_add ((smooth f).differentiable (by simp) z)
        ((smooth g).differentiable (by simp) z))
  map_smul' a f := by
    apply Subtype.ext
    funext z
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
      (fderiv_const_smul ((smooth f).differentiable (by simp) z) a)

@[simp] lemma d_apply (v : ℂ) (f : Test) (z : ℂ) :
    (d v f : ℂ → ℂ) z = fderiv ℝ (f : ℂ → ℂ) z v := rfl

def mulSmooth (a : ℂ → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) : Test →ₗ[ℂ] Test where
  toFun f := ⟨fun z => a z * f z, ⟨ha.mul (smooth f), (compact f).mul_left⟩⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change a z * (c * f z) = c * (a z * f z)
    ring

def Z : Test →ₗ[ℂ] Test := mulSmooth id contDiff_id
def Zbar : Test →ₗ[ℂ] Test := mulSmooth star Complex.conjCLE.contDiff

@[simp] lemma Z_apply (f : Test) (z : ℂ) : (Z f : ℂ → ℂ) z = z * f z := rfl
@[simp] lemma Zbar_apply (f : Test) (z : ℂ) : (Zbar f : ℂ → ℂ) z = star z * f z := rfl

lemma d_Z (v : ℂ) (f : Test) : d v (Z f) = v • f + Z (d v f) := by
  apply Subtype.ext
  funext z
  change fderiv ℝ (fun z => z * f z) z v = v * f z + z * ((d v f : ℂ → ℂ) z)
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((hasFDerivAt_id z).mul ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  simpa [d_apply, add_comm, mul_comm, Pi.mul_def] using h

lemma deriv_conj (f : Test) (z v : ℂ) :
    fderiv ℝ (fun z => star (f z)) z v = star (fderiv ℝ (f : ℂ → ℂ) z v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h

lemma d_Zbar (v : ℂ) (f : Test) : d v (Zbar f) = (star v) • f + Zbar (d v f) := by
  apply Subtype.ext
  funext z
  change fderiv ℝ (fun z => star z * f z) z v = star v * f z + star z * ((d v f : ℂ → ℂ) z)
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((Complex.conjCLE.hasFDerivAt (x := z)).mul
      ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  simpa [d_apply, Complex.star_def, add_comm, mul_comm, Pi.mul_def] using h

lemma d_d (v w : ℂ) (f : Test) (z : ℂ) :
    (d v (d w f) : ℂ → ℂ) z = fderiv ℝ (fderiv ℝ (f : ℂ → ℂ)) z v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : ℂ → ℂ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : ℂ → ℂ) y w) z v = _
  rw [fderiv_clm_apply (hd z) (differentiableAt_const w)]
  simp

lemma d_comm (v w : ℂ) (f : Test) : d v (d w f) = d w (d v f) := by
  apply Subtype.ext
  funext z
  rw [d_d, d_d]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

def pair (f g : Test) : ℂ := ∫ z : ℂ, star (f z) * g z

lemma integrable_pair (f g : Test) : Integrable (fun z : ℂ => star (f z)*g z) := by
  exact ((Complex.conjCLE.continuous.comp (smooth f).continuous).mul (smooth g).continuous).integrable_of_hasCompactSupport (compact g).mul_left

lemma pair_add_right (f g h : Test) : pair f (g+h) = pair f g + pair f h := by
  simpa only [pair, Submodule.coe_add, Pi.add_apply, mul_add] using
    integral_add (integrable_pair f g) (integrable_pair f h)

lemma pair_add_left (f g h : Test) : pair (f+g) h = pair f h + pair g h := by
  simpa only [pair, Submodule.coe_add, Pi.add_apply, star_add, add_mul] using
    integral_add (integrable_pair f h) (integrable_pair g h)

lemma pair_sub_right (f g h : Test) : pair f (g-h) = pair f g - pair f h := by
  simpa only [pair, Submodule.coe_sub, Pi.sub_apply, mul_sub] using
    integral_sub (integrable_pair f g) (integrable_pair f h)

lemma pair_sub_left (f g h : Test) : pair (f-g) h = pair f h - pair g h := by
  simpa only [pair, Submodule.coe_sub, Pi.sub_apply, star_sub, sub_mul] using
    integral_sub (integrable_pair f h) (integrable_pair g h)

lemma pair_smul_right (f g : Test) (a : ℂ) : pair f (a • g) = a * pair f g := by
  simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (star (f _)) a, mul_assoc]
  exact integral_const_mul a _

lemma pair_smul_left (f g : Test) (a : ℂ) : pair (a • f) g = star a * pair f g := by
  simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul, mul_comm (star (f _)), mul_assoc]
  exact integral_const_mul (star a) _

/-- Coordinate derivatives are skew adjoint on the actual test space. -/
lemma pair_d (f g : Test) (v : ℂ) : pair f (d v g) = -pair (d v f) g := by
  have h1 : Integrable (fun z : ℂ => fderiv ℝ (fun z => star (f z)) z v * g z) := by
    simpa only [deriv_conj, d_apply] using integrable_pair (d v f) g
  have h2 : Integrable (fun z : ℂ => star (f z)*fderiv ℝ (g : ℂ → ℂ) z v) :=
    integrable_pair f (d v g)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 (integrable_pair f g)
    (fun z _ => Complex.conjCLE.differentiableAt.comp z ((smooth f).differentiable (by simp) z))
    (fun z _ => (smooth g).differentiable (by simp) z)
    |>.trans (by simp only [pair, deriv_conj, d_apply])

lemma pair_Z (f g : Test) : pair f (Z g) = pair (Zbar f) g := by
  apply integral_congr_ae
  filter_upwards [] with z
  simp [mul_comm, mul_left_comm, mul_assoc]

lemma pair_Zbar (f g : Test) : pair f (Zbar g) = pair (Z f) g := by
  apply integral_congr_ae
  filter_upwards [] with z
  simp [mul_comm, mul_left_comm]

/-- Twice dbar conjugated by exp(t|z|²/2). -/
def B (t : ℝ) : Test →ₗ[ℂ] Test := d 1 + Complex.I • d Complex.I - (t : ℂ) • Z
/-- Formal Hermitian adjoint. -/
def C (t : ℝ) : Test →ₗ[ℂ] Test := -d 1 + Complex.I • d Complex.I - (t : ℂ) • Zbar

lemma pair_B (f g : Test) (t : ℝ) : pair f (B t g) = pair (C t f) g := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pair_add_right, pair_sub_right, pair_smul_right,
    pair_add_left, pair_sub_left, pair_smul_left, pair_d, pair_Z,
    ← neg_one_smul ℂ (d 1 f), pair_smul_left, map_neg, map_one,
    Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma pair_C (f g : Test) (t : ℝ) : pair f (C t g) = pair (B t f) g := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pair_add_right, pair_sub_right, pair_smul_right,
    pair_add_left, pair_sub_left, pair_smul_left, pair_d, pair_Zbar,
    ← neg_one_smul ℂ (d 1 g), pair_smul_right, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma Z_Zbar (f : Test) : Z (Zbar f) = Zbar (Z f) := by
  apply Subtype.ext
  funext z
  change z * (star z * f z) = star z * (z * f z)
  ring

/-- Positive commutator of the two Gaussian-conjugated planar operators. -/
lemma commutator (t : ℝ) (f : Test) :
    C t (B t f) - B t (C t f) = (4 * (t : ℂ)) • f := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, map_add, map_sub, map_smul, map_neg, d_Z, d_Zbar,
    star_one, Complex.star_def, Complex.conj_I]
  rw [d_comm I 1 f, Z_Zbar f]
  trans (2 * (t : ℂ) - 2 * (t : ℂ) * I ^ 2) • f
  · module
  · congr 1
    rw [Complex.I_sq]
    ring

lemma energy_identity (t : ℝ) (f : Test) :
    pair (B t f) (B t f) - pair (C t f) (C t f) =
      (4 * (t : ℂ)) * pair f f := by
  calc
    _ = pair f (C t (B t f) - B t (C t f)) := by
      rw [pair_sub_right, pair_C f (B t f) t, pair_B f (C t f) t]
    _ = _ := by rw [commutator, pair_smul_right]

def mass (f : Test) : ℝ := (pair f f).re

lemma mass_integral (f : Test) : mass f = ∫ z : ℂ, Complex.normSq (f z) := by
  have h := integral_re (integrable_pair f f)
  simpa only [mass, pair, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h.symm

lemma integrable_normSq (f : Test) : Integrable (fun z : ℂ => Complex.normSq (f z)) := by
  have h := (integrable_pair f f).re
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h

lemma mass_nonneg (f : Test) : 0 ≤ mass f := by
  rw [mass_integral]
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

lemma mass_eq_zero (f : Test) (h : mass f = 0) : f = 0 := by
  rw [mass_integral] at h
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun z : ℂ => Complex.normSq_nonneg (f z)) (integrable_normSq f)).mp h
  have hf : (f : ℂ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hae] with z hz
    exact Complex.normSq_eq_zero.mp hz
  apply Subtype.ext
  exact ((smooth f).continuous.ae_eq_iff_eq volume continuous_zero).mp hf

/-- An actual weighted support estimate, independent of any frame existence. -/
theorem gaussian_coercivity (t : ℝ) (f : Test) :
    4 * t * mass f ≤ mass (B t f) := by
  have h := congrArg Complex.re (energy_identity t f)
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, zero_mul, add_zero] at h
  change mass (B t f) - mass (C t f) = 4 * t * mass f at h
  linarith [mass_nonneg (C t f)]

def gaussian (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((t : ℂ) / 2) * (z * star z))

lemma smooth_gaussian (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gaussian t) := by
  exact (contDiff_const.mul (contDiff_id.mul Complex.conjCLE.contDiff)).cexp

def W (t : ℝ) : Test →ₗ[ℂ] Test := mulSmooth (gaussian t) (smooth_gaussian t)

@[simp] lemma W_apply (t : ℝ) (f : Test) (z : ℂ) :
    (W t f : ℂ → ℂ) z = gaussian t z * f z := rfl

lemma gaussian_ne_zero (t : ℝ) (z : ℂ) : gaussian t z ≠ 0 := Complex.exp_ne_zero _

lemma fderiv_gaussian (t : ℝ) (z v : ℂ) :
    fderiv ℝ (gaussian t) z v =
      gaussian t z * ((t : ℂ) / 2) * (v * star z + z * star v) := by
  have hd := (((hasFDerivAt_id z).mul (Complex.conjCLE.hasFDerivAt (x := z))).const_mul
    ((t : ℂ) / 2)).cexp
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (gaussian t) z v = _ at he
  rw [he]
  simp only [smul_apply, add_apply,
    smul_eq_mul, Complex.conjCLE_apply]
  change gaussian t z * ((t : ℂ) / 2 * (z * star v + star z * v)) = _
  ring

lemma d_W (t : ℝ) (v : ℂ) (f : Test) (z : ℂ) :
    (d v (W t f) : ℂ → ℂ) z = gaussian t z *
      (((t : ℂ) / 2) * (v * star z + z * star v) * f z + (d v f : ℂ → ℂ) z) := by
  have hd := ((smooth_gaussian t).differentiable (by simp) z).hasFDerivAt.mul
    ((smooth f).differentiable (by simp) z).hasFDerivAt
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (fun z => gaussian t z * f z) z v = _
  simp only [Pi.mul_def] at he
  rw [he]
  simp only [add_apply, smul_apply,
    smul_eq_mul, fderiv_gaussian, d_apply]
  ring

/-- Exact Gaussian conjugation of twice the planar Cauchy--Riemann operator. -/
lemma gaussian_conjugation (t : ℝ) (f : Test) :
    B t (W t f) = W t (d 1 f + I • d I f) := by
  apply Subtype.ext
  funext z
  change (d 1 (W t f) : ℂ → ℂ) z + I * (d I (W t f) : ℂ → ℂ) z -
      (t : ℂ) * (z * (gaussian t z * f z)) =
    gaussian t z * ((d 1 f : ℂ → ℂ) z + I * (d I f : ℂ → ℂ) z)
  rw [d_W, d_W]
  simp only [star_one, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

open scoped BigOperators

lemma normSq_sum_mul {n : Type*} [Fintype n] (a u : n → ℂ) :
    Complex.normSq (∑ j, a j * u j) ≤
      (∑ j, Complex.normSq (a j)) * ∑ j, Complex.normSq (u j) := by
  simp only [Complex.normSq_eq_norm_sq]
  have h := norm_sum_le Finset.univ (fun j => a j * u j)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖u j‖))

lemma mass_bound {n : Type*} [Fintype n] (f : Test) (u : n → Test) (K : ℝ)
    (h : ∀ z : ℂ, Complex.normSq (f z) ≤ K * ∑ j, Complex.normSq (u j z)) :
    mass f ≤ K * ∑ j, mass (u j) := by
  simp only [mass_integral]
  have hi : Integrable (fun z : ℂ => ∑ j, Complex.normSq (u j z)) :=
    integrable_finsetSum _ (fun j _ => integrable_normSq (u j))
  calc
    _ ≤ ∫ z : ℂ, K * ∑ j, Complex.normSq (u j z) :=
      integral_mono (integrable_normSq f) (hi.const_mul K) h
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => integrable_normSq (u j))]

/-- Compact-kernel uniqueness with a coefficient bound only where a column is
nonzero. This is a genuine analytic theorem, not an assumed continuation rule. -/
theorem compact_kernel_of_bound {n : Type*} [Fintype n]
    (a : n → n → ℂ → ℂ) (u : n → Test) (K : ℝ)
    (hb : ∀ z : ℂ, (∃ j, u j z ≠ 0) → ∀ i,
      (∑ j, Complex.normSq (a i j z)) ≤ K)
    (heq : ∀ i (z : ℂ),
      (d 1 (u i) + I • d I (u i) : Test) z = ∑ j, a i j z * u j z) :
    ∀ i, u i = 0 := by
  classical
  let t : ℝ := (Fintype.card n : ℝ) * K + 1
  let w : n → Test := fun i => W t (u i)
  have hBw (i : n) (z : ℂ) :
      (B t (w i) : Test) z = ∑ j, a i j z * w j z := by
    dsimp [w]
    rw [gaussian_conjugation, W_apply, heq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpoint (i : n) (z : ℂ) :
      Complex.normSq ((B t (w i) : Test) z) ≤ K * ∑ j, Complex.normSq (w j z) := by
    rw [hBw]
    by_cases hu : ∃ j, u j z ≠ 0
    · exact (normSq_sum_mul (fun j => a i j z) (fun j => w j z)).trans
        (mul_le_mul_of_nonneg_right (hb z hu i)
          (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _))
    · have hw : ∀ j, w j z = 0 := by
        intro j
        have h := not_exists.mp hu j
        simp only [not_not] at h
        simp [w, h]
      simp [hw]
  have hi (i : n) : mass (B t (w i)) ≤ K * ∑ j, mass (w j) :=
    mass_bound _ w K (hpoint i)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (gaussian_coercivity t (w i)).trans (hi i))
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hn : 0 ≤ ∑ i, mass (w i) := Finset.sum_nonneg fun i _ => mass_nonneg _
  have hz : ∑ i, mass (w i) = 0 := by
    by_contra hne
    have hp : 0 < ∑ i, mass (w i) := lt_of_le_of_ne hn (Ne.symm hne)
    have htK : (Fintype.card n : ℝ) * K ≥ 0 := by
      by_cases hnon : ∃ j z, u j z ≠ 0
      · obtain ⟨j, z, hj⟩ := hnon
        have hk : 0 ≤ K := (Finset.sum_nonneg
          (fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (a j k z))).trans
            (hb z ⟨j, hj⟩ j)
        exact mul_nonneg (Nat.cast_nonneg _) hk
      · have hw : ∀ j, w j = 0 := by
          intro j
          apply Subtype.ext
          funext z
          have hj : u j z = 0 := by simpa using not_exists.mp (not_exists.mp hnon j) z
          simp [w, hj]
        have hm : ∑ i, mass (w i) = 0 := by simp [hw, mass, pair]
        exact False.elim (hne hm)
    dsimp [t] at h
    nlinarith
  have hz' : ∀ i, mass (w i) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mass_nonneg (w j))).mp hz i
      (Finset.mem_univ _)
  intro i
  have hw := mass_eq_zero (w i) (hz' i)
  apply Subtype.ext
  funext z
  have hval := congrArg (fun f : Test => f z) hw
  change gaussian t z * u i z = 0 at hval
  exact (mul_eq_zero.mp hval).resolve_left (gaussian_ne_zero t z)

/-- A smooth compactly supported solution of a planar matrix Cauchy--Riemann
system with continuous coefficients is zero. No smallness is imposed. -/
theorem compact_kernel {n : Type*} [Fintype n]
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, Continuous (a i j))
    (u : n → Test)
    (heq : ∀ i (z : ℂ),
      (d 1 (u i) + I • d I (u i) : Test) z = ∑ j, a i j z * u j z) :
    ∀ i, u i = 0 := by
  classical
  let S : Set ℂ := ⋃ i, tsupport (u i : ℂ → ℂ)
  have hc : IsCompact S := isCompact_iUnion fun i => compact (u i)
  let F : ℂ → ℝ := fun z => ∑ i, ∑ j, Complex.normSq (a i j z)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuousOn hF.continuousOn
  apply compact_kernel_of_bound a u K ?_ heq
  intro z hz i
  have hmem : z ∈ S := by
    obtain ⟨j, hj⟩ := hz
    exact Set.mem_iUnion.mpr ⟨j, subset_tsupport _ hj⟩
  calc
    (∑ j, Complex.normSq (a i j z)) ≤ F z := by
      dsimp [F]
      exact Finset.single_le_sum (f := fun k => ∑ j, Complex.normSq (a k j z))
        (fun k _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
        (Finset.mem_univ i)
    _ ≤ ‖F z‖ := le_abs_self _
    _ ≤ K := hK z hmem

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped BigOperators

lemma normSq_add_le (z w : ℂ) :
    normSq (z+w) ≤ 2*normSq z+2*normSq w := by
  simp only [normSq_eq_norm_sq]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma mass_add_le (f g : Test) : mass (f+g) ≤ 2*mass f+2*mass g := by
  rw [mass_integral,mass_integral,mass_integral]
  calc
    _ ≤ ∫ z : ℂ, (2*normSq (f z)+2*normSq (g z)) :=
      integral_mono (integrable_normSq (f+g))
        (((integrable_normSq f).const_mul 2).add ((integrable_normSq g).const_mul 2))
        (fun z => normSq_add_le _ _)
    _ = _ := by rw [integral_add ((integrable_normSq f).const_mul 2)
      ((integrable_normSq g).const_mul 2),integral_const_mul,integral_const_mul]

lemma mass_mul_bound (f g : Test) (K : ℝ)
    (hb : ∀ z, normSq (f z) ≤ K*normSq (g z)) : mass f ≤ K*mass g := by
  simpa using (mass_bound (n := Unit) f (fun _ => g) K (by simpa using hb))

lemma mass_smul (k : ℂ) (f : Test) : mass (k • f)=normSq k*mass f := by
  rw [mass_integral,mass_integral,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => normSq_mul k (f z))

lemma pair_derivative_cross (f : Test) : pair (d 1 f) (d I f)=pair (d I f) (d 1 f) := by
  calc
    _ = -pair f (d 1 (d I f)) := by rw [pair_d f (d I f) 1]; simp
    _ = -pair f (d I (d 1 f)) := by rw [d_comm]
    _ = _ := by rw [pair_d f (d 1 f) I]; simp

/-- The exact two-dimensional elliptic energy identity for the actual dbar operator. -/
lemma dbar_energy (f : Test) :
    mass (d 1 f + I • d I f)=mass (d 1 f)+mass (d I f) := by
  have h : pair (d 1 f + I • d I f) (d 1 f + I • d I f)=
      pair (d 1 f) (d 1 f)+pair (d I f) (d I f) := by
    rw [pair_add_left, pair_add_right, pair_add_right,
      pair_smul_right, pair_smul_left, pair_smul_left, pair_smul_right,
      pair_derivative_cross]
    simp only [Complex.star_def, Complex.conj_I]
    calc
      _ = pair (d 1 f) (d 1 f)-I^2*pair (d I f) (d I f) := by ring
      _ = _ := by simp
  exact congrArg Complex.re h

/-- Quantitative Gaussian absorption for a system with no smallness of coefficients. -/
theorem weighted_inhomogeneous_bound {n : Type*} [Fintype n]
    (a : n → n → ℂ → ℂ) (u v : n → Test) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ z, (∃ j, u j z ≠ 0) → ∀ i, (∑ j, normSq (a i j z)) ≤ K)
    (heq : ∀ i z, (d 1 (u i)+I • d I (u i) : Test) z =
      v i z+∑ j, a i j z*u j z) :
    let t := (Fintype.card n : ℝ)*K+1
    (∑ i, mass (W t (u i))) ≤ ∑ i, mass (W t (v i)) := by
  classical
  dsimp only
  let t : ℝ := (Fintype.card n : ℝ)*K+1
  let w : n → Test := fun i => W t (u i)
  let f : n → Test := fun i => W t (v i)
  have hi (i : n) : mass (B t (w i)) ≤
      2*mass (f i)+2*K*∑ j, mass (w j) := by
    have hp (z : ℂ) : normSq ((B t (w i) : Test) z) ≤
        2*normSq (f i z)+2*K*∑ j, normSq (w j z) := by
      have he : (B t (w i) : Test) z=f i z+∑ j, a i j z*w j z := by
        dsimp [w,f]
        rw [gaussian_conjugation,W_apply,heq,mul_add,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      apply (normSq_add_le _ _).trans
      have hm : normSq (∑ j, a i j z*w j z) ≤ K*∑ j, normSq (w j z) := by
        by_cases hu : ∃ j, u j z ≠ 0
        · exact (normSq_sum_mul (fun j => a i j z) (fun j => w j z)).trans
            (mul_le_mul_of_nonneg_right (hb z hu i)
              (Finset.sum_nonneg fun j _ => normSq_nonneg _))
        · have hw : ∀ j, w j z=0 := by
            intro j
            have hj : u j z=0 := by simpa using not_exists.mp hu j
            simp [w,hj]
          simp [hw]
      linarith
    rw [mass_integral,mass_integral]
    simp only [mass_integral]
    calc
      _ ≤ ∫ z : ℂ, (2*normSq (f i z)+2*K*∑ j, normSq (w j z)) :=
        integral_mono (integrable_normSq _) (((integrable_normSq _).const_mul 2).add
          ((integrable_finsetSum _ (fun j _ => integrable_normSq (w j))).const_mul _)) hp
      _ = _ := by
        rw [integral_add ((integrable_normSq _).const_mul 2)
          ((integrable_finsetSum _ (fun j _ => integrable_normSq (w j))).const_mul _),
          integral_const_mul,integral_const_mul,
          integral_finsetSum _ (fun j _ => integrable_normSq (w j))]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (gaussian_coercivity t (w i)).trans (hi i))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] at hs
  have hn : 0 ≤ (Fintype.card n : ℝ)*K := mul_nonneg (Nat.cast_nonneg _) hK
  have hw : 0 ≤ ∑ i, mass (w i) := Finset.sum_nonneg fun i _ => mass_nonneg _
  change (∑ i, mass (w i)) ≤ ∑ i, mass (f i)
  dsimp [t] at hs
  nlinarith [mul_nonneg hn hw]


lemma gaussian_inv (t : ℝ) (z : ℂ) : gaussian (-t) z*gaussian t z=1 := by
  rw [gaussian,gaussian,← Complex.exp_add]
  have h : (((-t : ℝ) : ℂ)/2)*(z*star z)+((t : ℂ)/2)*(z*star z)=0 := by
    push_cast
    ring
  rw [h,Complex.exp_zero]

lemma supported_weight_bound {S : Set ℂ} (hS : IsCompact S) (t : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Test, tsupport (f : ℂ → ℂ) ⊆ S →
      mass (W t f) ≤ C*mass f := by
  have hc : Continuous (fun z => normSq (gaussian t z)) :=
    continuous_normSq.comp (smooth_gaussian t).continuous
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro f hf
  apply mass_mul_bound
  intro z
  rw [W_apply,normSq_mul]
  by_cases hz : f z=0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (normSq_nonneg _)
    exact (le_abs_self (normSq (gaussian t z))).trans
      ((hK z (hf (subset_tsupport _ hz))).trans (le_max_left _ _))

lemma supported_weight_equivalence {S : Set ℂ} (hS : IsCompact S) (t : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Test, tsupport (f : ℂ → ℂ) ⊆ S →
      mass f ≤ C*mass (W t f) ∧ mass (W t f) ≤ C*mass f := by
  obtain ⟨C₁,hC₁,h₁⟩ := supported_weight_bound hS t
  obtain ⟨C₂,hC₂,h₂⟩ := supported_weight_bound hS (-t)
  refine ⟨max C₁ C₂,lt_of_lt_of_le hC₁ (le_max_left _ _),?_⟩
  intro f hf
  have hw : tsupport (W t f : ℂ → ℂ) ⊆ S :=
    (tsupport_mul_subset_right (f := gaussian t) (g := (f : ℂ → ℂ))).trans hf
  have he : W (-t) (W t f)=f := by
    apply Subtype.ext
    funext z
    change gaussian (-t) z*(gaussian t z*f z)=f z
    rw [← mul_assoc,gaussian_inv,one_mul]
  constructor
  · have hh := h₂ (W t f) hw
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (mass_nonneg _))
  · exact (h₁ f hf).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (mass_nonneg _))

lemma matrix_bound_on_compact {n : Type*} [Fintype n] {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, Continuous (a i j)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ S, ∀ i, (∑ j, normSq (a i j z)) ≤ K := by
  classical
  let F : ℂ → ℝ := fun z => ∑ i, ∑ j, normSq (a i j z)
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max K 0,le_max_right _ _,?_⟩
  intro z hz i
  calc
    _ ≤ F z := Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      (fun j _ => normSq_nonneg _)) (Finset.mem_univ i)
    _ ≤ ‖F z‖ := le_abs_self _
    _ ≤ K := hK z hz
    _ ≤ max K 0 := le_max_left _ _

/-- A true unweighted supported L2 estimate, uniform over all test columns on a
fixed compact set, for an arbitrary continuous matrix coefficient. -/
theorem supported_inhomogeneous_L2 {n : Type*} [Fintype n]
    {S : Set ℂ} (hS : IsCompact S) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, Continuous (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u v : n → Test,
      (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      (∀ i, tsupport (v i : ℂ → ℂ) ⊆ S) →
      (∀ i z, (d 1 (u i)+I • d I (u i) : Test) z=v i z+∑ j, a i j z*u j z) →
      (∑ i, mass (u i)) ≤ C*∑ i, mass (v i) := by
  classical
  obtain ⟨K,hK,hb⟩ := matrix_bound_on_compact hS a ha
  let t : ℝ := (Fintype.card n : ℝ)*K+1
  obtain ⟨C,hC,hW⟩ := supported_weight_equivalence hS t
  refine ⟨C*C,mul_pos hC hC,?_⟩
  intro u v hu hv heq
  have hbound : ∀ z, (∃ j, u j z ≠ 0) → ∀ i, (∑ j, normSq (a i j z)) ≤ K := by
    intro z hz
    obtain ⟨j,hj⟩ := hz
    exact hb z (hu j (subset_tsupport _ hj))
  have hw := weighted_inhomogeneous_bound a u v K hK hbound heq
  change (∑ i, mass (W t (u i))) ≤ ∑ i, mass (W t (v i)) at hw
  calc
    _ ≤ ∑ i, C*mass (W t (u i)) := Finset.sum_le_sum fun i _ => (hW _ (hu i)).1
    _ = C*∑ i, mass (W t (u i)) := (Finset.mul_sum ..).symm
    _ ≤ C*∑ i, mass (W t (v i)) := mul_le_mul_of_nonneg_left hw hC.le
    _ ≤ C*(C*∑ i, mass (v i)) := mul_le_mul_of_nonneg_left (by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (hW _ (hv i)).2) hC.le
    _ = _ := by ring

end ElasticityPlanar
namespace ElasticityDualSolvability
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma weak_unique_in_range (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) {f z w : H}
    (hz : z ∈ A.range.topologicalClosure) (hw : w ∈ A.range.topologicalClosure)
    (hez : ∀ v : D, inner ℂ z (A v)=inner ℂ f (v : H))
    (hew : ∀ v : D, inner ℂ w (A v)=inner ℂ f (v : H)) : z=w := by
  have horth : z-w ∈ A.rangeᗮ := by
    intro y hy
    obtain ⟨v,rfl⟩ := hy
    rw [inner_eq_zero_symm,inner_sub_left,hez,hew,sub_self]
  have hcl : z-w ∈ A.range.topologicalClosureᗮ := by simpa using horth
  have hself := hcl (z-w) (A.range.topologicalClosure.sub_mem hz hw)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

/-- Hilbert projection makes the actual Hahn--Banach solver canonical and linear.
It will be used for smooth parameter dependence of the planar right inverse. -/
theorem exists_linear_weak_solver (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ v : D, ‖(v : H)‖ ≤ C*‖A v‖) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ C ∧ ∀ f v, inner ℂ (T f) (A v)=inner ℂ f (v : H) := by
  let V := A.range.topologicalClosure
  have : CompleteSpace V := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hex (f : H) : ∃ z : H, z ∈ V ∧ ‖z‖ ≤ C*‖f‖ ∧
      ∀ v : D, inner ℂ z (A v)=inner ℂ f (v : H) := by
    obtain ⟨z,hz,heq⟩ := exists_weak_solution D A C hC hA f
    refine ⟨V.orthogonalProjectionOnto z,(V.orthogonalProjectionOnto z).property,
      (V.norm_orthogonalProjectionOnto_apply_le z).trans hz,?_⟩
    intro v
    let av : V := ⟨A v,Submodule.le_topologicalClosure _ (LinearMap.mem_range_self A v)⟩
    have h := V.inner_orthogonalProjectionOnto_eq_of_mem_right av z
    change inner ℂ _ (A v) = inner ℂ z (A v) at h
    exact h.trans (heq v)
  choose t ht hnorm heq using hex
  let L : H →ₗ[ℂ] H :=
    { toFun := t
      map_add' := by
        intro f g
        apply weak_unique_in_range D A (ht (f+g)) (V.add_mem (ht f) (ht g)) (heq (f+g))
        intro v
        simp only [inner_add_left,heq]
      map_smul' := by
        intro c f
        apply weak_unique_in_range D A (ht (c • f)) (V.smul_mem c (ht f)) (heq (c • f))
        intro v
        simp only [inner_smul_left,heq] }
  refine ⟨L.mkContinuous C hnorm,L.mkContinuous_norm_le hC hnorm,heq⟩
end ElasticityDualSolvability
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators

def toSchwartz : Test →ₗ[ℂ] 𝓢(ℂ,ℂ) where
  toFun f := (compact f).toSchwartzMap (smooth f)
  map_add' _ _ := by ext z; rfl
  map_smul' _ _ := by ext z; rfl
@[simp] lemma toSchwartz_apply (f : Test) (z : ℂ) : toSchwartz f z=f z := rfl
lemma toSchwartz_injective : Function.Injective toSchwartz := by
  intro u v h
  apply Subtype.ext
  exact congrArg (fun f : 𝓢(ℂ,ℂ) => (f : ℂ → ℂ)) h

def L2 : Test →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℂ)).toLinearMap.comp toSchwartz
lemma L2_injective : Function.Injective L2 := (SchwartzMap.injective_toLp 2 volume).comp toSchwartz_injective
lemma inner_L2 (f g : Test) : inner ℂ (L2 f) (L2 g)=pair f g := by
  simpa only [L2,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,SchwartzMap.toLpCLM_apply,
    RCLike.inner_apply',RCLike.star_def,toSchwartz_apply,pair] using
    SchwartzMap.inner_toL2_toL2_eq (toSchwartz f) (toSchwartz g) volume
lemma norm_L2_sq (f : Test) : ‖L2 f‖^2=mass f := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),inner_L2]
  rfl

def cj (f : Test) : Test := ⟨fun z => star (f z),
  ⟨Complex.conjCLE.contDiff.comp (smooth f),(compact f).comp_left (star_zero ℂ)⟩⟩
@[simp] lemma cj_apply (f : Test) (z : ℂ) : cj f z=star (f z) := rfl
@[simp] lemma cj_cj (f : Test) : cj (cj f)=f := by ext z; simp
lemma cj_d (v : ℂ) (f : Test) : cj (d v f)=d v (cj f) := by
  apply Subtype.ext
  funext z
  exact (deriv_conj f z v).symm
lemma cj_add (f g : Test) : cj (f+g)=cj f+cj g := by ext z; exact star_add _ _
lemma cj_neg (f : Test) : cj (-f)= -cj f := by ext z; exact star_neg _
lemma cj_smul (c : ℂ) (f : Test) : cj (c • f)=star c • cj f := by
  apply Subtype.ext
  funext z
  change star (c*f z)=star c*star (f z)
  rw [star_mul,mul_comm]
lemma mass_cj (f : Test) : mass (cj f)=mass f := by
  rw [mass_integral,mass_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [cj_apply,Complex.star_def,normSq_conj]
lemma support_cj (S : Set ℂ) (f : Test) (h : tsupport (f : ℂ → ℂ) ⊆ S) :
    tsupport (cj f : ℂ → ℂ) ⊆ S := by
  apply Set.Subset.trans (closure_mono ?_) h
  intro z hz hh
  exact hz (by change star (f z)=0; rw [hh,star_zero])

variable {n : Type*}
abbrev Hilbert (n : Type*) := PiLp 2 (fun _ : n => Lp ℂ 2 (volume : Measure ℂ))
def embed : (n → Test) →ₗ[ℂ] Hilbert n where
  toFun u := WithLp.toLp 2 (fun i => L2 (u i))
  map_add' _ _ := by apply PiLp.ext; intro i; exact map_add L2 _ _
  map_smul' _ _ := by apply PiLp.ext; intro i; exact map_smul L2 _ _
@[simp] lemma embed_apply (u : n → Test) (i : n) : embed u i = L2 (u i) := rfl
lemma embed_injective : Function.Injective (embed (n := n)) := by
  intro u v h
  funext i
  exact L2_injective (congrArg (fun w : Hilbert n => w i) h)
variable [Fintype n]
lemma norm_embed_sq (u : n → Test) : ‖embed u‖^2=∑ i, mass (u i) := by
  rw [PiLp.norm_eq_of_L2,Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl (fun i _ => norm_L2_sq (u i))
lemma norm_embed_cj (u : n → Test) : ‖embed (fun i => cj (u i))‖=‖embed u‖ := by
  have h : ‖embed (fun i => cj (u i))‖^2=‖embed u‖^2 := by
    simp only [norm_embed_sq,mass_cj]
  nlinarith [norm_nonneg (embed (fun i => cj (u i))),norm_nonneg (embed u)]

/-- Actual first-order matrix transport on compactly supported smooth tests. -/
def transport (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    (n → Test) →ₗ[ℂ] (n → Test) where
  toFun u i := d 1 (u i)+I • d I (u i)+∑ j, mulSmooth (a i j) (ha i j) (u j)
  map_add' u v := by
    funext i
    simp only [Pi.add_apply,map_add,Finset.sum_add_distrib,smul_add]
    abel
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply,map_smul,smul_add,Finset.smul_sum,smul_comm I c,RingHom.id_apply]

lemma transport_supported {S : Set ℂ} (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) (u : n → Test)
    (hu : ∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) :
    ∀ i, tsupport (transport a ha u i : ℂ → ℂ) ⊆ S := by
  intro i
  apply (tsupport_add _ _).trans
  apply Set.union_subset
  · apply (tsupport_add _ _).trans
    apply Set.union_subset
    · exact (tsupport_fderiv_apply_subset ℝ _).trans (hu i)
    · exact (tsupport_smul_subset_right (fun _ : ℂ => (I : ℂ)) (d I (u i) : ℂ → ℂ)).trans ((tsupport_fderiv_apply_subset ℝ I).trans (hu i))
  · have hsum (s : Finset n) : tsupport ((∑ j ∈ s, mulSmooth (a i j) (ha i j) (u j) : Test) : ℂ → ℂ) ⊆ S := by
      classical
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty,Submodule.coe_zero,tsupport_zero,Set.empty_subset]
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (tsupport_add _ _).trans (Set.union_subset ((tsupport_mul_subset_right).trans (hu j)) ih)
    exact hsum Finset.univ

/-- A true L2 lower bound for the actual transport operator. -/
theorem supported_transport_estimate {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      ‖embed u‖ ≤ C*‖embed (transport a ha u)‖ := by
  obtain ⟨C,hC,hest⟩ := supported_inhomogeneous_L2 hS (fun i j z => -(a i j z)) (fun i j => (ha i j).continuous.neg)
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun u hu => ?_⟩
  have heq : ∀ i z, (d 1 (u i)+I • d I (u i) : Test) z =
      transport a ha u i z+∑ j, -(a i j z)*u j z := by
    intro i z
    change _ = (d 1 (u i)+I • d I (u i) : Test) z+(∑ j, mulSmooth (a i j) (ha i j) (u j) : Test) z+_
    simp only [Submodule.coe_sum,Finset.sum_apply,mulSmooth,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_neg_distrib,neg_mul]
    ring
  have h := hest u (transport a ha u) hu (transport_supported a ha u hu) heq
  rw [← norm_embed_sq,← norm_embed_sq] at h
  have hs := Real.sq_sqrt hC.le
  have hp : 0 ≤ Real.sqrt C*‖embed (transport a ha u)‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (embed u)]
end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators
variable {n : Type*} [Fintype n]

/-- The genuine Hermitian formal adjoint of dbar+a, written using conjugation
and the transpose coefficient. No elliptic right inverse is assumed. -/
def adjTransport (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    (n → Test) →ₗ[ℂ] (n → Test) where
  toFun u i := -cj (transport (fun i j z => -a j i z) (fun i j => (ha j i).neg)
    (fun j => cj (u j)) i)
  map_add' u v := by
    have hh : (fun i => cj ((u+v) i))=(fun i => cj (u i))+(fun i => cj (v i)) := by
      funext i; exact cj_add _ _
    rw [hh,map_add]
    funext i
    simp only [Pi.add_apply,cj_add,neg_add_rev,add_comm]
  map_smul' c u := by
    have hh : (fun i => cj ((c • u) i))=star c • (fun i => cj (u i)) := by
      funext i; exact cj_smul _ _
    rw [hh,map_smul]
    funext i
    simp only [Pi.smul_apply,cj_smul,star_star,smul_neg,RingHom.id_apply]

lemma norm_adjTransport (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (u : n → Test) : ‖embed (adjTransport a ha u)‖=
      ‖embed (transport (fun i j z => -a j i z) (fun i j => (ha j i).neg) (fun i => cj (u i)))‖ := by
  change ‖embed (-(fun i => cj (transport (fun i j z => -a j i z) (fun i j => (ha j i).neg) (fun i => cj (u i)) i)))‖=_
  rw [map_neg,norm_neg,norm_embed_cj]

/-- Supported test vectors form the actual L2 domain for the adjoint. -/
def supported (S : Set ℂ) : Submodule ℂ (n → Test) where
  carrier := {u | ∀ i, tsupport (u i : ℂ → ℂ) ⊆ S}
  zero_mem' _ := by simpa only [Pi.zero_apply,Submodule.coe_zero,tsupport_zero] using Set.empty_subset S
  add_mem' hu hv i := (tsupport_add _ _).trans (Set.union_subset (hu i) (hv i))
  smul_mem' c u hu i := (tsupport_smul_subset_right (fun _ : ℂ => c) (u i : ℂ → ℂ)).trans (hu i)

/-- Actual supported matrix transport has a bounded linear L2 weak right inverse.
The estimate comes from the proved Gaussian positive commutator, not a smallness
assumption or a globally given frame. -/
theorem exists_planar_weak_inverse {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∃ T : Hilbert n →L[ℂ] Hilbert n, ‖T‖ ≤ C ∧
      ∀ f : Hilbert n, ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
        inner ℂ (T f) (embed (adjTransport a ha u))=inner ℂ f (embed u) := by
  obtain ⟨C,hC,hest⟩ := supported_transport_estimate hS (fun i j z => -a j i z) (fun i j => (ha j i).neg)
  have hbound (u : n → Test) (hu : ∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) :
      ‖embed u‖ ≤ C*‖embed (adjTransport a ha u)‖ := by
    rw [norm_adjTransport,← norm_embed_cj u]
    exact hest _ (fun i => support_cj S (u i) (hu i))
  let V := supported (n := n) S
  let e : V →ₗ[ℂ] Hilbert n := embed.comp V.subtype
  have hinj : Function.Injective e := by
    intro u v h
    exact Subtype.val_injective (embed_injective h)
  let E := LinearEquiv.ofInjective e hinj
  let A : e.range →ₗ[ℂ] Hilbert n :=
    (embed.comp (adjTransport a ha)).comp (V.subtype.comp E.symm.toLinearMap)
  have he (u : e.range) : e (E.symm u)=(u : Hilbert n) := congrArg Subtype.val (E.apply_symm_apply u)
  have hA (u : e.range) : ‖(u : Hilbert n)‖ ≤ C*‖A u‖ := by
    rw [← he u]
    exact hbound _ (E.symm u).property
  obtain ⟨T,hT,heq⟩ := ElasticityDualSolvability.exists_linear_weak_solver e.range A C hC.le hA
  refine ⟨C,hC,T,hT,fun f u hu => ?_⟩
  let u' : V := ⟨u,hu⟩
  have h := heq f (E u')
  change inner ℂ (T f) (embed (adjTransport a ha ((E.symm (E u') : V) : n → Test)))=inner ℂ f (e u') at h
  rw [E.symm_apply_apply] at h
  exact h
end ElasticityPlanar
namespace ElasticityPlanarDistribution
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap LineDeriv Laplacian ENNReal BigOperators
open ElasticityRegularity
abbrev Test := 𝓢(ℂ,ℂ)
abbrev Dist := 𝓢'(ℂ,ℂ)
def dbar (u : Dist) : Dist := ∂_{(1 : ℂ)} u+I • ∂_{I} u
def dhol (u : Dist) : Dist := ∂_{(1 : ℂ)} u-I • ∂_{I} u

lemma schwartz_derivative_commute (v w : ℂ) (f : Test) : ∂_{v} (∂_{w} f)=∂_{w} (∂_{v} f) := by
  ext x
  have hdd (v w : ℂ) : (∂_{v} (∂_{w} f) : Test) x =
      fderiv ℝ (fderiv ℝ (f : ℂ → ℂ)) x v w := by
    change fderiv ℝ (fun y => fderiv ℝ (f : ℂ → ℂ) y w) x v = _
    rw [fderiv_clm_apply (((f.smooth ⊤).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x)
      (differentiableAt_const w)]
    simp
  rw [hdd,hdd]
  exact (f.smooth ⊤).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _
lemma derivative_commute (v w : ℂ) (u : Dist) : ∂_{v} (∂_{w} u)=∂_{w} (∂_{v} u) := by
  ext φ
  change u (- ∂_{w} (- ∂_{v} φ))=u (- ∂_{v} (- ∂_{w} φ))
  simp only [LineDeriv.lineDerivOp_neg,neg_neg]
  rw [schwartz_derivative_commute]
lemma dhol_dbar (u : Dist) : dhol (dbar u)=Δ u := by
  rw [laplacian_eq_sum Complex.orthonormalBasisOneI]
  simp only [Complex.coe_orthonormalBasisOneI,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [dhol,dbar,LineDeriv.lineDerivOp_add,LineDeriv.lineDerivOp_smul,
    smul_add,smul_smul,Complex.I_mul_I,neg_one_smul]
  rw [derivative_commute (1 : ℂ) I]
  module
lemma dhol_sum {ι : Type*} (S : Finset ι) (u : ι → Dist) :
    dhol (∑ i ∈ S, u i)=∑ i ∈ S, dhol (u i) := by
  simp only [dhol,LineDeriv.lineDerivOp_sum,Finset.smul_sum,Finset.sum_sub_distrib]
lemma dhol_add (u v : Dist) : dhol (u+v)=dhol u+dhol v := by
  simp only [dhol,LineDeriv.lineDerivOp_add,smul_add]
  module
lemma LocalEqual.dhol {Ω : Set ℂ} {u v : Dist} (h : ElasticityRegularity.LocalEqual Ω u v) :
    ElasticityRegularity.LocalEqual Ω (dhol u) (dhol v) :=
  (h.derivative 1).sub ((h.derivative I).smul I)
lemma LocalSobolev.dhol {Ω : Set ℂ} {s : ℝ} {u : Dist} (h : ElasticityRegularity.LocalSobolev Ω s u) :
    ElasticityRegularity.LocalSobolev Ω (s-1) (dhol u) :=
  (h.derivative 1).sub ((h.derivative I).smul I)

/-- Actual planar first-order equation on distributions, not an abstract
regularity or frame existence interface. -/
def Equation {n : Type*} [Fintype n] (Ω : Set ℂ) (a : n → n → ℂ → ℂ) (u f : n → Dist) : Prop :=
  ∀ i, ElasticityRegularity.LocalEqual Ω (dbar (u i)) (f i+∑ j, smulLeftCLM ℂ (a i j) (u j))

theorem local_gain {n : Type*} [Fintype n] {Ω : Set ℂ} {s : ℝ}
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u f : n → Dist) (heq : Equation Ω a u f)
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω s (u i))
    (hf : ∀ i, ElasticityRegularity.LocalSobolev Ω s (f i)) :
    ∀ i, ElasticityRegularity.LocalSobolev Ω (s+1) (u i) := by
  intro i
  apply local_laplacian_gain_basis Complex.orthonormalBasisOneI (hu i)
  have he := LocalEqual.dhol (heq i)
  rw [dhol_dbar,dhol_add,dhol_sum] at he
  apply he.localSobolev
  exact (LocalSobolev.dhol (hf i)).add (ElasticityRegularity.LocalSobolev.sum Finset.univ (fun j _ =>
    LocalSobolev.dhol ((hu j).coeff (ha i j))))

theorem local_all_orders {n : Type*} [Fintype n] {Ω : Set ℂ}
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u f : n → Dist) (heq : Equation Ω a u f)
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (u i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (f i)) :
    ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (u i) := by
  intro N
  induction N with
  | zero => rw [Nat.cast_zero]; exact hu
  | succ N hN =>
    rw [Nat.cast_add,Nat.cast_one]
    exact local_gain a ha u f heq hN (hf N)

theorem cutoff_smooth {n : Type*} [Fintype n] {Ω : Set ℂ}
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u f : n → Dist) (heq : Equation Ω a u f)
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (u i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (f i))
    (i : n) {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    ∃ v : BoundedContinuousFunction ℂ ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : ℂ → ℂ) ∧
      smulLeftCLM ℂ g (u i)=((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure ℂ)) : Dist) :=
  all_orders_smooth_representative (fun N => local_all_orders a ha u f heq hu hf N i g hg hc hs)
end ElasticityPlanarDistribution
namespace ElasticityPlanar
open MeasureTheory Complex TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators LineDeriv
variable {n : Type*} [Fintype n]

lemma toSchwartz_d (v : ℂ) (φ : Test) : toSchwartz (d v φ)=∂_{v} (toSchwartz φ) := by
  ext z
  rfl
lemma toSchwartz_mul (a : ℂ → ℂ) (ha : a.HasTemperateGrowth) (φ : Test) :
    toSchwartz (mulSmooth a ha.1 φ)=SchwartzMap.smulLeftCLM ℂ a (toSchwartz φ) := by
  ext z
  simp only [toSchwartz_apply,SchwartzMap.smulLeftCLM_apply_apply ha,smul_eq_mul]
  rfl
lemma Lp_test (w : Lp ℂ 2 (volume : Measure ℂ)) (φ : Test) :
    (w : 𝓢'(ℂ,ℂ)) (toSchwartz φ) = inner ℂ (L2 (cj φ)) w := by
  rw [Lp.toTemperedDistribution_apply,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(toSchwartz (cj φ)).coeFn_toLp 2 volume] with z hz
  change φ z • w z = inner ℂ ((L2 (cj φ)) z) (w z)
  change (L2 (cj φ) : ℂ → ℂ) z=cj φ z at hz
  rw [hz]
  simp only [cj_apply,RCLike.inner_apply',starRingEnd_apply,star_star,smul_eq_mul,mul_comm]

lemma vector_transpose (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (w : n → 𝓢'(ℂ,ℂ)) (φ : n → Test) :
    (∑ i, (ElasticityPlanarDistribution.dbar (w i)+∑ j, smulLeftCLM ℂ (a i j) (w j)) (toSchwartz (φ i))) =
      ∑ i, w i (toSchwartz (- transport (fun i j z => -a j i z) (fun i j => (ha j i).1.neg) φ i)) := by
  simp only [ElasticityPlanarDistribution.dbar,add_apply,sum_apply,smul_apply,
    smulLeftCLM_apply_apply,TemperedDistribution.lineDerivOp_apply_apply]
  simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,map_neg,map_add,map_smul,map_sum,
    toSchwartz_d, smul_eq_mul]
  have hm (i j : n) : toSchwartz (mulSmooth (fun z => -a j i z) (ha j i).1.neg (φ j)) =
      -SchwartzMap.smulLeftCLM ℂ (a j i) (toSchwartz (φ j)) := by
    ext z
    simp only [toSchwartz_apply,neg_apply,SchwartzMap.smulLeftCLM_apply_apply (ha j i),smul_eq_mul]
    change (-a j i z)*φ j z= -(a j i z*φ j z)
    ring
  simp only [hm,map_neg,Finset.sum_neg_distrib,neg_add_rev,neg_neg,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [mul_neg,Finset.sum_neg_distrib]
  ring

lemma weak_to_vector_distribution (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth) (S : Set ℂ) (w f : Hilbert n)
    (heq : ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      inner ℂ w (embed (adjTransport a (fun i j => (ha i j).1) u))=inner ℂ f (embed u))
    (φ : n → Test) (hφ : ∀ i, tsupport (φ i : ℂ → ℂ) ⊆ S) :
    (∑ i, (ElasticityPlanarDistribution.dbar (w i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (w j : 𝓢'(ℂ,ℂ))) (toSchwartz (φ i))) =
      ∑ i, (f i : 𝓢'(ℂ,ℂ)) (toSchwartz (φ i)) := by
  rw [vector_transpose a ha]
  simp only [Lp_test]
  have h := congrArg star (heq (fun i => cj (φ i)) (fun i => support_cj S _ (hφ i)))
  have hs (u v : Hilbert n) : star (inner ℂ u v)=inner ℂ v u := inner_conj_symm (𝕜 := ℂ) v u
  rw [hs,hs] at h
  simp only [PiLp.inner_apply,embed_apply] at h
  have he (i : n) : adjTransport a (fun i j => (ha i j).1) (fun i => cj (φ i)) i =
      cj (-transport (fun i j z => -a j i z) (fun i j => (ha j i).1.neg) φ i) := by
    simp only [adjTransport,LinearMap.coe_mk,AddHom.coe_mk,cj_cj,cj_neg]
  simpa only [he] using h

lemma weak_to_local_equation (Ω S : Set ℂ) (hΩ : Ω ⊆ S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth) (w f : Hilbert n)
    (heq : ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      inner ℂ w (embed (adjTransport a (fun i j => (ha i j).1) u))=inner ℂ f (embed u)) :
    ∀ i, ElasticityRegularity.LocalEqual Ω (ElasticityPlanarDistribution.dbar (w i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (w j : 𝓢'(ℂ,ℂ))) (f i : 𝓢'(ℂ,ℂ)) := by
  classical
  intro i φ hc hs
  let φ' : Test := ⟨φ,⟨φ.smooth ⊤,hc⟩⟩
  let ψ : n → Test := fun j => if j=i then φ' else 0
  have hψ : ∀ j, tsupport (ψ j : ℂ → ℂ) ⊆ S := by
    intro j
    by_cases hji : j=i
    · simpa only [ψ,ite_eq_left hji] using hs.trans hΩ
    · simpa only [ψ,ite_eq_right hji,Submodule.coe_zero,tsupport_zero] using Set.empty_subset S
  have h := weak_to_vector_distribution a ha S w f heq ψ hψ
  simpa only [ψ,apply_ite,ite_true,map_zero,Finset.sum_ite_eq',Finset.mem_univ,
    show toSchwartz φ'=φ from by ext z; rfl] using h
end ElasticityPlanar
section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
namespace ElasticityRegularity

/-- The closed graph argument supplies norms for genuine distribution operators,
not additional quantitative regularity assumptions. -/
theorem exists_continuous_lift
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (J : Y →L[ℂ] Z) (hJ : Function.Injective J) (T : X →L[ℂ] Z)
    (hT : ∀ x, ∃ y, J y=T x) :
    ∃ L : X →L[ℂ] Y, ∀ x, J (L x)=T x := by
  choose l hl using hT
  let L : X →ₗ[ℂ] Y := {
    toFun := l
    map_add' := fun x y => hJ (by rw [map_add,hl,hl,hl,map_add])
    map_smul' := fun c x => hJ (by rw [map_smul,hl,hl,map_smul]; rfl) }
  have hc : IsClosed (L.graph : Set (X × Y)) := by
    have he : (L.graph : Set (X × Y))={p | T p.1=J p.2} := by
      ext p
      change p.2=L p.1 ↔ T p.1=J p.2
      constructor
      · intro h
        rw [h]
        exact (hl p.1).symm
      · intro h
        apply hJ
        exact h.symm.trans (hl p.1).symm
    rw [he]
    exact isClosed_eq (T.continuous.comp continuous_fst) (J.continuous.comp continuous_snd)
  exact ⟨⟨L,L.continuous_of_isClosed_graph hc⟩,hl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lp_distribution_injective : Function.Injective
    (fun u : Lp ℂ 2 (volume : Measure E) => (u : 𝓢'(E,ℂ))) := by
  intro u v huv
  apply Lp.ext
  have h : LocalEqual Set.univ (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ)) :=
    fun _ _ _ => congrArg (fun T : 𝓢'(E,ℂ) => T _) huv
  filter_upwards [h.lp_ae isOpen_univ u v] with x hx
  exact hx (Set.mem_univ x)

/-- H^s is represented isometrically by L2 via J^{-s}; its injection is into the
actual space of tempered distributions. -/
def sobolevInjection (s : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] 𝓢'(E,ℂ) :=
  (besselPotential E ℂ (-s)).comp (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2)

lemma sobolevInjection_injective (s : ℝ) :
    Function.Injective (sobolevInjection (E := E) s) := by
  intro u v huv
  have h := congrArg (besselPotential E ℂ s) huv
  have hh : (u : 𝓢'(E,ℂ))=(v : 𝓢'(E,ℂ)) := by
    simpa only [sobolevInjection,ContinuousLinearMap.comp_apply,
      besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
      ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply] using h
  exact lp_distribution_injective hh

lemma sobolevInjection_mem (s : ℝ) (f : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (sobolevInjection s f) := by
  refine ⟨f,?_⟩
  simp only [sobolevInjection,ContinuousLinearMap.comp_apply,
    besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
    ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply]

lemma memSobolev_iff_range (s : ℝ) (u : 𝓢'(E,ℂ)) :
    MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure E), sobolevInjection s f=u := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f,?_⟩
    change besselPotential E ℂ (-s) (f : 𝓢'(E,ℂ))=u
    exact (besselPotential_neg_apply_eq_iff s (f : 𝓢'(E,ℂ)) u).mpr hf
  · rintro ⟨f,rfl⟩
    exact sobolevInjection_mem s f

/-- A qualitative everywhere-defined Sobolev mapping theorem for a continuous
actual distribution operator automatically gives its bounded Sobolev realization.
This is useful for smooth multipliers and coordinate derivatives on cutoffs. -/
theorem exists_sobolev_realization (s t : ℝ) (P : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ))
    (hP : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (P u)) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection t (L f)=P (sobolevInjection s f) := by
  exact exists_continuous_lift (sobolevInjection t) (sobolevInjection_injective t)
    (P.comp (sobolevInjection s)) (fun f =>
      (memSobolev_iff_range t _).mp (hP _ (sobolevInjection_mem s f)))

theorem exists_bounded_sobolev_derivative (s : ℝ) (m : E) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (s-1) (L f)=∂_{m} (sobolevInjection s f) := by
  exact exists_sobolev_realization s (s-1) (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E,ℂ) m)
    (fun _ h => h.lineDerivOp)

theorem exists_bounded_sobolev_inclusion {s t : ℝ} (hst : t ≤ s) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection t (L f)=sobolevInjection s f := by
  exact exists_sobolev_realization s t (ContinuousLinearMap.id ℂ _)
    (fun _ h => h.mono hst)

end ElasticityRegularity

end
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Compact smooth multiplication on the negative initial Sobolev order in
which the physical divergence is initially controlled. -/
theorem sobolev_neg_one_product {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,ℂ)} (hu : MemSobolev (-1) 2 u) :
    MemSobolev (-1) 2 (smulLeftCLM ℂ g u) := by
  let v := besselPotential E ℂ (-2) u
  have hv : MemSobolev 1 2 v := by
    apply memSobolev_besselPotential_iff.mpr
    norm_num
    exact hu
  have hv0 : MemSobolev 0 2 v := hv.mono (by norm_num)
  let b := stdOrthonormalBasis ℝ E
  have hd : MemSobolev (-1) 2 (smulLeftCLM ℂ g (Δ v)) := by
    rw [laplacian_eq_sum b,map_sum]
    apply sobolev_sum Finset.univ
    intro i _
    apply sobolev_zero_product_derivative hg hc (b i)
    simpa only [sub_self] using (hv.lineDerivOp (m := b i))
  have hp : (-(2*Real.pi)^2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have he : u=v+(-(2*Real.pi)^2 : ℝ)⁻¹ • Δ v := by
    rw [laplacian_eq_fourierMultiplierCLM,smul_smul,inv_mul_cancel₀ hp,one_smul,
      ← besselPotential_two]
    simp only [v,besselPotential_besselPotential_apply,neg_add_cancel,
      besselPotential_zero,ContinuousLinearMap.id_apply]
  rw [he,map_add,ContinuousLinearMap.map_smul_of_tower]
  exact ((sobolev_zero_product (hc.hasTemperateGrowth hg)
    (compact_bounded_multiplier hg hc) hv0).mono (by norm_num)).add
      (sobolev_real_smul hd _)

lemma sobolev_product_step_down (s : ℝ)
    (hm : ∀ (g : E → ℂ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∀ u : 𝓢'(E,ℂ), MemSobolev s 2 u → MemSobolev s 2 (smulLeftCLM ℂ g u))
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,ℂ)} (hu : MemSobolev (s-1) 2 u) :
    MemSobolev (s-1) 2 (smulLeftCLM ℂ g u) := by
  let v := besselPotential E ℂ (-2) u
  have hv : MemSobolev (s+1) 2 v := by
    apply memSobolev_besselPotential_iff.mpr
    convert hu using 1
    ring
  have hvs : MemSobolev s 2 v := hv.mono (by linarith)
  let b := stdOrthonormalBasis ℝ E
  have hd : MemSobolev (s-1) 2 (smulLeftCLM ℂ g (Δ v)) := by
    rw [laplacian_eq_sum b,map_sum]
    apply sobolev_sum Finset.univ
    intro i _
    have hdi : MemSobolev s 2 (∂_{b i} v) := by
      simpa only [add_sub_cancel_right] using (hv.lineDerivOp (m := b i))
    have hgd := smooth_derivative hg (b i)
    have hcd := compact_derivative hc (b i)
    have h₁ := (hm g hg hc _ hdi).lineDerivOp (m := b i)
    have h₂ := (hm _ hgd hcd _ hdi).mono (by linarith : s-1 ≤ s)
    have hh := h₁.sub h₂
    rw [distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd),
      add_sub_cancel_left] at hh
    exact hh
  have hp : (-(2*Real.pi)^2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have he : u=v+(-(2*Real.pi)^2 : ℝ)⁻¹ • Δ v := by
    rw [laplacian_eq_fourierMultiplierCLM,smul_smul,inv_mul_cancel₀ hp,one_smul,
      ← besselPotential_two]
    simp only [v,besselPotential_besselPotential_apply,neg_add_cancel,
      besselPotential_zero,ContinuousLinearMap.id_apply]
  rw [he,map_add,ContinuousLinearMap.map_smul_of_tower]
  exact ((hm g hg hc _ hvs).mono (by linarith)).add (sobolev_real_smul hd _)

/-- Smooth compact multiplication preserves every integral Sobolev order,
including the H^-2 forcing order in the first augmented bootstrap step. -/
theorem sobolev_negative_product (n : ℕ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,ℂ)} (hu : MemSobolev (-(n : ℝ)) 2 u) :
    MemSobolev (-(n : ℝ)) 2 (smulLeftCLM ℂ g u) := by
  induction n generalizing g u with
  | zero =>
    simp only [Nat.cast_zero,neg_zero] at hu ⊢
    exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu
  | succ n ih =>
    have hh := sobolev_product_step_down (-(n : ℝ))
      (fun g hg hc u hu => ih hg hc hu) hg hc (u := u)
    have he : (-(n : ℝ)-1 : ℝ)= -((n+1 : ℕ) : ℝ) := by push_cast; ring
    rw [he] at hh
    exact hh hu

theorem exists_bounded_negative_multiplier (n : ℕ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (-(n : ℝ)) (L f)=smulLeftCLM ℂ g (sobolevInjection (-(n : ℝ)) f) := by
  exact exists_sobolev_realization _ _ (smulLeftCLM ℂ g)
    (fun _ h => sobolev_negative_product n hg hc h)

theorem exists_bounded_nat_multiplier (n : ℕ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (n : ℝ) (L f)=smulLeftCLM ℂ g (sobolevInjection (n : ℝ) f) := by
  exact exists_sobolev_realization _ _ (smulLeftCLM ℂ g)
    (fun _ h => sobolev_nat_product (stdOrthonormalBasis ℝ E) n hg hc h)
end ElasticityRegularity
namespace ElasticityDualSolvability
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded zeroth-order perturbation of an actual weak right inverse. -/
theorem perturbed_weak_solver (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (T B Q : H →L[ℂ] H)
    (hT : ∀ f v, inner ℂ (T f) (A v)=inner ℂ f (v : H))
    (hQ : (1+B*T)*Q=1) (f : H) (v : D) :
    inner ℂ ((T*Q) f) (A v+B.adjoint (v : H))=inner ℂ f (v : H) := by
  rw [mul_apply_eq_comp,inner_add_right,hT,ContinuousLinearMap.adjoint_inner_right,
    ← inner_add_left]
  have h := congrArg (fun L : H →L[ℂ] H => L f) hQ
  simpa only [mul_apply_eq_comp,add_apply,
    one_apply_eq_self] using congrArg (fun y => inner ℂ y (v : H)) h

/-- The perturbative solver exists without adding a range surjectivity
assumption. The smallness condition is strictly local in parameter space. -/
theorem perturbed_weak_inverse (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (T B : H →L[ℂ] H)
    (hT : ∀ f v, inner ℂ (T f) (A v)=inner ℂ f (v : H))
    (hBT : ‖B*T‖<1) :
    ∀ f v, inner ℂ ((T*Ring.inverse (1+B*T)) f) (A v+B.adjoint (v : H))=
      inner ℂ f (v : H) := by
  have hu : IsUnit (1+B*T) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using hBT : ‖-(B*T)‖<1)
  exact perturbed_weak_solver D A T B _ hT (Ring.mul_inverse_cancel _ hu)

/-- Smooth dependence of the local Neumann inverse, established with the stock
Banach-algebra inversion theorem. -/
theorem smooth_local_weak_inverse {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (T : H →L[ℂ] H) (B : P → H →L[ℂ] H) {p : P}
    (hB : ContDiffAt ℝ (⊤ : ℕ∞) B p) (hBT : ‖B p*T‖<1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => T*Ring.inverse (1+B q*T)) p := by
  have hu : IsUnit (1+B p*T) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using hBT : ‖-(B p*T)‖<1)
  obtain ⟨u,hu⟩ := hu
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) Ring.inverse (1+B p*T) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (1 : H →L[ℂ] H)+B q*T) p :=
    contDiffAt_const.add (hB.mul contDiffAt_const)
  have hc := hi.comp p hg
  exact contDiffAt_const.mul hc
end ElasticityDualSolvability

end

end OAI
