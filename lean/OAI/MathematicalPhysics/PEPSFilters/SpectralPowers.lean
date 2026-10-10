import Mathlib

namespace OAI

/-! Spectral functional calculus, analytic matrix powers and eigenprojectors. -/

noncomputable section
open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

def applyFn {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => f (hA.eigenvalues i)))

lemma applyFn_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    applyFn hA (fun x => f x * g x) = applyFn hA f * applyFn hA g := by
  unfold applyFn
  rw [← map_mul, Matrix.diagonal_mul_diagonal]

lemma applyFn_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    applyFn hA (fun _ => 1) = 1 := by
  simp [applyFn]

lemma applyFn_star {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    applyFn hA (fun x => star (f x)) = star (applyFn hA f) := by
  unfold applyFn
  rw [← map_star]
  congr 1
  simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Pi.star_def]

lemma applyFn_norm {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    ‖applyFn hA f‖ = ‖fun i => f (hA.eigenvalues i)‖ := by
  simp only [applyFn, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

lemma applyFn_unitary {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ)
    (hf : ∀ i, star (f (hA.eigenvalues i)) * f (hA.eigenvalues i) = 1) :
    applyFn hA f ∈ unitary (Matrix n n ℂ) := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [← applyFn_star, ← applyFn_mul]
  convert applyFn_one hA using 1
  unfold applyFn
  congr 2
  funext i
  exact hf i

lemma applyFn_positive {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (applyFn hA (fun x => (f x : ℂ))).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (by intro i; exact_mod_cast hf i)
  exact hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix n n ℂ)

lemma eigenvalues_conjugate {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (u : unitary (Matrix n n ℂ)) :
    (hA.mul_mul_conjTranspose_same (u : Matrix n n ℂ)).isHermitian.eigenvalues =
      hA.isHermitian.eigenvalues := by
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
  rw [Matrix.charpoly_mul_comm]
  rw [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, u.property.1, one_mul]

lemma tracePower_conjugate {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (u : unitary (Matrix n n ℂ)) (p : ℝ) :
    (∑ i, Real.rpow
      ((hA.mul_mul_conjTranspose_same (u : Matrix n n ℂ)).isHermitian.eigenvalues i) p) =
      ∑ i, Real.rpow (hA.isHermitian.eigenvalues i) p := by
  rw [eigenvalues_conjugate hA u]

lemma sum_eigenvalues_applyFn {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hB : (applyFn hA (fun x => (f x : ℂ))).IsHermitian)
    (g : ℝ → ℝ) :
    (∑ i, g (hB.eigenvalues i)) = ∑ i, g (f (hA.eigenvalues i)) := by
  have hc : (applyFn hA (fun x => (f x : ℂ))).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (f (hA.eigenvalues i) : ℂ)) := by
    unfold applyFn
    rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
    simp [Matrix.charpoly_diagonal]
  have hr := hB.roots_charpoly_eq_eigenvalues
  rw [hc, Polynomial.roots_prod] at hr
  · simp only [Polynomial.roots_X_sub_C] at hr
    have he := congrArg (fun s : Multiset ℂ => (s.map (fun z => g z.re)).sum) hr
    simpa only [Multiset.map_bind, Multiset.bind_map, Multiset.map_singleton,
      Multiset.bind_singleton, Multiset.map_map, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Finset.sum_eq_multiset_sum] using he.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

def scalarPower (a x : ℝ) (z : ℂ) : ℂ :=
  if x = 0 then 0 else Complex.exp (z * ((a / 2 * Real.log x : ℝ) : ℂ))

lemma scalarPower_entire (a x : ℝ) : Differentiable ℂ (scalarPower a x) := by
  unfold scalarPower
  split_ifs <;> fun_prop

lemma scalarPower_one {exponent value : ℝ} (ha : 0 < exponent) (hx : 0 ≤ value) :
    scalarPower exponent value 1 = ((value ^ (exponent / 2) : ℝ) : ℂ) := by
  by_cases hzero : value = 0
  · simp [scalarPower, hzero, Real.zero_rpow (by positivity : exponent / 2 ≠ 0)]
  · have hx' : 0 < value := lt_of_le_of_ne hx (Ne.symm hzero)
    simp only [scalarPower, hzero, ↓reduceIte, one_mul,
      Real.rpow_def_of_pos hx', Complex.ofReal_exp]
    congr 2
    ring

lemma scalarPower_norm_le_one {exponent value : ℝ}
    (ha : 0 ≤ exponent) (hx : 0 ≤ value) (hx1 : value ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖scalarPower exponent value z‖ ≤ 1 := by
  by_cases hzero : value = 0
  · simp [scalarPower, hzero]
  · simp only [scalarPower, hzero, ↓reduceIte, Complex.norm_exp, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hz
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos hx hx1))

end PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma applyFn_id {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    applyFn hA (fun x => (x : ℂ)) = A := hA.spectral_theorem.symm

lemma applyFn_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    (applyFn hA f).trace = ∑ i, f (hA.eigenvalues i) := by
  unfold applyFn
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc, hA.eigenvectorUnitary.property.1, one_mul]
  exact Matrix.trace_diagonal _

lemma density_eigenvalues_sum {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) : ∑ i, hA.isHermitian.eigenvalues i = 1 := by
  have h := congrArg Complex.re (hA.isHermitian.trace_eq_sum_eigenvalues)
  simpa only [htr, Complex.one_re, Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using h.symm

lemma density_eigenvalues_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) (i : n) : hA.isHermitian.eigenvalues i ≤ 1 := by
  rw [← density_eigenvalues_sum hA htr]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

def spectralCLM {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  ((Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary).toAlgEquiv.toLinearMap.comp
    (Matrix.diagonalLinearMap n ℂ ℂ)).toContinuousLinearMap

lemma spectralCLM_apply {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    spectralCLM hA (fun i => f (hA.eigenvalues i)) = applyFn hA f := rfl

lemma applyFn_differentiable {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℂ → ℝ → ℂ) (hf : ∀ i, Differentiable ℂ (fun z => f z (hA.eigenvalues i))) :
    Differentiable ℂ (fun z => applyFn hA (f z)) := by
  exact (spectralCLM hA).differentiable.comp (differentiable_pi.mpr hf)

lemma applyFn_hasDerivAt {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℂ → ℝ → ℂ) (g : ℝ → ℂ) {z : ℂ}
    (hf : ∀ i, HasDerivAt (fun w => f w (hA.eigenvalues i)) (g (hA.eigenvalues i)) z) :
    HasDerivAt (fun w => applyFn hA (f w)) (applyFn hA g) z := by
  exact (spectralCLM hA).hasFDerivAt.comp_hasDerivAt z (hasDerivAt_pi.mpr hf)

lemma power_entire {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ) :
    Differentiable ℂ (fun z => applyFn hA (fun x => scalarPower a x z)) :=
  applyFn_differentiable hA _ (fun i => scalarPower_entire a (hA.eigenvalues i))

lemma power_norm_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖applyFn hA.isHermitian (fun x => scalarPower a x z)‖ ≤ 1 := by
  rw [applyFn_norm]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i =>
    scalarPower_norm_le_one ha (hA.eigenvalues_nonneg i)
      (density_eigenvalues_le_one hA htr i) hz)

lemma power_one_positive {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {a : ℝ} (ha : 0 < a) :
    (applyFn hA.isHermitian (fun x => scalarPower a x 1)).PosSemidef := by
  have he : applyFn hA.isHermitian (fun x => scalarPower a x 1) =
      applyFn hA.isHermitian (fun x => ((x ^ (a / 2) : ℝ) : ℂ)) := by
    unfold applyFn
    congr 2
    funext i
    exact scalarPower_one ha (hA.eigenvalues_nonneg i)
  rw [he]
  exact applyFn_positive hA.isHermitian _ (fun i => Real.rpow_nonneg (hA.eigenvalues_nonneg i) _)

lemma power_one_tracePower {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) {a : ℝ} (ha : 0 < a) :
    (∑ i, Real.rpow ((power_one_positive hA ha).isHermitian.eigenvalues i) (2 / a)) = 1 := by
  have he : applyFn hA.isHermitian (fun x => scalarPower a x 1) =
      applyFn hA.isHermitian (fun x => ((x ^ (a / 2) : ℝ) : ℂ)) := by
    unfold applyFn
    congr 2
    funext i
    exact scalarPower_one ha (hA.eigenvalues_nonneg i)
  have hp := power_one_positive hA ha
  rw [he] at hp
  have hev : (power_one_positive hA ha).isHermitian.eigenvalues = hp.isHermitian.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr (congrArg Matrix.charpoly he)
  rw [hev]
  have ht : a / 2 * (2 / a) = 1 := by field_simp [ha.ne']
  calc
    _ = ∑ i, (hA.isHermitian.eigenvalues i ^ (a / 2)).rpow (2 / a) :=
      sum_eigenvalues_applyFn hA.isHermitian (fun x => x ^ (a / 2)) hp.isHermitian
        (fun x => x.rpow (2 / a))
    _ = ∑ i, hA.isHermitian.eigenvalues i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.rpow_eq_pow, ← Real.rpow_mul (hA.eigenvalues_nonneg i), ht, Real.rpow_one]
    _ = 1 := density_eigenvalues_sum hA htr

end PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma scalarPower_hasDerivAt_zero (a x : ℝ) :
    HasDerivAt (scalarPower a x) ((a / 2 * Real.log x : ℝ) : ℂ) 0 := by
  by_cases hx : x = 0
  · subst x
    have he : scalarPower a 0 = fun _ : ℂ => 0 := by
      funext z
      simp only [scalarPower, ↓reduceIte]
    rw [he]
    simpa only [Real.log_zero, mul_zero, Complex.ofReal_zero] using
      (hasDerivAt_const (0 : ℂ) (0 : ℂ))
  · have he : scalarPower a x = fun z : ℂ => Complex.exp (z * ((a / 2 * Real.log x : ℝ) : ℂ)) := by
      funext z
      exact ite_eq_right hx
    rw [he]
    simpa only [id_eq, zero_mul, Complex.exp_zero, one_mul] using
      ((hasDerivAt_id (0 : ℂ)).mul_const ((a / 2 * Real.log x : ℝ) : ℂ)).cexp

lemma power_hasDerivAt_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ) :
    HasDerivAt (fun z => applyFn hA (fun x => scalarPower a x z))
      (applyFn hA (fun x => ((a / 2 * Real.log x : ℝ) : ℂ))) 0 :=
  applyFn_hasDerivAt hA _ _ (fun i => scalarPower_hasDerivAt_zero a (hA.eigenvalues i))

def scalarPhase (a x t : ℝ) : ℂ :=
  if x = 0 then 1 else Complex.exp (((t : ℂ) * Complex.I) * ((a / 2 * Real.log x : ℝ) : ℂ))

lemma scalarPhase_norm (a x t : ℝ) : ‖scalarPhase a x t‖ = 1 := by
  by_cases hx : x = 0
  · simp [scalarPhase, hx]
  · simp [scalarPhase, hx, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

lemma scalarPhase_unitary (a x t : ℝ) : star (scalarPhase a x t) * scalarPhase a x t = 1 := by
  change (starRingEnd ℂ) (scalarPhase a x t) * scalarPhase a x t = 1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, scalarPhase_norm]
  norm_num

lemma scalarPower_right (a x : ℝ) {z : ℂ} (hz : z.re = 1) :
    scalarPower a x z = scalarPhase a x z.im * scalarPower a x 1 := by
  by_cases hx : x = 0
  · simp [scalarPower, scalarPhase, hx]
  · simp only [scalarPower, scalarPhase, hx, ↓reduceIte, one_mul, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hz] <;> ring

lemma spectralPhase_unitary {A : Matrix n n ℂ} (hA : A.IsHermitian) (a t : ℝ) :
    applyFn hA (fun x => scalarPhase a x t) ∈ unitary (Matrix n n ℂ) :=
  applyFn_unitary hA _ (fun i => scalarPhase_unitary a (hA.eigenvalues i) t)

lemma power_right {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ)
    {z : ℂ} (hz : z.re = 1) :
    applyFn hA (fun x => scalarPower a x z) =
      applyFn hA (fun x => scalarPhase a x z.im) *
      applyFn hA (fun x => scalarPower a x 1) := by
  rw [← applyFn_mul]
  congr 1
  funext x
  exact scalarPower_right a x hz

end PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

lemma applyFn_real_eq_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    applyFn hA (fun x => (f x : ℂ)) = cfc f A := by
  rw [hA.cfc_eq]
  rfl

lemma applyFn_complex_parts {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    applyFn hA f = applyFn hA (fun x => (f x).re) +
      Complex.I • applyFn hA (fun x => (f x).im) := by
  unfold applyFn
  rw [← map_smul, ← map_add, ← Matrix.diagonal_smul, Matrix.diagonal_add]
  congr 2
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (Complex.re_add_im (f (hA.eigenvalues i))).symm.trans (by ring)

lemma continuousOn_quasispectrum {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : ContinuousOn f (quasispectrum ℝ A) := by
  rw [quasispectrum_eq_spectrum_union_zero, hA.spectrum_real_eq_range_eigenvalues]
  exact ((Set.finite_range hA.eigenvalues).union (Set.finite_singleton 0)).continuousOn f

lemma applyFn_map {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (φ : Matrix n n ℂ →⋆ₙₐ[ℂ] Matrix k k ℂ) (f : ℝ → ℂ) (hf0 : f 0 = 0) :
    φ (applyFn hA f) = applyFn (hA.isSelfAdjoint.map φ).isHermitian f := by
  have hreal (g : ℝ → ℝ) (hg0 : g 0 = 0) :
      φ (applyFn hA (fun x => (g x : ℂ))) =
        applyFn (hA.isSelfAdjoint.map φ).isHermitian (fun x => (g x : ℂ)) := by
    rw [applyFn_real_eq_cfc, applyFn_real_eq_cfc,
      ← cfcₙ_eq_cfc (continuousOn_quasispectrum hA g) hg0,
      ← cfcₙ_eq_cfc (continuousOn_quasispectrum (hA.isSelfAdjoint.map φ).isHermitian g) hg0]
    let φL : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ :=
      { toFun := φ, map_add' := map_add φ, map_smul' := map_smul φ }
    exact φ.map_cfcₙ g A (continuousOn_quasispectrum hA g) hg0
      φL.continuous_of_finiteDimensional hA.isSelfAdjoint (hA.isSelfAdjoint.map φ)
  rw [applyFn_complex_parts hA f, applyFn_complex_parts _ f, map_add, map_smul]
  rw [hreal (fun x => (f x).re) (by simp [hf0]),
      hreal (fun x => (f x).im) (by simp [hf0])]

lemma power_zero_mul_self {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ) :
    applyFn hA (fun x => scalarPower a x 0) * A = A := by
  conv_lhs => arg 2; rw [← applyFn_id hA]
  rw [← applyFn_mul]
  have he : (fun x : ℝ => scalarPower a x 0 * (x : ℂ)) = (fun x : ℝ => (x : ℂ)) := by
    funext x
    by_cases hx : x = 0 <;> simp [scalarPower, hx]
  rw [he, applyFn_id]

lemma power_zero_hermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ) :
    (applyFn hA (fun x => scalarPower a x 0)).IsHermitian := by
  change star (applyFn hA (fun x => scalarPower a x 0)) = _
  rw [← applyFn_star]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [scalarPower, hx]

lemma power_zero_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ) :
    applyFn hA (fun x => scalarPower a x 0) *
      applyFn hA (fun x => scalarPower a x 0) =
      applyFn hA (fun x => scalarPower a x 0) := by
  rw [← applyFn_mul]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [scalarPower, hx]

lemma power_mul_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ) (z : ℂ) :
    applyFn hA (fun x => scalarPower a x z) *
      applyFn hA (fun x => scalarPower a x 0) =
      applyFn hA (fun x => scalarPower a x z) := by
  rw [← applyFn_mul]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [scalarPower, hx]

lemma deriv_mul_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ) :
    applyFn hA (fun x => ((a / 2 * Real.log x : ℝ) : ℂ)) *
      applyFn hA (fun x => scalarPower a x 0) =
      applyFn hA (fun x => ((a / 2 * Real.log x : ℝ) : ℂ)) := by
  rw [← applyFn_mul]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [scalarPower, hx]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

def eigenProjector {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i 1))

lemma eigenProjector_positive {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    (eigenProjector hA i).PosSemidef := by
  have hd : (Matrix.diagonal (Pi.single i (1 : ℂ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (by
      intro j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num)
  exact hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix n n ℂ)

lemma eigenProjector_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    eigenProjector hA i * eigenProjector hA i = eigenProjector hA i := by
  rw [eigenProjector, ← map_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  funext j
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

lemma eigenProjector_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    (eigenProjector hA i).trace = 1 := by
  rw [eigenProjector, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← mul_assoc, hA.eigenvectorUnitary.property.1, one_mul, Matrix.trace_diagonal]
  simp

lemma eigenProjector_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∑ i, eigenProjector hA i = 1 := by
  have hs : (∑ i : n, Matrix.diagonal (Pi.single i (1 : ℂ))) = 1 := by
    ext j k
    by_cases h : j = k
    · subst k
      simp [Matrix.sum_apply, Pi.single_apply]
    · simp [Matrix.sum_apply, h]
  unfold eigenProjector
  rw [← map_sum, hs, map_one]

lemma eigenProjector_mul_self {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    eigenProjector hA i * A = (hA.eigenvalues i : ℂ) • eigenProjector hA i := by
  conv_lhs => arg 2; rw [← applyFn_id hA]
  unfold eigenProjector applyFn
  rw [← map_mul, ← map_smul, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 2
  ext j
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with h
  · subst j; simp
  · simp

lemma eigenProjector_norm {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    ‖eigenProjector hA i‖ ≤ 1 := by
  rw [eigenProjector, StarAlgEquiv.norm_map]
  rw [Matrix.l2_opNorm_diagonal]
  apply pi_norm_le_iff_of_nonneg zero_le_one |>.mpr
  intro j
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

end PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral

end

end OAI
