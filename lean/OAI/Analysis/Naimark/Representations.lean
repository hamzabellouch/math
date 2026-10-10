import OAI.Analysis.Naimark.States

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexStarModule InnerProductSpace
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_commutant_scalar
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hcomm : ∀ a : A, Commute T (π a)) :
    ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  have hstar (a : A) : Commute (star T) (π a) := by
    change star T * π a = π a * star T
    have hh := congrArg star (hcomm (star a)).eq
    simpa only [star_mul, ← map_star, star_star] using hh.symm
  have hr (a : A) : Commute (realPart T : H →L[ℂ] H) (π a) := by
    rw [realPart_apply_coe]
    exact ((hcomm a).add_left (hstar a)).smul_left _
  have hi (a : A) : Commute (imaginaryPart T : H →L[ℂ] H) (π a) := by
    rw [imaginaryPart_apply_coe]
    exact (((hcomm a).sub_left (hstar a)).smul_left _).smul_left _
  obtain ⟨r, hr⟩ := irreducible_commutant_selfAdjoint_scalar π hπ
    (realPart T) (realPart T).property hr
  obtain ⟨s, hs⟩ := irreducible_commutant_selfAdjoint_scalar π hπ
    (imaginaryPart T) (imaginaryPart T).property hi
  refine ⟨r + Complex.I * s, ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart T, hr, hs]
  simp only [← Complex.coe_smul, smul_smul, add_smul]

theorem inner_realPart_operator (T : H →L[ℂ] H) (x y : H) :
    2 * (⟪y, (realPart T : H →L[ℂ] H) x⟫_ℂ).re =
      (⟪y, T x⟫_ℂ).re + (⟪T y, x⟫_ℂ).re := by
  simp only [realPart_apply_coe, smul_apply, add_apply, ← Complex.coe_smul,
    inner_smul_right, inner_add_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

variable {ι : Type*} [Fintype ι]

def diagonalOperator (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap (fun _ : ι => T)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).toContinuousLinearMap)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_apply (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) : diagonalOperator T x i = T (x i) := rfl

def diagonalHom : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) where
  toFun := diagonalOperator
  map_one' := by ext x i; rfl
  map_mul' T S := by ext x i; rfl
  map_zero' := by ext x i; rfl
  map_add' T S := by ext x i; rfl
  commutes' z := by ext x i; rfl
  map_star' T := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change ⟪y, diagonalOperator (ContinuousLinearMap.adjoint T) x⟫_ℂ =
      ⟪y, (ContinuousLinearMap.adjoint (diagonalOperator T)) x⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [PiLp.inner_apply, diagonalOperator_apply,
      ContinuousLinearMap.adjoint_inner_right]

def diagonalRepresentation (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₙₐ[ℂ] (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :=
  diagonalHom.toNonUnitalStarAlgHom.comp π

def coordinateInclusion [DecidableEq ι] (i : ι) :
    H →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem coordinateInclusion_apply [DecidableEq ι] (i : ι) (x : H) :
    coordinateInclusion i x = PiLp.single 2 i x := rfl

omit [CompleteSpace H] in

theorem sum_coordinateInclusion [DecidableEq ι] (x : PiLp 2 (fun _ : ι => H)) :
    ∑ i, coordinateInclusion i (x i) = x := by
  ext j
  simp [coordinateInclusion_apply]

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_coordinateInclusion [DecidableEq ι]
    (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonalOperator T (coordinateInclusion i x) = coordinateInclusion i (T x) := by
  ext j
  simp only [diagonalOperator_apply, coordinateInclusion_apply, PiLp.single_apply]
  split_ifs <;> simp

def amplificationBlock [DecidableEq ι]
    (P : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (P.comp (coordinateInclusion j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem amplificationBlock_apply [DecidableEq ι]
    (P : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) (i j : ι) (x : H) :
    amplificationBlock P i j x = P (coordinateInclusion j x) i := rfl

omit [CompleteSpace H] in
theorem amplificationBlock_sum [DecidableEq ι]
    (P : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) :
    P x i = ∑ j, amplificationBlock P i j (x j) := by
  have hh := congrArg (fun z : PiLp 2 (fun _ : ι => H) => (P z) i)
    (sum_coordinateInclusion x)
  simpa only [map_sum, amplificationBlock_apply, WithLp.ofLp_sum, Finset.sum_apply] using hh.symm

theorem amplified_commutant_commute
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (P : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (hP : ∀ a, Commute P (diagonalOperator (π a))) (T : H →L[ℂ] H) :
    Commute P (diagonalOperator T) := by
  classical
  have hc (i j : ι) (a : A) : Commute (amplificationBlock P i j) (π a) := by
    change amplificationBlock P i j * π a = π a * amplificationBlock P i j
    ext x
    have hh := congrArg (fun Q : PiLp 2 (fun _ : ι => H) →L[ℂ]
        PiLp 2 (fun _ : ι => H) => Q (coordinateInclusion j x) i) (hP a).eq
    simpa only [mul_apply_eq_comp, diagonalOperator_coordinateInclusion,
      diagonalOperator_apply, amplificationBlock_apply] using hh
  have hs (i j : ι) := irreducible_commutant_scalar π hπ
    (amplificationBlock P i j) (hc i j)
  change P * diagonalOperator T = diagonalOperator T * P
  ext x i
  simp only [mul_apply_eq_comp, diagonalOperator_apply]
  rw [amplificationBlock_sum P _ i, amplificationBlock_sum P x i, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨z, hz⟩ := hs i j
  simp only [diagonalOperator_apply, hz, smul_apply, one_apply_eq_self, map_smul]

theorem irreducible_finite_strong_density
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : PiLp 2 (fun _ : ι => H)) (T : H →L[ℂ] H) :
    diagonalOperator T x ∈ closure (Set.range fun a : A => diagonalOperator (π a) x) := by
  let ρ : A →⋆ₙₐ[ℂ] (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :=
    diagonalRepresentation π
  let M := (orbitMap ρ x).range
  have hm (a : A) : M.map (ρ a).toLinearMap ≤ M := by
    rintro _ ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨a * b, ?_⟩
    simp [orbitMap, map_mul, mul_apply_eq_comp]
  have hinv (a : A) (y : PiLp 2 (fun _ : ι => H)) (hy : y ∈ M.topologicalClosure) :
      ρ a y ∈ M.topologicalClosure := by
    apply Submodule.topologicalClosure_mono (hm a)
    apply Submodule.topologicalClosure_map (ρ a) M
    exact ⟨y, hy, rfl⟩
  let : IsClosed (M.topologicalClosure : Set (PiLp 2 (fun _ : ι => H))) :=
    M.isClosed_topologicalClosure
  have hx : x ∈ M.topologicalClosure := by
    apply M.le_topologicalClosure
    refine ⟨1, ?_⟩
    change diagonalOperator (π 1) x = x
    rw [irreducible_map_one π hπ]
    ext i
    rfl
  have hc (a : A) : Commute M.topologicalClosure.starProjection (diagonalOperator (π a)) := by
    change M.topologicalClosure.starProjection * ρ a = ρ a * M.topologicalClosure.starProjection
    apply ContinuousLinearMap.ext
    intro y
    exact invariant_starProjection_commute ρ M.topologicalClosure hinv a y
  have hp := amplified_commutant_commute π hπ M.topologicalClosure.starProjection hc T
  have he := congrArg (fun Q : PiLp 2 (fun _ : ι => H) →L[ℂ]
    PiLp 2 (fun _ : ι => H) => Q x) hp.eq
  simp only [mul_apply_eq_comp, Submodule.starProjection_eq_self_iff.mpr hx] at he
  show diagonalOperator T x ∈ M.topologicalClosure
  rw [← he]
  exact M.topologicalClosure.starProjection_apply_mem _

theorem irreducible_selfAdjoint_strong_density
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : PiLp 2 (fun _ : ι => H)) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    diagonalOperator T x ∈ closure
      ((fun a : A => diagonalOperator (π a) x) '' {a | IsSelfAdjoint a}) := by
  classical
  let D := PiLp 2 (fun _ : ι => H)
  let : InnerProductSpace ℝ D := InnerProductSpace.rclikeToReal ℂ D
  let ρ : A →⋆ₙₐ[ℂ] (D →L[ℂ] D) := diagonalRepresentation π
  let L : A →ₗ[ℝ] D := (orbitMap ρ x).restrictScalars ℝ
  let M : Submodule ℝ D := (selfAdjoint.submodule ℝ A).map L
  show diagonalOperator T x ∈ M.topologicalClosure
  rw [← M.orthogonal_orthogonal_eq_closure]
  apply (Mᗮ.mem_orthogonal' _).mpr
  intro y hy
  have hz (a : A) : (⟪y, diagonalOperator (π (realPart a : A)) x⟫_ℂ).re = 0 := by
    change ⟪y, diagonalOperator (π (realPart a : A)) x⟫_ℝ = 0
    exact M.inner_left_of_mem_orthogonal
      (show diagonalOperator (π (realPart a : A)) x ∈ M from
        ⟨(realPart a : A), (realPart a).property, rfl⟩) hy
  let z : PiLp 2 (fun _ : ι ⊕ ι => H) := WithLp.toLp 2 (Sum.elim x y)
  let Φ : PiLp 2 (fun _ : ι ⊕ ι => H) → ℝ := fun w =>
    ∑ i, ((⟪y i, w (Sum.inl i)⟫_ℂ).re + (⟪w (Sum.inr i), x i⟫_ℂ).re)
  have hΦ : Continuous Φ := by
    apply continuous_finsetSum
    intro i _
    apply Continuous.add
    · exact Complex.continuous_re.comp
        ((continuous_const.inner (𝕜 := ℂ) (PiLp.continuous_apply 2 (fun _ : ι ⊕ ι => H)
          (Sum.inl i))))
    · exact Complex.continuous_re.comp
        (((PiLp.continuous_apply 2 (fun _ : ι ⊕ ι => H) (Sum.inr i)).inner
          (𝕜 := ℂ) continuous_const))
  have hΦa (a : A) : Φ (diagonalOperator (π a) z) = 0 := by
    change (∑ i, ((⟪y i, π a (x i)⟫_ℂ).re + (⟪π a (y i), x i⟫_ℂ).re)) = 0
    simp_rw [← inner_realPart_operator, ← map_realPart π a]
    rw [← Finset.mul_sum]
    have hh := hz a
    simp only [D, PiLp.inner_apply, Complex.re_sum, diagonalOperator_apply] at hh
    rw [hh, mul_zero]
  have hclosed : IsClosed {w | Φ w = 0} := isClosed_eq hΦ continuous_const
  have hΦT : Φ (diagonalOperator T z) = 0 :=
    (closure_minimal (by rintro _ ⟨a, rfl⟩; exact hΦa a) hclosed)
      (irreducible_finite_strong_density π hπ z T)
  change (⟪diagonalOperator T x, y⟫_ℂ).re = 0
  suffices hs : (⟪y, diagonalOperator T x⟫_ℂ).re = 0 by
    exact (inner_re_symm (𝕜 := ℂ) (diagonalOperator T x) y).trans hs
  have hself : (realPart T : H →L[ℂ] H) = T := hT.coe_realPart
  have he : 2 * (⟪y, diagonalOperator T x⟫_ℂ).re = 0 := by
    change (∑ i, ((⟪y i, T (x i)⟫_ℂ).re + (⟪T (y i), x i⟫_ℂ).re)) = 0 at hΦT
    have hi (i : ι) : 2 * (⟪y i, T (x i)⟫_ℂ).re =
        (⟪y i, T (x i)⟫_ℂ).re + (⟪T (y i), x i⟫_ℂ).re := by
      simpa only [hself] using inner_realPart_operator T (x i) (y i)
    simp_rw [← hi] at hΦT
    simpa only [D, PiLp.inner_apply, Complex.re_sum, diagonalOperator_apply,
      Finset.mul_sum] using hΦT
  linarith

open scoped ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

def saResolvent (a : A) (z : ℂ) : A := cfc (fun t : ℂ => (t - z)⁻¹) a

theorem sa_spectrum_sub_ne_zero (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) (t : ℂ) (ht : t ∈ spectrum ℂ a) : t - z ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  exact hz (he ▸ ha.im_eq_zero_of_mem_spectrum ht)

theorem saResolvent_continuousOn (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousOn (fun t : ℂ => (t - z)⁻¹) (spectrum ℂ a) :=
  (continuous_id.sub continuous_const).continuousOn.inv₀ (sa_spectrum_sub_ne_zero a ha z hz)

theorem saResolvent_inverse (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) :
    (a - algebraMap ℂ A z) * saResolvent a z = 1 ∧
    saResolvent a z * (a - algebraMap ℂ A z) = 1 := by
  let u := cfcUnits (fun t : ℂ => t - z) a (sa_spectrum_sub_ne_zero a ha z hz)
    (continuous_id.sub continuous_const).continuousOn ha.isStarNormal
  have hu : (u : A) = a - algebraMap ℂ A z := by
    change cfc (fun t : ℂ => t - z) a = a - algebraMap ℂ A z
    rw [cfc_sub (fun t : ℂ => t) (fun _ : ℂ => z) a (continuous_id.continuousOn) (continuous_const.continuousOn), cfc_id' ℂ a ha.isStarNormal, cfc_const z a ha.isStarNormal]
  have hv : (↑u⁻¹ : A) = saResolvent a z := rfl
  constructor
  · rw [← hu, ← hv]; exact u.val_inv
  · rw [← hu, ← hv]; exact u.inv_val

theorem saResolvent_norm_le (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) : ‖saResolvent a z‖ ≤ |z.im|⁻¹ := by
  apply norm_cfc_le (inv_nonneg.mpr (abs_nonneg _))
  intro t ht
  rw [norm_inv]
  rw [← one_div, ← one_div]
  apply one_div_le_one_div_of_le (abs_pos.mpr hz)
  have hh := Complex.abs_im_le_norm (t - z)
  simpa only [Complex.sub_im, ha.im_eq_zero_of_mem_spectrum ht, zero_sub, abs_neg] using hh

theorem saResolvent_star (a : A) (ha : IsSelfAdjoint a) (z : ℂ) :
    star (saResolvent a z) = saResolvent a (star z) := by
  rw [saResolvent, ← cfc_star]
  apply cfc_congr
  intro t ht
  have ht' : star t = t := by
    rw [ha.mem_spectrum_eq_re ht]
    simp
  simp only [star_inv₀, star_sub, ht']

def saBoundedTransform (a : A) : A := saResolvent a Complex.I + saResolvent a (-Complex.I)

theorem saBoundedTransform_selfAdjoint (a : A) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (saBoundedTransform a) := by
  change star (saBoundedTransform a) = saBoundedTransform a
  simp only [saBoundedTransform, star_add, saResolvent_star a ha, star_neg,
    Complex.star_def, Complex.conj_I, neg_neg, add_comm]

theorem saBoundedTransform_norm_le (a : A) (ha : IsSelfAdjoint a) :
    ‖saBoundedTransform a‖ ≤ 2 := by
  have hp := saResolvent_norm_le a ha Complex.I (by simp)
  have hm := saResolvent_norm_le a ha (-Complex.I) (by simp)
  simp only [Complex.I_im, Complex.neg_im, abs_neg, abs_one, inv_one] at hp hm
  exact (norm_add_le _ _).trans (by linarith)

theorem resolvent_sum_real (t : ℝ) :
    ((t : ℂ) - Complex.I)⁻¹ + ((t : ℂ) - (-Complex.I))⁻¹ =
      (2 * t / (1 + t ^ 2) : ℝ) := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      zero_sub, sub_zero, neg_zero, neg_neg] <;> ring

theorem saBoundedTransform_eq_cfc (a : A) (ha : IsSelfAdjoint a) :
    saBoundedTransform a = cfc (fun t : ℝ => 2 * t / (1 + t ^ 2)) a := by
  rw [cfc_real_eq_complex _ ha]
  rw [saBoundedTransform, saResolvent, saResolvent, ← cfc_add (a := a) _ _
    (saResolvent_continuousOn a ha Complex.I (by simp))
    (saResolvent_continuousOn a ha (-Complex.I) (by simp))]
  apply cfc_congr
  intro t ht
  rw [ha.mem_spectrum_eq_re ht]
  simpa only [Complex.ofReal_re] using resolvent_sum_real t.re

def rationalPreimage (t : ℝ) : ℝ := t / (1 + Real.sqrt (1 - t ^ 2))

theorem rationalPreimage_continuous : Continuous rationalPreimage := by
  change Continuous (fun t : ℝ => t / (1 + Real.sqrt (1 - t ^ 2)))
  exact continuous_id.div
    (continuous_const.add ((continuous_const.sub (continuous_id.pow 2)).sqrt))
    (fun t => ne_of_gt (show 0 < 1 + Real.sqrt (1 - t ^ 2) by positivity))

theorem rationalPreimage_rightInverse (t : ℝ) (ht : |t| ≤ 1) :
    2 * rationalPreimage t / (1 + rationalPreimage t ^ 2) = t := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
  have hs := Real.sq_sqrt (show 0 ≤ 1 - t ^ 2 by linarith)
  have hp : 0 < 1 + Real.sqrt (1 - t ^ 2) := by positivity
  have hd : 0 < 1 + rationalPreimage t ^ 2 := by positivity
  apply (div_eq_iff (ne_of_gt hd)).mpr
  dsimp [rationalPreimage]
  field_simp
  linear_combination -t * hs

theorem saBoundedTransform_preimage (a : A) (ha : IsSelfAdjoint a) (hn : ‖a‖ ≤ 1) :
    ∃ b : A, IsSelfAdjoint b ∧ saBoundedTransform b = a := by
  let b : A := cfc rationalPreimage a
  have hb : IsSelfAdjoint b := cfc_predicate _ _
  refine ⟨b, hb, ?_⟩
  rw [saBoundedTransform_eq_cfc b hb]
  change cfc (fun t : ℝ => 2 * t / (1 + t ^ 2)) (cfc rationalPreimage a) = a
  have hf : Continuous (fun t : ℝ => 2 * t / (1 + t ^ 2)) :=
    (continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2)) (fun t => ne_of_gt (by positivity))
  rw [← cfc_comp' (fun t : ℝ => 2 * t / (1 + t ^ 2)) rationalPreimage a
    (hf := rationalPreimage_continuous.continuousOn) (hg := hf.continuousOn)]
  calc
    _ = cfc (fun t : ℝ => t) a := by
      apply cfc_congr
      intro t ht
      have ht' : |t| ≤ ‖a‖ := by
        simpa only [Real.norm_eq_abs, mul_one] using
          (spectrum.norm_le_norm_mul_of_mem ht).trans
            (mul_le_mul_of_nonneg_left ((IsStarProjection.one A).norm_le _) (norm_nonneg a))
      exact rationalPreimage_rightInverse t (ht'.trans hn)
    _ = a := cfc_id' ℝ a ha

theorem saResolvent_sub (a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (z : ℂ) (hz : z.im ≠ 0) :
    saResolvent a z - saResolvent b z =
      saResolvent a z * (b - a) * saResolvent b z := by
  have ha' := (saResolvent_inverse a ha z hz).2
  have hb' := (saResolvent_inverse b hb z hz).1
  symm
  calc
    _ = saResolvent a z * ((b - algebraMap ℂ A z) - (a - algebraMap ℂ A z)) *
        saResolvent b z := by congr 2; abel
    _ = saResolvent a z * ((b - algebraMap ℂ A z) * saResolvent b z) -
        (saResolvent a z * (a - algebraMap ℂ A z)) * saResolvent b z := by noncomm_ring
    _ = _ := by rw [ha', hb']; simp

theorem map_saBoundedTransform {B : Type*} [CStarAlgebra B] (π : A →⋆ₐ[ℂ] B)
    (a : A) (ha : IsSelfAdjoint a) :
    π (saBoundedTransform a) = saBoundedTransform (π a) := by
  simp only [saBoundedTransform, map_add, saResolvent]
  rw [π.map_cfc _ _ (saResolvent_continuousOn a ha Complex.I (by simp))
      (hφ := map_continuous π) (ha := ha.isStarNormal) (hφa := (ha.map π).isStarNormal),
    π.map_cfc _ _ (saResolvent_continuousOn a ha (-Complex.I) (by simp))
      (hφ := map_continuous π) (ha := ha.isStarNormal) (hφa := (ha.map π).isStarNormal)]

theorem saResolvent_eval_sub_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a b : H →L[ℂ] H) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    ‖(saResolvent a z - saResolvent b z) x‖ ≤
      |z.im|⁻¹ * ‖(b - a) (saResolvent b z x)‖ := by
  rw [saResolvent_sub a b ha hb z hz]
  simpa only [mul_apply_eq_comp] using
    ((saResolvent a z).le_opNorm ((b - a) (saResolvent b z x))).trans
      (mul_le_mul_of_nonneg_right (saResolvent_norm_le a ha z hz) (norm_nonneg _))

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def irreducibleUnitalRepresentation
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) : A →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := π
  map_one' := irreducible_map_one π hπ
  map_zero' := map_zero π
  map_add' := map_add π
  map_mul' := map_mul π
  map_star' := map_star π
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, irreducible_map_one π hπ,
      Algebra.algebraMap_eq_smul_one]

@[simp] theorem irreducibleUnitalRepresentation_apply
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (a : A) :
    irreducibleUnitalRepresentation π hπ a = π a := rfl

theorem irreducible_bounded_strong_density
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ι : Type*} [Fintype ι] (x : ι → H)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 ∧ ∀ i, ‖π a (x i) - T (x i)‖ < ε := by
  classical
  obtain ⟨S, hS, hST⟩ := saBoundedTransform_preimage T hT hn
  let y : PiLp 2 (fun _ : Sum ι ι => H) := WithLp.toLp 2 (Sum.elim
    (fun i => saResolvent S Complex.I (x i))
    (fun i => saResolvent S (-Complex.I) (x i)))
  have hd := irreducible_selfAdjoint_strong_density π hπ y S hS
  obtain ⟨v, ⟨a, ha, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp hd (ε / 2) (half_pos hε)
  have hv' : ‖diagonalOperator S y - diagonalOperator (π a) y‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hv
  have hc (i : Sum ι ι) : ‖(S - π a) (y i)‖ < ε / 2 := by
    have hh := (PiLp.norm_apply_le (diagonalOperator S y - diagonalOperator (π a) y) i).trans_lt hv'
    simpa only [WithLp.ofLp_sub, Pi.sub_apply, diagonalOperator_apply, sub_apply] using hh
  refine ⟨saBoundedTransform a, saBoundedTransform_selfAdjoint a ha,
    saBoundedTransform_norm_le a ha, ?_⟩
  intro i
  have hp := (saResolvent_eval_sub_le (π a) S (ha.map π) hS Complex.I (by simp) (x i)).trans_lt
    (show |Complex.I.im|⁻¹ * ‖(S - π a) (saResolvent S Complex.I (x i))‖ < ε / 2 by
      simpa [y] using hc (Sum.inl i))
  have hm := (saResolvent_eval_sub_le (π a) S (ha.map π) hS (-Complex.I) (by simp) (x i)).trans_lt
    (show |(-Complex.I).im|⁻¹ * ‖(S - π a) (saResolvent S (-Complex.I) (x i))‖ < ε / 2 by
      simpa [y] using hc (Sum.inr i))
  change ‖irreducibleUnitalRepresentation π hπ (saBoundedTransform a) (x i) - T (x i)‖ < ε
  rw [map_saBoundedTransform _ a ha, ← hST]
  change ‖(saResolvent (π a) Complex.I (x i) + saResolvent (π a) (-Complex.I) (x i)) -
    (saResolvent S Complex.I (x i) + saResolvent S (-Complex.I) (x i))‖ < ε
  rw [show (saResolvent (π a) Complex.I (x i) + saResolvent (π a) (-Complex.I) (x i)) -
      (saResolvent S Complex.I (x i) + saResolvent S (-Complex.I) (x i)) =
      ((saResolvent (π a) Complex.I - saResolvent S Complex.I) (x i)) +
      ((saResolvent (π a) (-Complex.I) - saResolvent S (-Complex.I)) (x i)) by
        simp only [sub_apply]; abel]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem irreducible_bounded_strong_density_scaled
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ι : Type*} [Fintype ι] (x : ι → H)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * ‖T‖ ∧
      ∀ i, ‖π a (x i) - T (x i)‖ < ε := by
  by_cases h0 : T = 0
  · subst T
    refine ⟨0, IsSelfAdjoint.zero _, by simp, ?_⟩
    intro i
    simpa using hε
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr h0
  let S : H →L[ℂ] H := (‖T‖⁻¹ : ℝ) • T
  have hS : IsSelfAdjoint S := (IsSelfAdjoint.all (‖T‖⁻¹ : ℝ)).smul hT
  have hSn : ‖S‖ ≤ 1 := by
    simp [S, norm_smul, inv_mul_cancel₀ (ne_of_gt hn)]
  obtain ⟨a, ha, hab, hap⟩ := irreducible_bounded_strong_density π hπ x S hS hSn
    (ε / ‖T‖) (div_pos hε hn)
  refine ⟨(‖T‖ : ℝ) • a, (IsSelfAdjoint.all (‖T‖ : ℝ)).smul ha, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hn]
    nlinarith
  · intro i
    have he : T = (‖T‖ : ℝ) • S := by
      dsimp [S]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
    have hmap : π ((‖T‖ : ℝ) • a) = (‖T‖ : ℝ) • π a := by
      rw [← Complex.coe_smul, map_smul, Complex.coe_smul]
    rw [hmap]
    nth_rw 2 [he]
    rw [smul_apply, smul_apply, ← smul_sub]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hn]
    have hh := mul_lt_mul_of_pos_left (hap i) hn
    simpa only [mul_div_cancel₀ _ (ne_of_gt hn)] using hh

open scoped InnerProductSpace ComplexStarModule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def symmetricCompression (P T : H →L[ℂ] H) : H →L[ℂ] H := T * P + P * T - P * T * P

theorem symmetricCompression_selfAdjoint (P T : H →L[ℂ] H)
    (hP : IsSelfAdjoint P) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (symmetricCompression P T) := by
  change star (symmetricCompression P T) = symmetricCompression P T
  simp only [symmetricCompression, star_sub, star_add, star_mul, hP.star_eq, hT.star_eq]
  noncomm_ring

omit [CompleteSpace H] in
theorem symmetricCompression_mul_projection (P T : H →L[ℂ] H)
    (hP : IsIdempotentElem P) : symmetricCompression P T * P = T * P := by
  have hPP : P * P = P := hP
  simp only [symmetricCompression, add_mul, sub_mul, mul_assoc, hPP]
  abel

theorem symmetricCompression_norm_le (P T : H →L[ℂ] H)
    (hP : IsSelfAdjoint P) (hT : IsSelfAdjoint T) (hn : ‖P‖ ≤ 1) :
    ‖symmetricCompression P T‖ ≤ 3 * ‖T * P‖ := by
  have h : ‖P * T‖ = ‖T * P‖ := by
    rw [← norm_star (P * T)]
    simp only [star_mul, hP.star_eq, hT.star_eq]
  have h' : ‖P * T * P‖ ≤ ‖T * P‖ := by
    calc
      _ ≤ ‖P * T‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖P * T‖ * 1 := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = ‖T * P‖ := by rw [mul_one, h]
  calc
    ‖symmetricCompression P T‖ ≤ ‖T * P + P * T‖ + ‖P * T * P‖ := norm_sub_le _ _
    _ ≤ (‖T * P‖ + ‖P * T‖) + ‖P * T * P‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 3 * ‖T * P‖ := by linarith

omit [CompleteSpace H] in

theorem norm_mul_starProjection_le_sum {M : Submodule ℂ H} [M.HasOrthogonalProjection]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ M) (T : H →L[ℂ] H) :
    ‖T * M.starProjection‖ ≤ ∑ i, ‖T (b i : H)‖ := by
  classical
  rw [b.starProjection_eq_sum_rankOne, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne,
    InnerProductSpace.norm_rankOne]
  have hb : ‖(b i : H)‖ = 1 := b.orthonormal.1 i
  rw [hb, mul_one]

omit [CompleteSpace H] in

theorem symmetricCompression_apply_of_mem {M : Submodule ℂ H} [M.HasOrthogonalProjection]
    (T : H →L[ℂ] H) {x : H} (hx : x ∈ M) :
    symmetricCompression M.starProjection T x = T x := by
  have hp := symmetricCompression_mul_projection M.starProjection T M.isIdempotentElem_starProjection
  have hh := congrArg (fun S : H →L[ℂ] H => S x) hp
  simpa only [mul_apply_eq_comp, M.starProjection_eq_self_iff.mpr hx] using hh

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_selfAdjoint_correction
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ (a : A) (S : H →L[ℂ] H), IsSelfAdjoint a ∧ IsSelfAdjoint S ∧
      ‖a‖ ≤ 2 * ‖T‖ ∧ ‖S‖ ≤ (1 / 2 : ℝ) * ‖T‖ ∧
      ∀ x ∈ M, (π a + S) x = T x := by
  classical
  by_cases h0 : T = 0
  · subst T
    refine ⟨0, 0, IsSelfAdjoint.zero _, IsSelfAdjoint.zero _, by simp, by simp, ?_⟩
    simp
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr h0
  let b := stdOrthonormalBasis ℂ M
  let n := Module.finrank ℂ M
  let ε : ℝ := ‖T‖ / (6 * (n + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨a, ha, han, hap⟩ := irreducible_bounded_strong_density_scaled π hπ
    (fun i => (b i : H)) T hT ε hε
  let S := symmetricCompression M.starProjection (T - π a)
  have hS : IsSelfAdjoint S := symmetricCompression_selfAdjoint _ _
    (isSelfAdjoint_starProjection M) (hT.sub (ha.map π))
  have hb : ‖(T - π a) * M.starProjection‖ ≤ n * ε := by
    calc
      _ ≤ ∑ i, ‖(T - π a) (b i : H)‖ := norm_mul_starProjection_le_sum b _
      _ ≤ ∑ _ : Fin n, ε := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sub_apply, norm_sub_rev] using (hap i).le
      _ = n * ε := by simp
  have hεeq : ε * (6 * (n + 1)) = ‖T‖ := by
    exact div_mul_cancel₀ _ (by positivity)
  have hnS : ‖S‖ ≤ (1 / 2 : ℝ) * ‖T‖ := by
    have hh := symmetricCompression_norm_le M.starProjection (T - π a)
      (isSelfAdjoint_starProjection M) (hT.sub (ha.map π)) M.starProjection_norm_le
    change ‖S‖ ≤ 3 * ‖(T - π a) * M.starProjection‖ at hh
    nlinarith
  refine ⟨a, S, ha, hS, han, hnS, ?_⟩
  intro x hx
  have hh := symmetricCompression_apply_of_mem (T - π a) hx
  change S x = (T - π a) x at hh
  simp only [add_apply, hh, sub_apply]
  abel

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_selfAdjoint_transitivity
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 4 * ‖T‖ ∧
      ∀ x ∈ M, π a x = T x := by
  classical
  have hc (S : selfAdjoint (H →L[ℂ] H)) :=
    irreducible_selfAdjoint_correction π hπ M S.val S.property
  choose a S ha hS han hSn heq using hc
  let r : selfAdjoint (H →L[ℂ] H) → selfAdjoint (H →L[ℂ] H) := fun t => ⟨S t, hS t⟩
  let R (n : ℕ) : selfAdjoint (H →L[ℂ] H) := r^[n] ⟨T, hT⟩
  let u (n : ℕ) : A := a (R n)
  have R0 : (R 0 : H →L[ℂ] H) = T := rfl
  have Rsucc (n : ℕ) : (R (n + 1) : H →L[ℂ] H) = S (R n) := by
    exact congrArg Subtype.val (Function.iterate_succ_apply' r n ⟨T, hT⟩)
  have hRn (n : ℕ) : ‖(R n : H →L[ℂ] H)‖ ≤ (1 / 2 : ℝ) ^ n * ‖T‖ := by
    induction n with
    | zero => simp only [R0, pow_zero, one_mul, le_rfl]
    | succ n ih =>
      rw [Rsucc]
      apply (hSn (R n)).trans
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left ih (by norm_num)
  have hun (n : ℕ) : ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (2 * ‖T‖) := by
    apply (han (R n)).trans
    calc
      2 * ‖(R n : H →L[ℂ] H)‖ ≤ 2 * ((1 / 2 : ℝ) ^ n * ‖T‖) := by gcongr; exact hRn n
      _ = _ := by ring
  have sNu : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hun
      (summable_geometric_two.mul_right (2 * ‖T‖))
  have su : Summable u := sNu.of_norm
  have hua : IsSelfAdjoint (∑' n, u n) := by
    change star (∑' n, u n) = ∑' n, u n
    rw [tsum_star]
    exact tsum_congr (fun n => (ha (R n)).star_eq)
  have hub : ‖∑' n, u n‖ ≤ 4 * ‖T‖ := by
    calc
      _ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * (2 * ‖T‖) :=
        sNu.tsum_le_tsum hun (summable_geometric_two.mul_right _)
      _ = 4 * ‖T‖ := by rw [tsum_mul_right, tsum_geometric_two]; ring
  refine ⟨∑' n, u n, hua, hub, ?_⟩
  intro x hx
  have hs (n : ℕ) : π (∑ i ∈ Finset.range n, u i) x = T x - (R n : H →L[ℂ] H) x := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, map_zero, zero_apply, R0, sub_self]
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, add_apply, ih, Rsucc]
      have hh := heq (R n) x hx
      change π (u n) x + S (R n) x = (R n : H →L[ℂ] H) x at hh
      rw [← hh]
      abel
  have hlimR : Tendsto (fun n => (R n : H →L[ℂ] H) x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hbound (n : ℕ) : ‖(R n : H →L[ℂ] H) x‖ ≤
        (1 / 2 : ℝ) ^ n * (‖T‖ * ‖x‖) := by
      calc
        _ ≤ ‖(R n : H →L[ℂ] H)‖ * ‖x‖ := (R n : H →L[ℂ] H).le_opNorm x
        _ ≤ ((1 / 2 : ℝ) ^ n * ‖T‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (hRn n) (norm_nonneg x)
        _ = _ := by ring
    apply squeeze_zero (fun n => norm_nonneg _) hbound
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)).mul_const (‖T‖ * ‖x‖)
    simpa only [zero_mul] using hh
  have hlim := ((orbitCLM π x).continuous.tendsto (∑' n, u n)).comp su.hasSum.tendsto_sum_nat
  change Tendsto (fun n => π (∑ i ∈ Finset.range n, u i) x) atTop (𝓝 (π (∑' n, u n) x)) at hlim
  simp only [hs] at hlim
  have hlim' : Tendsto (fun n => T x - (R n : H →L[ℂ] H) x) atTop (𝓝 (T x)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hlimR
  exact tendsto_nhds_unique hlim hlim'

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_operator_vector (d w : H) (hd : d ≠ 0)
    (hw : (⟪d, w⟫_ℂ).im = 0) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ T d = w := by
  let r : ℝ := ‖d‖ ^ 2
  let c : ℝ := (⟪d, w⟫_ℂ).re
  have hr : r ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  have hdd : ⟪d, d⟫_ℂ = (r : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (Complex.ofReal_pow ‖d‖ 2).symm
  have hdw : ⟪d, w⟫_ℂ = (c : ℂ) := Complex.ext rfl hw
  have hwd : ⟪w, d⟫_ℂ = (c : ℂ) := by rw [← inner_conj_symm, hdw]; simp
  let T : H →L[ℂ] H := r⁻¹ • (InnerProductSpace.rankOne ℂ w d +
    InnerProductSpace.rankOne ℂ d w - (c / r) • InnerProductSpace.rankOne ℂ d d)
  refine ⟨T, ?_, ?_⟩
  · change star T = T
    simp only [T, star_smul, star_trivial, star_sub, star_add,
      ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
    rw [add_comm]
  · simp only [T, smul_apply, sub_apply, add_apply, InnerProductSpace.rankOne_apply,
      hdd, hwd, Complex.coe_smul, smul_smul, div_mul_cancel₀ c hr,
      add_sub_cancel_right, inv_mul_cancel₀ hr, one_smul]

theorem irreducible_selfAdjoint_vector
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (d w : H) (hd : d ≠ 0) (hw : (⟪d, w⟫_ℂ).im = 0) :
    ∃ a : A, IsSelfAdjoint a ∧ π a d = w := by
  obtain ⟨T, hT, hTd⟩ := exists_selfAdjoint_operator_vector d w hd hw
  obtain ⟨a, ha, _, hM⟩ := irreducible_selfAdjoint_transitivity π hπ
    (Submodule.span ℂ {d}) T hT
  exact ⟨a, ha, (hM d (Submodule.subset_span (Set.mem_singleton d))).trans hTd⟩

def saCayley (a : A) : A :=
  cfc (fun t : ℂ => (t - (-Complex.I))⁻¹ * (t - Complex.I)) a

theorem saCayley_eq (a : A) (ha : IsSelfAdjoint a) :
    saCayley a = saResolvent a (-Complex.I) * (a - Complex.I • (1 : A)) := by
  rw [saCayley, cfc_mul _ _ a
    (saResolvent_continuousOn a ha (-Complex.I) (by simp)) (by fun_prop)]
  rw [cfc_sub _ _ a, cfc_id' ℂ a ha.isStarNormal, cfc_const Complex.I a ha.isStarNormal]
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

theorem saCayley_unitary (a : A) (ha : IsSelfAdjoint a) : saCayley a ∈ unitary A := by
  apply (cfc_unitary_iff _ a ha.isStarNormal
    ((saResolvent_continuousOn a ha (-Complex.I) (by simp)).mul
      (continuous_id.sub continuous_const).continuousOn)).mpr
  intro t ht
  change star ((t - (-Complex.I))⁻¹ * (t - Complex.I)) *
    ((t - (-Complex.I))⁻¹ * (t - Complex.I)) = 1
  have htstar : star t = t := by rw [ha.mem_spectrum_eq_re ht]; simp
  have hp := sa_spectrum_sub_ne_zero a ha Complex.I (by simp) t ht
  have hm := sa_spectrum_sub_ne_zero a ha (-Complex.I) (by simp) t ht
  simp only [star_mul, star_inv₀, star_sub, htstar, star_neg,
    Complex.star_def, Complex.conj_I, neg_neg]
  field_simp [hp, hm]

theorem irreducible_unitary_vector
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (heq : ‖ξ‖ = ‖η‖) :
    ∃ u : unitary A, π u ξ = η := by
  by_cases h : ξ = η
  · refine ⟨1, ?_⟩
    simpa only [OneMemClass.coe_one, irreducible_map_one π hπ, one_apply_eq_self] using h
  have hd : ξ - η ≠ 0 := sub_ne_zero.mpr h
  have hi : (⟪ξ - η, Complex.I • (ξ + η)⟫_ℂ).im = 0 := by
    rw [inner_smul_right, inner_sub_left, inner_add_right, inner_add_right]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
      Complex.sub_re, Complex.add_re, inner_self_eq_norm_sq_to_K]
    have hh := inner_re_symm (𝕜 := ℂ) ξ η
    change (⟪ξ, η⟫_ℂ).re = (⟪η, ξ⟫_ℂ).re at hh
    rw [hh, heq]
    ring
  obtain ⟨a, ha, hact⟩ := irreducible_selfAdjoint_vector π hπ
    (ξ - η) (Complex.I • (ξ + η)) hd hi
  have hre : π (a - Complex.I • (1 : A)) ξ =
      π (a - (-Complex.I) • (1 : A)) η := by
    simp only [map_sub, map_smul, sub_apply, smul_apply,
      irreducible_map_one π hπ, one_apply_eq_self]
    simp only [map_sub, smul_add] at hact
    rw [neg_smul]
    apply sub_eq_iff_eq_add.mpr
    rw [sub_neg_eq_add]
    have hh := sub_eq_iff_eq_add.mp hact
    rw [hh]
    abel
  refine ⟨⟨saCayley a, saCayley_unitary a ha⟩, ?_⟩
  change π (saCayley a) ξ = η
  rw [saCayley_eq a ha, map_mul, mul_apply_eq_comp, hre, ← mul_apply_eq_comp, ← map_mul]
  rw [← Algebra.algebraMap_eq_smul_one, (saResolvent_inverse a ha (-Complex.I) (by simp)).2,
    irreducible_map_one π hπ, one_apply_eq_self]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
universe u v w

variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

@[refl] theorem UnitarilyEquivalent.refl (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    UnitarilyEquivalent π π := ⟨LinearIsometryEquiv.refl ℂ H, fun _ _ => rfl⟩

@[symm] theorem UnitarilyEquivalent.symm
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    (h : UnitarilyEquivalent π ρ) : UnitarilyEquivalent ρ π := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun a y => ?_⟩
  apply U.injective
  simpa only [U.apply_symm_apply] using (hU a (U.symm y)).symm

@[trans] theorem UnitarilyEquivalent.trans
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    {σ : A →⋆ₙₐ[ℂ] (L →L[ℂ] L)}
    (h : UnitarilyEquivalent π ρ) (k : UnitarilyEquivalent ρ σ) :
    UnitarilyEquivalent π σ := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨V, hV⟩ := k
  exact ⟨U.trans V, fun a x => by simp only [LinearIsometryEquiv.trans_apply, hU, hV]⟩

variable [PartialOrder A] [StarOrderedRing A]

theorem cyclic_representation_equivalent (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hc : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ)
    (hd : DenseRange (fun a : A => π a ξ)) :
    UnitarilyEquivalent f.gnsNonUnitalStarAlgHom π :=
  ⟨cyclicGNSEquiv f π ξ hc hd, cyclicGNSEquiv_intertwines f π ξ hc hd⟩

theorem irreducible_equivalent_of_coefficients
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (ξ : H) (η : K) (hξ : ξ ≠ 0) (hη : η ≠ 0)
    (hc : ∀ a : A, ⟪ξ, π a ξ⟫_ℂ = ⟪η, ρ a η⟫_ℂ) :
    UnitarilyEquivalent π ρ := by
  let f : A →ₚ[ℂ] ℂ := positiveOfSquares (vectorFunctional π ξ)
    (fun a => by
      rw [vectorFunctional_square, ← Complex.ofReal_pow]
      exact ⟨rfl, sq_nonneg _⟩)
  have hfc (a : A) : f a = ⟪ξ, π a ξ⟫_ℂ := rfl
  exact (cyclic_representation_equivalent f π ξ hfc
    (irreducible_vector_cyclic π hπ ξ hξ)).symm.trans
    (cyclic_representation_equivalent f ρ η (fun a => (hfc a).trans (hc a))
      (irreducible_vector_cyclic ρ hρ η hη))

omit [PartialOrder A] [StarOrderedRing A] in

theorem equivalent_vector_states_unitary
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (he : UnitarilyEquivalent π ρ) (ξ : H) (η : K)
    (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) :
    ∃ u : unitary A, ∀ a : A,
      ⟪η, ρ a η⟫_ℂ = ⟪ξ, π (star (u : A) * a * (u : A)) ξ⟫_ℂ := by
  obtain ⟨U, hU⟩ := he
  obtain ⟨u, hu⟩ := irreducible_unitary_vector π hπ ξ (U.symm η)
    (by rw [hξ, U.symm.norm_map, hη])
  refine ⟨u, fun a => ?_⟩
  calc
    ⟪η, ρ a η⟫_ℂ = ⟪U (π u ξ), ρ a (U (π u ξ))⟫_ℂ := by rw [hu, U.apply_symm_apply]
    _ = ⟪U (π u ξ), U (π a (π u ξ))⟫_ℂ :=
      congrArg (fun z => ⟪U (π u ξ), z⟫_ℂ) (hU a (π u ξ)).symm
    _ = ⟪π u ξ, π a (π u ξ)⟫_ℂ := U.inner_map_map _ _
    _ = _ := by
      simp only [map_mul, map_star, mul_apply_eq_comp,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_adjoint_transitivity
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M] (T : H →L[ℂ] H) :
    ∃ a : A, ‖a‖ ≤ 8 * ‖T‖ ∧ ∀ x ∈ M,
      π a x = T x ∧ π (star a) x = star T x := by
  obtain ⟨b, hb, hbn, hbM⟩ := irreducible_selfAdjoint_transitivity π hπ M
    (realPart T) (realPart T).property
  obtain ⟨c, hc, hcn, hcM⟩ := irreducible_selfAdjoint_transitivity π hπ M
    (imaginaryPart T) (imaginaryPart T).property
  refine ⟨b + Complex.I • c, ?_, ?_⟩
  · have hbr := realPart.norm_le T
    have hci := imaginaryPart.norm_le T
    calc
      _ ≤ ‖b‖ + ‖Complex.I • c‖ := norm_add_le _ _
      _ = ‖b‖ + ‖c‖ := by rw [norm_smul, Complex.norm_I, one_mul]
      _ ≤ 8 * ‖T‖ := by
        change ‖(realPart T : H →L[ℂ] H)‖ ≤ ‖T‖ at hbr
        change ‖(imaginaryPart T : H →L[ℂ] H)‖ ≤ ‖T‖ at hci
        linarith
  · intro x hx
    constructor
    · rw [map_add, map_smul, add_apply, smul_apply, hbM x hx, hcM x hx]
      exact congrArg (fun S : H →L[ℂ] H => S x) (realPart_add_I_smul_imaginaryPart T)
    · simp only [star_add, star_smul, hb.star_eq, hc.star_eq, Complex.star_def,
        Complex.conj_I, map_add, map_smul, add_apply, smul_apply, hbM x hx, hcM x hx]
      have hh := congrArg star (realPart_add_I_smul_imaginaryPart T)
      simp only [star_add, star_smul, (realPart T).property.star_eq,
        (imaginaryPart T).property.star_eq, Complex.star_def, Complex.conj_I] at hh
      exact congrArg (fun S : H →L[ℂ] H => S x) hh

theorem irreducible_null_decomposition
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) (a : A) (ha : ⟪ξ, π a ξ⟫_ℂ = 0) :
    ∃ b c : A, π b ξ = 0 ∧ π c ξ = 0 ∧ a = b + star c := by
  let T := InnerProductSpace.rankOne ℂ ξ (π a ξ)
  obtain ⟨c, _, hc⟩ := irreducible_adjoint_transitivity π hπ
    (Submodule.span ℂ {ξ}) T
  have hξM : ξ ∈ Submodule.span ℂ {ξ} := Submodule.subset_span (Set.mem_singleton ξ)
  have hc0 : π c ξ = 0 := by
    rw [(hc ξ hξM).1]
    simp [T, InnerProductSpace.rankOne_apply, inner_eq_zero_symm.mp ha]
  have hcstar : π (star c) ξ = π a ξ := by
    rw [(hc ξ hξM).2]
    simp [T, ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
      InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hξ]
  refine ⟨a - star c, c, ?_, hc0, (sub_add_cancel _ _).symm⟩
  rw [map_sub, sub_apply, hcstar, sub_self]

open scoped CStarAlgebra InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorNullAlgebra (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a | π a ξ = 0 ∧ π (star a) ξ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    simp [map_add, add_apply, star_add, ha, hb, ha', hb']
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    simp [map_mul, mul_apply_eq_comp, star_mul, hb, ha']
  smul_mem' := by
    rintro z a ⟨ha, ha'⟩
    simp [map_smul, smul_apply, star_smul, ha, ha']
  star_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa only [star_star] using ha⟩

instance vectorNullAlgebra_closed (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    IsClosed (vectorNullAlgebra π ξ : Set A) := by
  have hp : Continuous (fun a : A => π a ξ) :=
    (ContinuousLinearMap.apply ℂ H ξ).continuous.comp (map_continuous π)
  exact (isClosed_eq hp continuous_const).inter
    (isClosed_eq (hp.comp continuous_star) continuous_const)

instance (priority := 1100) vectorNullAlgebra_order (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    PartialOrder (vectorNullAlgebra π ξ) := CStarAlgebra.spectralOrder _

instance (priority := 1100) vectorNullAlgebra_starOrdered (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    StarOrderedRing (vectorNullAlgebra π ξ) := CStarAlgebra.spectralOrderedRing _

theorem star_mul_self_mem_vectorNullAlgebra (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) {a : A} (ha : π a ξ = 0) : star a * a ∈ vectorNullAlgebra π ξ := by
  constructor <;> simp [map_mul, star_mul, mul_apply_eq_comp, ha]

variable [PartialOrder A] [StarOrderedRing A]

lemma vectorNullAlgebra_coe_nonneg
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e : vectorNullAlgebra π ξ)
    (he : @LE.le _ (vectorNullAlgebra_order π ξ).toLE 0 e) : 0 ≤ (e : A) := by
  obtain ⟨v, hv⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self
    (A := vectorNullAlgebra π ξ)).mp he
  have hh := congrArg (fun b : vectorNullAlgebra π ξ => (b : A)) hv
  change (e : A) = star (v : A) * (v : A) at hh
  rw [hh]
  exact star_mul_self_nonneg _

theorem vectorNull_approximateUnit_annihilates
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) {a : A} (ha : π a ξ = 0) :
    Tendsto (fun e : vectorNullAlgebra π ξ => a * (1 - (e : A)))
      (CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ)) (𝓝 0) := by
  let B := vectorNullAlgebra π ξ
  let j : B →⋆ₙₐ[ℂ] A := NonUnitalStarSubalgebraClass.subtype B
  let l := CStarAlgebra.approximateUnit B
  have hl := CStarAlgebra.increasingApproximateUnit B
  let b : B := ⟨star a * a, star_mul_self_mem_vectorNullAlgebra π ξ ha⟩
  have hb : Tendsto (fun e : B => (star a * a) * (e : A)) l (𝓝 (star a * a)) := by
    exact show Tendsto (fun e : B => j (b * e)) l (𝓝 (j b)) from
      (map_continuous j).tendsto b |>.comp (hl.tendsto_mul_left b)
  have hd : Tendsto (fun e : B => ‖star a * a - star a * a * (e : A)‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((tendsto_const_nhds (x := star a * a)).sub hb).norm
  have hbs : ∀ᶠ e : B in l,
      ‖a * (1 - (e : A))‖ ≤ Real.sqrt ‖star a * a - star a * a * (e : A)‖ := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he hen
    have heA : 0 ≤ (e : A) := vectorNullAlgebra_coe_nonneg π ξ e he
    have hle : (e : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ heA).mp hen
    have hx : 0 ≤ 1 - (e : A) := sub_nonneg.mpr hle
    have hxn : ‖1 - (e : A)‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hx).mpr (sub_le_self _ heA)
    apply (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mpr
    calc
      ‖a * (1 - (e : A))‖ ^ 2 =
          ‖star (a * (1 - (e : A))) * (a * (1 - (e : A)))‖ := by
        rw [CStarRing.norm_star_mul_self, pow_two]
      _ = ‖(1 - (e : A)) * (star a * a - star a * a * (e : A))‖ := by
        congr 1
        simp only [star_mul, star_sub, star_one, (IsSelfAdjoint.of_nonneg heA).star_eq]
        noncomm_ring
      _ ≤ ‖1 - (e : A)‖ * ‖star a * a - star a * a * (e : A)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖star a * a - star a * a * (e : A)‖ := by gcongr
      _ = _ := one_mul _
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbs
  simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hd

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorNull_complement_properties
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (ξ : H) :
    ∀ᶠ e : vectorNullAlgebra π ξ in
      CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ),
      0 ≤ 1 - (e : A) ∧ ‖1 - (e : A)‖ ≤ 1 ∧ π (1 - (e : A)) ξ = ξ := by
  have hl := CStarAlgebra.increasingApproximateUnit (vectorNullAlgebra π ξ)
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he hen
  have heA : 0 ≤ (e : A) := vectorNullAlgebra_coe_nonneg π ξ e he
  have hle : (e : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ heA).mp hen
  have hx : 0 ≤ 1 - (e : A) := sub_nonneg.mpr hle
  refine ⟨hx, (CStarAlgebra.norm_le_one_iff_of_nonneg _ hx).mpr
    (sub_le_self _ heA), ?_⟩
  simp only [map_sub, sub_apply, hone, one_apply_eq_self, e.property.1, sub_zero]

theorem irreducible_vector_excision
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) (a : A) :
    Tendsto (fun e : vectorNullAlgebra π ξ =>
      (1 - (e : A)) * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) * (1 - (e : A)))
      (CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ)) (𝓝 0) := by
  let a₀ := a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)
  have ha₀ : ⟪ξ, π a₀ ξ⟫_ℂ = 0 := by
    simp [a₀, map_sub, map_smul, sub_apply, smul_apply, irreducible_map_one π hπ,
      one_apply_eq_self, inner_self_eq_norm_sq_to_K, hξ]
  obtain ⟨b, c, hb, hc, hbc⟩ := irreducible_null_decomposition π hπ ξ hξ a₀ ha₀
  have hbL := vectorNull_approximateUnit_annihilates π ξ hb
  have hcL := vectorNull_approximateUnit_annihilates π ξ hc
  have hnL : Tendsto (fun e : vectorNullAlgebra π ξ =>
      ‖b * (1 - (e : A))‖ + ‖c * (1 - (e : A))‖)
      (CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ)) (𝓝 0) := by
    simpa only [norm_zero, zero_add] using hbL.norm.add hcL.norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hnL
  filter_upwards [vectorNull_complement_properties π (irreducible_map_one π hπ) ξ]
    with e he
  let x : A := 1 - (e : A)
  have hx : IsSelfAdjoint x := IsSelfAdjoint.of_nonneg he.1
  have hxn : ‖x‖ ≤ 1 := he.2.1
  change ‖x * a₀ * x‖ ≤ ‖b * x‖ + ‖c * x‖
  rw [hbc, mul_add, add_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ = ‖x * (b * x)‖ := by rw [mul_assoc]
      _ ≤ ‖x‖ * ‖b * x‖ := norm_mul_le _ _
      _ ≤ 1 * ‖b * x‖ := by gcongr
      _ = _ := one_mul _
  · calc
      _ ≤ ‖x * star c‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ ‖x * star c‖ * 1 := by gcongr
      _ = ‖c * x‖ := by rw [mul_one, ← norm_star (c * x), star_mul, hx.star_eq]

theorem pure_state_excision (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : A, 0 ≤ x ∧ ‖x‖ ≤ 1 ∧ f x = 1 ∧
      ‖x * (a - f a • (1 : A)) * x‖ < ε := by
  let g := positiveOfSquares f hf.1.2
  let π := g.gnsNonUnitalStarAlgHom
  let ξ := gnsVector g
  have hg : g 1 = 1 := (isState_iff f).mp hf.1 |>.1
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one g hg
  have hπ : IsIrreducible π := pure_gns_irreducible f hf.1 hf
  have hL := irreducible_vector_excision π hπ ξ hξ a
  have hcoeff (b : A) : ⟪ξ, π b ξ⟫_ℂ = f b := gnsVector_coefficient g b
  have hl := CStarAlgebra.increasingApproximateUnit (vectorNullAlgebra π ξ)
  have := hl.neBot
  have hsmall : ∀ᶠ e : vectorNullAlgebra π ξ in
      CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ),
      ‖(1 - (e : A)) * (a - f a • (1 : A)) * (1 - (e : A))‖ < ε := by
    simpa only [hcoeff, norm_zero] using (tendsto_order.1 hL.norm).2 ε (by simpa only [norm_zero] using hε)
  obtain ⟨e, he, hen⟩ :=
    ((vectorNull_complement_properties π (irreducible_map_one π hπ) ξ).and hsmall).exists
  refine ⟨1 - (e : A), he.1, he.2.1, ?_, hen⟩
  rw [← hcoeff, he.2.2, inner_self_eq_norm_sq_to_K, hξ]
  norm_num

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [StarOrderedRing B] in
theorem approximateUnit_strong
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) {l : Filter B}
    (hl : IsIncreasingApproximateUnit l)
    (hker : ∀ ξ : H, (∀ b : B, ρ b ξ = 0) → ξ = 0) (ξ : H) :
    Tendsto (fun e : B => ρ e ξ) l (𝓝 ξ) := by
  classical
  let M : Submodule ℂ H :=
    { carrier := {x | Tendsto (fun e : B => ρ e x) l (𝓝 x)}
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using (tendsto_const_nhds (x := (0 : H)))
      add_mem' := by
        intro x y hx hy
        simpa only [Set.mem_ofPred_eq, map_add] using hx.add hy
      smul_mem' := by
        intro z x hx
        simpa only [Set.mem_ofPred_eq, map_smul] using hx.const_smul z }
  have hclosed : IsClosed (M : Set H) := by
    let T (e : B) : H →L[ℂ] H := if ‖e‖ ≤ 1 then ρ e else 0
    have hT (e : B) : ‖T e‖ ≤ 1 := by
      dsimp only [T]
      split_ifs with he
      · exact (NonUnitalStarAlgHom.norm_apply_le ρ e).trans he
      · simp
    have hEq : Equicontinuous (fun e x => T e x) :=
      (LipschitzWith.uniformEquicontinuous _ 1
        (fun e => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hT e))).equicontinuous
    have hE (x : H) : (fun e => T e x) =ᶠ[l] (fun e => ρ e x) := by
      filter_upwards [hl.eventually_norm] with e he
      simp only [T, ite_eq_left he]
    have hc := hEq.isClosed_setOfPred_tendsto (l := l) continuous_id
    convert hc using 1
    ext x
    exact (tendsto_congr' (hE x)).symm
  have hr (b : B) (x : H) : ρ b x ∈ M := by
    have hc : Continuous (fun b : B => ρ b x) :=
      (ContinuousLinearMap.apply ℂ H x).continuous.comp (map_continuous ρ)
    have ht := (hc.tendsto b).comp (hl.tendsto_mul_right b)
    change Tendsto (fun e => ρ e (ρ b x)) l (𝓝 (ρ b x))
    simpa only [Function.comp_def, map_mul, mul_apply_eq_comp] using ht
  have hbot : Mᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply hker x
    intro b
    have hh := (M.mem_orthogonal x).mp hx (ρ (star b) (ρ b x)) (hr _ _)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at hh
    exact inner_self_eq_zero.mp hh
  let : IsClosed (M : Set H) := hclosed
  have htop : M = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
  exact show ξ ∈ M from htop ▸ Submodule.mem_top

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder A] [StarOrderedRing A] in

theorem nullAlgebra_vector_coefficient
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hone : ρ 1 = 1)
    (η : K) (hη : ‖η‖ = 1)
    (hnull : ∀ e : vectorNullAlgebra π ξ, ρ (e : A) η = 0) :
    ∀ a : A, ⟪ξ, π a ξ⟫_ℂ = ⟪η, ρ a η⟫_ℂ := by
  have hL (b : A) (hb : π b ξ = 0) : ρ b η = 0 := by
    have hh := hnull ⟨star b * b, star_mul_self_mem_vectorNullAlgebra π ξ hb⟩
    have hi : ⟪ρ b η, ρ b η⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
        ← map_star, ← mul_apply_eq_comp, ← map_mul, hh, inner_zero_right]
    exact inner_self_eq_zero.mp hi
  intro a
  let a₀ := a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)
  have ha₀ : ⟪ξ, π a₀ ξ⟫_ℂ = 0 := by
    simp [a₀, map_sub, map_smul, sub_apply, smul_apply, irreducible_map_one π hπ,
      one_apply_eq_self, inner_self_eq_norm_sq_to_K, hξ]
  obtain ⟨b, c, hb, hc, hbc⟩ := irreducible_null_decomposition π hπ ξ hξ a₀ ha₀
  have hzero : ⟪η, ρ a₀ η⟫_ℂ = 0 := by
    rw [hbc, map_add, add_apply, inner_add_right, hL b hb, inner_zero_right,
      zero_add, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hL c hc, inner_zero_left]
  dsimp only [a₀] at hzero
  simp only [map_sub, map_smul, sub_apply, smul_apply, hone, one_apply_eq_self,
    inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hη,
    ] at hzero
  norm_num at hzero
  exact (sub_eq_zero.mp hzero).symm

theorem inequivalent_nullAlgebra_common_kernel
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (hne : ¬ UnitarilyEquivalent π ρ) (η : K)
    (hnull : ∀ e : vectorNullAlgebra π ξ, ρ (e : A) η = 0) : η = 0 := by
  by_contra hη
  let ζ : K := ‖η‖⁻¹ • η
  have hζ : ‖ζ‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hη)]
  have hζ0 : ζ ≠ 0 := by intro h; simp only [h, norm_zero, zero_ne_one] at hζ
  have hξ0 : ξ ≠ 0 := by intro h; simp only [h, norm_zero, zero_ne_one] at hξ
  have hznull (e : vectorNullAlgebra π ξ) : ρ (e : A) ζ = 0 := by
    change (ρ (e : A)) (‖η‖⁻¹ • η) = 0
    rw [ContinuousLinearMap.map_smul_of_tower, hnull, smul_zero]
  exact hne (irreducible_equivalent_of_coefficients π hπ ρ hρ ξ ζ hξ0 hζ0
    (nullAlgebra_vector_coefficient π hπ ξ hξ ρ (irreducible_map_one ρ hρ) ζ hζ hznull))

theorem inequivalent_nullAlgebra_complement_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (hne : ¬ UnitarilyEquivalent π ρ) (η : K) :
    Tendsto (fun e : vectorNullAlgebra π ξ => ρ (1 - (e : A)) η)
      (CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ)) (𝓝 0) := by
  let j := NonUnitalStarSubalgebraClass.subtype (vectorNullAlgebra π ξ)
  have ht := approximateUnit_strong (ρ.comp j)
    (CStarAlgebra.increasingApproximateUnit (vectorNullAlgebra π ξ))
    (fun η hη => inequivalent_nullAlgebra_common_kernel π hπ ξ hξ ρ hρ hne η hη) η
  simpa only [map_sub, sub_apply, irreducible_map_one ρ hρ, one_apply_eq_self,
    NonUnitalStarAlgHom.comp_apply, j, NonUnitalStarSubalgebraClass.coe_subtype,
    sub_self] using (tendsto_const_nhds (x := η)).sub ht

open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_contraction_square_le {y : A} (hy : 0 ≤ y) (hn : ‖y‖ ≤ 1) :
    y * y ≤ y := by
  have h1 : y ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg y hy).mp hn
  have hpos := ((Commute.one_right y).sub_right (Commute.refl y)).mul_nonneg
    hy (sub_nonneg.mpr h1)
  simpa only [mul_sub, mul_one, sub_nonneg] using hpos

theorem cross_excision_bound {x y z : A} (hx : 0 ≤ x) (hxn : ‖x‖ ≤ 1)
    (hy : 0 ≤ y) (hyn : ‖y‖ ≤ 1) (hyz : y ≤ z) (a : A) (c : ℂ) :
    ‖x * a * y‖ ^ 2 ≤ ‖c‖ + ‖x * (a * z * star a - c • (1 : A)) * x‖ := by
  have hxs := IsSelfAdjoint.of_nonneg hx
  have hys := IsSelfAdjoint.of_nonneg hy
  have hsq := (positive_contraction_square_le hy hyn).trans hyz
  have hle := star_right_conjugate_le_conjugate hsq (x * a)
  have hid : x * a * (y * y) * star (x * a) =
      (x * a * y) * star (x * a * y) := by
    simp only [star_mul, hxs.star_eq, hys.star_eq]
    noncomm_ring
  rw [hid] at hle
  calc
    ‖x * a * y‖ ^ 2 = ‖(x * a * y) * star (x * a * y)‖ := by
      rw [CStarRing.norm_self_mul_star, pow_two]
    _ ≤ ‖x * a * z * star (x * a)‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hle (mul_star_self_nonneg _)
    _ = ‖c • (x * x) + x * (a * z * star a - c • (1 : A)) * x‖ := by
      congr 1
      simp only [star_mul, hxs.star_eq, mul_sub, sub_mul, mul_smul_comm,
        smul_mul_assoc, mul_one]
      noncomm_ring
    _ ≤ ‖c • (x * x)‖ + ‖x * (a * z * star a - c • (1 : A)) * x‖ := norm_add_le _ _
    _ ≤ ‖c‖ + ‖x * (a * z * star a - c • (1 : A)) * x‖ := by
      gcongr
      rw [norm_smul]
      calc
        _ ≤ ‖c‖ * (‖x‖ * ‖x‖) := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖c‖ * (1 * 1) := by gcongr
        _ = ‖c‖ := by ring

theorem cross_excision_tendsto
    {ι κ : Type*} [Preorder ι] [Preorder κ]
    [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]
    (x : ι → A) (y : κ → A) (f : A → ℂ)
    (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hy : ∀ j, 0 ≤ y j) (hyn : ∀ j, ‖y j‖ ≤ 1)
    (hym : Antitone y)
    (hexc : ∀ b : A, Tendsto (fun i => x i * (b - f b • (1 : A)) * x i) atTop (𝓝 0))
    (a : A) (hcoef : Tendsto (fun j => f (a * y j * star a)) atTop (𝓝 0)) :
    Tendsto (fun ij : ι × κ => x ij.1 * a * y ij.2) atTop (𝓝 0) := by
  let : IsDirectedOrder (ι × κ) := ⟨by
    intro p q
    obtain ⟨i, hi, hi'⟩ := exists_ge_ge p.1 q.1
    obtain ⟨j, hj, hj'⟩ := exists_ge_ge p.2 q.2
    exact ⟨(i,j), ⟨hi,hj⟩, ⟨hi',hj'⟩⟩⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε ^ 2 / 2 := by positivity
  have hc : ∀ᶠ j in atTop, ‖f (a * y j * star a)‖ < ε ^ 2 / 2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hcoef) _ hδ
  obtain ⟨j, hj⟩ := hc.exists
  have he : ∀ᶠ i in atTop,
      ‖x i * (a * y j * star a - f (a * y j * star a) • (1 : A)) * x i‖ < ε ^ 2 / 2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp (hexc (a * y j * star a))) _ hδ
  rw [eventually_atTop] at he
  obtain ⟨i, hi⟩ := he
  rw [eventually_atTop]
  refine ⟨(i,j), fun ij hij => ?_⟩
  simp only [dist_zero_right, norm_norm]
  have hb := cross_excision_bound (hx ij.1) (hxn ij.1) (hy ij.2) (hyn ij.2)
    (hym hij.2) a (f (a * y j * star a))
  have hh := hi ij.1 hij.1
  nlinarith [norm_nonneg (x ij.1 * a * y ij.2)]

open Filter Topology

def ExcisionIndex (B : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] := {b : B // 0 ≤ b ∧ ‖b‖ < 1}

namespace ExcisionIndex
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
instance : PartialOrder (ExcisionIndex B) := inferInstanceAs (PartialOrder {b : B // 0 ≤ b ∧ ‖b‖ < 1})
instance : Inhabited (ExcisionIndex B) := ⟨⟨0, by simp⟩⟩
instance : IsDirectedOrder (ExcisionIndex B) := ⟨by
  intro x y
  obtain ⟨z, hz, hxz, hyz⟩ := CStarAlgebra.directedOn_nonneg_ball
    (A := B) x.val (by simpa using x.property) y.val (by simpa using y.property)
  exact ⟨⟨z, by simpa using hz⟩, hxz, hyz⟩⟩

theorem tendsto_coe : Tendsto (fun e : ExcisionIndex B => e.val) atTop
    (CStarAlgebra.approximateUnit B) := by
  rw [(CStarAlgebra.hasBasis_approximateUnit B).tendsto_right_iff]
  intro b hb
  filter_upwards [eventually_ge_atTop (⟨b, hb⟩ : ExcisionIndex B)] with e he
  exact ⟨he, by simpa using e.property.2.le⟩

end ExcisionIndex

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma vectorNullAlgebra_coe_le
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e d : vectorNullAlgebra π ξ)
    (hed : @LE.le _ (vectorNullAlgebra_order π ξ).toLE e d) : (e : A) ≤ (d : A) := by
  have hdiff : @LE.le _ (vectorNullAlgebra_order π ξ).toLE 0 (d-e) := by
    simpa +instances only [vectorNullAlgebra_order, CStarAlgebra.spectralOrder, sub_zero]
      using hed
  exact sub_nonneg.mp (vectorNullAlgebra_coe_nonneg π ξ (d - e) hdiff)

def pureExcisionNet (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e : ExcisionIndex (vectorNullAlgebra π ξ)) : A := 1 - (e.val : A)

lemma pureExcisionNet_nonneg (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e : ExcisionIndex (vectorNullAlgebra π ξ)) : 0 ≤ pureExcisionNet π ξ e := by
  have he := vectorNullAlgebra_coe_nonneg π ξ e.val e.property.1
  exact sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ he).mp e.property.2.le)

lemma pureExcisionNet_norm (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e : ExcisionIndex (vectorNullAlgebra π ξ)) : ‖pureExcisionNet π ξ e‖ ≤ 1 := by
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (pureExcisionNet_nonneg π ξ e)).mpr
    (sub_le_self _ (vectorNullAlgebra_coe_nonneg π ξ e.val e.property.1))

lemma pureExcisionNet_antitone (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Antitone (pureExcisionNet π ξ) := by
  intro e d hed
  exact sub_le_sub_left (vectorNullAlgebra_coe_le π ξ e.val d.val hed) 1

omit [PartialOrder A] [StarOrderedRing A] in
lemma pureExcisionNet_fixes (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (ξ : H)
    (e : ExcisionIndex (vectorNullAlgebra π ξ)) : π (pureExcisionNet π ξ e) ξ = ξ := by
  simp only [pureExcisionNet, map_sub, sub_apply, hone, one_apply_eq_self,
    e.val.property.1, sub_zero]

lemma pureExcisionNet_excision (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) (a : A) :
    Tendsto (fun e => pureExcisionNet π ξ e * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) *
      pureExcisionNet π ξ e) atTop (𝓝 0) :=
  (irreducible_vector_excision π hπ ξ hξ a).comp ExcisionIndex.tendsto_coe

lemma pureExcisionNet_inequivalent_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (hne : ¬ UnitarilyEquivalent π ρ) (η : K) :
    Tendsto (fun e => ρ (pureExcisionNet π ξ e) η) atTop (𝓝 0) :=
  (inequivalent_nullAlgebra_complement_strong π hπ ξ hξ ρ hρ hne η).comp
    ExcisionIndex.tendsto_coe

theorem pureExcisionNet_cross
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (η : K) (hη : ‖η‖ = 1) (hne : ¬ UnitarilyEquivalent π ρ) (a : A) :
    Tendsto (fun ij : ExcisionIndex (vectorNullAlgebra π ξ) ×
        ExcisionIndex (vectorNullAlgebra ρ η) =>
      pureExcisionNet π ξ ij.1 * a * pureExcisionNet ρ η ij.2) atTop (𝓝 0) := by
  apply cross_excision_tendsto (pureExcisionNet π ξ) (pureExcisionNet ρ η)
    (fun b => ⟪ξ, π b ξ⟫_ℂ) (pureExcisionNet_nonneg π ξ) (pureExcisionNet_norm π ξ)
    (pureExcisionNet_nonneg ρ η) (pureExcisionNet_norm ρ η) (pureExcisionNet_antitone ρ η)
    (pureExcisionNet_excision π hπ ξ hξ) a
  have hs := pureExcisionNet_inequivalent_strong ρ hρ η hη π hπ
    (fun h => hne h.symm) (π (star a) ξ)
  have ht := Filter.Tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := π (star a) ξ)) hs
  simpa only [map_mul, map_star, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    inner_zero_right] using ht

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem strong_zero_of_nondegenerate
    {ι : Type*} {l : Filter ι} (T : ι → (H →L[ℂ] H))
    (hT : ∀ i, ‖T i‖ ≤ 1) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hker : ∀ ξ : H, (∀ b : B, ρ b ξ = 0) → ξ = 0)
    (hr : ∀ b : B, ∀ ξ : H, Tendsto (fun i => T i (ρ b ξ)) l (𝓝 0))
    (ξ : H) : Tendsto (fun i => T i ξ) l (𝓝 0) := by
  let M : Submodule ℂ H :=
    { carrier := {x | Tendsto (fun i => T i x) l (𝓝 0)}
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using
        (tendsto_const_nhds (x := (0 : H)))
      add_mem' := by
        intro x y hx hy
        simpa only [Set.mem_ofPred_eq, map_add, add_zero] using hx.add hy
      smul_mem' := by
        intro z x hx
        simpa only [Set.mem_ofPred_eq, map_smul, smul_zero] using hx.const_smul z }
  have hEq : Equicontinuous (fun i x => T i x) :=
    (LipschitzWith.uniformEquicontinuous _ 1
      (fun i => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hT i))).equicontinuous
  have hclosed : IsClosed (M : Set H) :=
    hEq.isClosed_setOfPred_tendsto (l := l) continuous_const
  have hbot : Mᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply hker x
    intro b
    have hh := (M.mem_orthogonal x).mp hx (ρ (star b) (ρ b x)) (hr _ _)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at hh
    exact inner_self_eq_zero.mp hh
  let : IsClosed (M : Set H) := hclosed
  have htop : M = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
  exact show ξ ∈ M from htop ▸ Submodule.mem_top

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {l : Filter ι}

theorem excision_null_mul_tendsto
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (x : ι → A)
    (hx : ∀ i, 0 ≤ x i)
    (hexc : ∀ a : A, Tendsto (fun i => x i * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) * x i)
      l (𝓝 0)) (b : A) (hb : π (star b) ξ = 0) :
    Tendsto (fun i => x i * b) l (𝓝 0) := by
  have hc : ⟪ξ, π (b * star b) ξ⟫_ℂ = 0 := by
    rw [map_mul, mul_apply_eq_comp, hb, map_zero, inner_zero_right]
  have hsq (i : ι) : ‖x i * b‖ ^ 2 = ‖x i * (b * star b) * x i‖ := by
    rw [pow_two, ← CStarRing.norm_self_mul_star, star_mul,
      (IsSelfAdjoint.of_nonneg (hx i)).star_eq]
    congr 1
    noncomm_ring
  have ht : Tendsto (fun i => ‖x i * b‖ ^ 2) l (𝓝 0) := by
    simpa only [hsq, hc, zero_smul, sub_zero, norm_zero] using (hexc (b * star b)).norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

theorem excision_inequivalent_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (ξ : H) (hξ : ‖ξ‖ = 1)
    (x : ι → A) (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hexc : ∀ a : A, Tendsto (fun i => x i * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) * x i)
      l (𝓝 0))
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (hne : ¬ UnitarilyEquivalent π ρ) (η : K) :
    Tendsto (fun i => ρ (x i) η) l (𝓝 0) := by
  let j := NonUnitalStarSubalgebraClass.subtype (vectorNullAlgebra π ξ)
  apply strong_zero_of_nondegenerate (fun i => ρ (x i))
    (fun i => (NonUnitalStarAlgHom.norm_apply_le ρ _).trans (hxn i)) (ρ.comp j)
    (fun η hη => inequivalent_nullAlgebra_common_kernel π hπ ξ hξ ρ hρ hne η hη)
  intro b ζ
  have ht := excision_null_mul_tendsto π ξ x hx hexc b.val b.property.2
  have hc : Continuous (fun a : A => ρ a ζ) :=
    (ContinuousLinearMap.apply ℂ K ζ).continuous.comp (map_continuous ρ)
  simpa only [Function.comp_def, map_mul, mul_apply_eq_comp, map_zero, zero_apply,
    NonUnitalStarAlgHom.comp_apply, j, NonUnitalStarSubalgebraClass.coe_subtype] using
    (hc.tendsto 0).comp ht

omit [PartialOrder A] [StarOrderedRing A] in

theorem irreducible_nullAlgebra_fixes_orthogonal
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (ξ : H) (hξ : ‖ξ‖ = 1)
    (η : H) (horth : ⟪ξ, η⟫_ℂ = 0) :
    ∃ b : vectorNullAlgebra π ξ, π (b : A) η = η := by
  let M := Submodule.span ℂ ({ξ, η} : Set H)
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton η).insert ξ)
  let T : H →L[ℂ] H := 1 - InnerProductSpace.rankOne ℂ ξ ξ
  have hT : IsSelfAdjoint T := by
    change star T = T
    simp only [T, star_sub, star_one, ContinuousLinearMap.star_eq_adjoint,
      InnerProductSpace.adjoint_rankOne]
  obtain ⟨b, hb, _, hbM⟩ := irreducible_selfAdjoint_transitivity π hπ M T hT
  have hbξ : π b ξ = 0 := by
    rw [hbM ξ (Submodule.subset_span (by simp))]
    simp [T, sub_apply, InnerProductSpace.rankOne_apply, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, hξ]
  refine ⟨⟨b, hbξ, by simpa only [hb.star_eq] using hbξ⟩, ?_⟩
  rw [hbM η (Submodule.subset_span (by simp))]
  simp [T, sub_apply, InnerProductSpace.rankOne_apply, one_apply_eq_self, horth]

theorem excision_orthogonal_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (ξ : H) (hξ : ‖ξ‖ = 1)
    (x : ι → A) (hx : ∀ i, 0 ≤ x i)
    (hexc : ∀ a : A, Tendsto (fun i => x i * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) * x i)
      l (𝓝 0)) (η : H) (horth : ⟪ξ, η⟫_ℂ = 0) :
    Tendsto (fun i => π (x i) η) l (𝓝 0) := by
  obtain ⟨b, hbη⟩ := irreducible_nullAlgebra_fixes_orthogonal π hπ ξ hξ η horth
  have ht := excision_null_mul_tendsto π ξ x hx hexc b.val b.property.2
  have hc : Continuous (fun a : A => π a η) :=
    (ContinuousLinearMap.apply ℂ H η).continuous.comp (map_continuous π)
  simpa only [Function.comp_def, map_mul, mul_apply_eq_comp, hbη,
    map_zero, zero_apply] using (hc.tendsto 0).comp ht

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positiveTrace_sandwich (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x a : A) (hx : 0 ≤ x) :
    ‖τ (star a * x * a)‖ ≤ ‖a‖ ^ 2 * ‖τ x‖ := by
  let s := CFC.sqrt x
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)
  have hss : s*s = x := CFC.sqrt_mul_sqrt_self x hx
  have hc : τ (star a*x*a) = τ (s*(a*star a)*s) := by
    rw [← hss]
    calc
      _ = τ ((s*s*a)*star a) := by
        simpa only [mul_assoc] using htr (star a) (s*s*a)
      _ = τ (s*(a*star a)*s) := by
        rw [show s*s*a*star a = s*(s*a*star a) by noncomm_ring,
          htr s (s*a*star a)]
        congr 1
        noncomm_ring
  have hb : s*(a*star a)*s ≤ ‖a‖ ^ 2 • x := by
    have hh := CStarAlgebra.star_left_conjugate_le_norm_smul (a := s) (b := a*star a)
    simpa only [hs.star_eq, hss, CStarRing.norm_self_mul_star, pow_two, mul_assoc] using hh
  have hp : 0 ≤ star a*x*a := star_left_conjugate_nonneg hx a
  have hτx := τ.map_nonneg hx
  rw [← Complex.re_eq_norm.mpr (τ.map_nonneg hp), hc,
    ← Complex.re_eq_norm.mpr hτx]
  have hh := (τ.monotone hb).1
  have hm : τ (‖a‖ ^ 2 • x) = (‖a‖ ^ 2 : ℝ) • τ x := by
    rw [← Complex.coe_smul, map_smul]
    rfl
  change (τ (s*(a*star a)*s)).re ≤ (τ (‖a‖ ^ 2 • x)).re at hh
  rw [hm] at hh
  simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hh

open Filter Topology
open scoped ComplexOrder

theorem positive_dini
    {ι X : Type*} [Preorder ι] [TopologicalSpace X] [CompactSpace X]
    (g : ι → C(X, ℂ)) (hg : ∀ i, 0 ≤ g i) (hm : Antitone g)
    (ht : ∀ t : X, Tendsto (fun i => g i t) atTop (𝓝 0)) :
    Tendsto g atTop (𝓝 0) := by
  let F : ι → C(X, ℝ) := fun i => ⟨fun t => ‖g i t‖, (g i).continuous.norm⟩
  have hF : Antitone F := by
    intro i j hij t
    exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (hm hij t) (hg j t)
  have htt : ∀ t : X, Tendsto (fun i => F i t) atTop (𝓝 ((0 : C(X, ℝ)) t)) := by
    intro t
    simpa only [F, ContinuousMap.coe_mk, norm_zero, ContinuousMap.zero_apply] using (ht t).norm
  have hn := (ContinuousMap.tendsto_of_antitone_of_pointwise hF htt).norm
  have hFn (i : ι) : ‖F i‖ = ‖g i‖ := by
    simp only [ContinuousMap.norm_eq_iSup_norm, F, ContinuousMap.coe_mk, norm_norm]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [hFn, norm_zero] using hn

open Filter Topology
open scoped ComplexOrder ComplexStarModule OnePoint InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev SequenceDiagonal := C(OnePoint ℕ, ℂ)
variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

def peakingCoefficientsFun (a : A) : SequenceDiagonal :=
  OnePoint.continuousMapMkNat (fun n => cornerState τ (peakAtom p n) a) (f a)
    (hp.tendsto_atomState τ hτ hpos a)

@[simp] theorem peakingCoefficientsFun_nat (a : A) (n : ℕ) :
    peakingCoefficientsFun hp τ hτ hpos a n = cornerState τ (peakAtom p n) a := rfl

@[simp] theorem peakingCoefficientsFun_infty (a : A) :
    peakingCoefficientsFun hp τ hτ hpos a ∞ = f a := rfl

theorem peakingCoefficientsFun_norm_le (a : A) :
    ‖peakingCoefficientsFun hp τ hτ hpos a‖ ≤ ‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  induction x using OnePoint.rec with
  | infty => exact state_norm_apply_le _ hp.2.2.1 a
  | coe n =>
    exact state_norm_apply_le _
      (cornerState_isState τ hτ _ (hp.peakAtom_projection n) (hpos n)) a

def peakingCoefficients : A →L[ℂ] SequenceDiagonal :=
  LinearMap.mkContinuous
    { toFun := peakingCoefficientsFun hp τ hτ hpos
      map_add' a b := by
        ext x
        induction x using OnePoint.rec with
        | infty => exact map_add f a b
        | coe n => exact map_add (cornerState τ (peakAtom p n)) a b
      map_smul' z a := by
        ext x
        induction x using OnePoint.rec with
        | infty => exact f.map_smul z a
        | coe n => exact (cornerState τ (peakAtom p n)).map_smul z a }
    1 (fun a => by
      change ‖peakingCoefficientsFun hp τ hτ hpos a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using peakingCoefficientsFun_norm_le hp τ hτ hpos a)

@[simp] theorem peakingCoefficients_nat (a : A) (n : ℕ) :
    peakingCoefficients hp τ hτ hpos a n = cornerState τ (peakAtom p n) a := rfl

@[simp] theorem peakingCoefficients_infty (a : A) :
    peakingCoefficients hp τ hτ hpos a ∞ = f a := rfl

def peakingCoefficientsPositive : A →ₚ[ℂ] SequenceDiagonal :=
  PositiveLinearMap.mk₀ (peakingCoefficients hp τ hτ hpos).toLinearMap (fun a ha t => by
    induction t using OnePoint.rec with
    | infty => exact (positiveOfSquares f hp.2.2.1.2).map_nonneg ha
    | coe n => exact (positiveOfSquares _
        (cornerState_isState τ hτ _ (hp.peakAtom_projection n) (hpos n)).2).map_nonneg ha)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}

theorem trace_sandwich_tendsto (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x : ι → A) (hx : ∀ i, 0 ≤ x i)
    (ht : Tendsto (fun i => τ (x i)) l (𝓝 0)) (a : A) :
    Tendsto (fun i => τ (star a * x i * a)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => positiveTrace_sandwich τ htr (x i) a (hx i))
  simpa only [norm_zero,mul_zero] using ht.norm.const_mul (‖a‖^2)

theorem peaking_endpoint_decay [Preorder ι]
    {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (x : ι → A) (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1) (hm : Antitone x)
    (htrace : Tendsto (fun i => τ (x i)) atTop (𝓝 0)) (a : A)
    (hinfty : Tendsto (fun i => f (star a*x i*a)) atTop (𝓝 0)) :
    Tendsto (fun i => peakingCoefficients hp τ hτ hpos (star a*(x i*x i)*a)) atTop (𝓝 0) := by
  let E := peakingCoefficientsPositive hp τ hτ hpos
  have hE (i : ι) : 0 ≤ E (star a*x i*a) :=
    E.map_nonneg (star_left_conjugate_nonneg (hx i) a)
  have hmono : Antitone (fun i => E (star a*x i*a)) := by
    intro i j hij
    exact E.monotone (star_left_conjugate_le_conjugate (hm hij) a)
  have ht : Tendsto (fun i => E (star a*x i*a)) atTop (𝓝 0) := by
    apply positive_dini _ hE hmono
    intro t
    induction t using OnePoint.rec with
    | infty => exact hinfty
    | coe n =>
      have hh := trace_sandwich_tendsto (positiveOfSquares τ hτ.2) htr x hx htrace (a*peakAtom p n)
      have he (i : ι) :
          E (star a*x i*a) n = (τ (peakAtom p n)).re⁻¹ •
            τ (star (a*peakAtom p n)*x i*(a*peakAtom p n)) := by
        change cornerState τ (peakAtom p n) (star a*x i*a) = _
        rw [cornerState_apply, star_mul, (hp.peakAtom_projection n).isSelfAdjoint.star_eq]
        simp only [mul_assoc]
      simp_rw [he]
      simpa only [smul_zero, positiveOfSquares_apply] using hh.const_smul (τ (peakAtom p n)).re⁻¹
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (g := fun i => ‖E (star a*x i*a)‖) (fun i => norm_nonneg _)
  · intro i
    exact CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (E.monotone (star_left_conjugate_le_conjugate
        (positive_contraction_square_le (hx i) (hxn i)) a))
      (E.map_nonneg (star_left_conjugate_nonneg
        (by simpa only [(IsSelfAdjoint.of_nonneg (hx i)).star_eq] using
          star_mul_self_nonneg (x i)) a))
  · simpa only [norm_zero] using ht.norm

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma state_norm_sq_le (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (a : A) :
    ‖τ a‖ ^ 2 ≤ (τ (star a * a)).re := by
  let g := positiveOfSquares τ hτ.2
  have h1 : g 1 = 1 := (isState_iff τ).mp hτ |>.1
  have hv : ‖gnsVector g‖ = 1 := gnsVector_norm_eq_one g h1
  have hc := norm_inner_le_norm (𝕜 := ℂ) (gnsVector g) (g.gnsStarAlgHom a (gnsVector g))
  rw [gnsVector_coefficient, hv, one_mul] at hc
  have hs : ‖g.gnsStarAlgHom a (gnsVector g)‖ ^ 2 = (τ (star a * a)).re := by
    have hh := gnsVector_coefficient g (star a * a)
    rw [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right] at hh
    calc
      _ = (⟪g.gnsStarAlgHom a (gnsVector g), g.gnsStarAlgHom a (gnsVector g)⟫_ℂ).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = _ := congrArg Complex.re hh
  change ‖τ a‖ ≤ _ at hc
  nlinarith [norm_nonneg (τ a), norm_nonneg (g.gnsStarAlgHom a (gnsVector g))]

lemma trace_excision_square_bound (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    {x q : A} (hx : 0 ≤ x) (hxn : ‖x‖ ≤ 1) (hq : IsStarProjection q) :
    (τ (x*x)).re ≤ (τ q).re + ‖x * (1-q) * x‖ := by
  have hxs := IsSelfAdjoint.of_nonneg hx
  have hxl : x*x ≤ 1 := (positive_contraction_square_le hx hxn).trans
    ((CStarAlgebra.norm_le_one_iff_of_nonneg x hx).mp hxn)
  have hqxx : q*x*x*q ≤ q := by
    have hh := hq.isSelfAdjoint.conjugate_le_conjugate hxl
    simpa only [mul_one, hq.isIdempotentElem.eq, mul_assoc] using hh
  have hmono := (positiveOfSquares τ hτ.2).monotone hqxx
  have hcyc : τ (x*q*x) = τ (q*x*x*q) := by
    have h1 := htr x (q*x)
    have h2 := htr (q*x*x) q
    simp only [mul_assoc] at h1 h2 ⊢
    rw [← mul_assoc q q, hq.isIdempotentElem.eq] at h2
    exact h1.trans h2.symm
  have hsum : τ (x*x) = τ (x*q*x) + τ (x*(1-q)*x) := by
    rw [← map_add]
    congr 1
    noncomm_ring
  rw [hsum, Complex.add_re, hcyc]
  exact add_le_add hmono.1 ((Complex.re_le_norm _).trans
    (state_norm_apply_le τ hτ _))

theorem excision_trace_null_of_small_projections
    {ι : Type*} {l : Filter ι} (x : ι → A) (f : A → ℂ)
    (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hexc : ∀ a : A, Tendsto (fun i => x i * (a - f a • (1 : A)) * x i) l (𝓝 0))
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hq : ∀ ε : ℝ, 0 < ε → ∃ q : A, IsStarProjection q ∧ f q = 1 ∧ (τ q).re < ε) :
    Tendsto (fun i => τ (x i)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε^2/2 := by positivity
  obtain ⟨q, hqp, hqf, hqt⟩ := hq (ε^2/2) hδ
  have hs : Tendsto (fun i => x i * (1-q) * x i) l (𝓝 0) := by
    have ht := (hexc q).neg
    have hh (i : ι) : -(x i * (q - 1) * x i) = x i * (1 - q) * x i := by
      noncomm_ring
    simpa only [hqf, one_smul, hh, neg_zero] using ht
  have he : ∀ᶠ i in l, ‖x i * (1-q) * x i‖ < ε^2/2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hs) _ hδ
  filter_upwards [he] with i hi
  simp only [dist_zero_right, norm_norm]
  have hb := trace_excision_square_bound τ hτ htr (hx i) (hxn i) hqp
  have hc := state_norm_sq_le τ hτ (x i)
  rw [(IsSelfAdjoint.of_nonneg (hx i)).star_eq] at hc
  nlinarith [norm_nonneg (τ (x i))]

lemma projection_exists_unit_fixed {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (hne : P ≠ 0) : ∃ η : H, ‖η‖ = 1 ∧ P η = η := by
  obtain ⟨v, hv⟩ : ∃ v : H, P v ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hne (ContinuousLinearMap.ext hh)
  let η : H := ‖P v‖⁻¹ • P v
  refine ⟨η, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  · change P (‖P v‖⁻¹ • P v) = ‖P v‖⁻¹ • P v
    rw [ContinuousLinearMap.map_smul_of_tower, ← mul_apply_eq_comp, hP.isIdempotentElem.eq]

lemma irreducible_small_projection_value_one
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (τ : A →L[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (p : A) (hp : IsStarProjection p) (hne : π p ≠ 0) :
    ∃ q : A, IsStarProjection q ∧ ⟪ξ, π q ξ⟫_ℂ = 1 ∧ τ q = τ p := by
  obtain ⟨η, hη, hpη⟩ := projection_exists_unit_fixed (hp.map π) hne
  obtain ⟨u, hu⟩ := irreducible_unitary_vector π hπ ξ η (hξ.trans hη.symm)
  let q : A := (Unitary.conjStarAlgAut ℂ A u).symm p
  refine ⟨q, hp.map _, ?_, ?_⟩
  · change ⟪ξ, π (star (u : A) * p * (u : A)) ξ⟫_ℂ = 1
    rw [map_mul, map_mul, map_star, mul_apply_eq_comp, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      hu, hpη, inner_self_eq_norm_sq_to_K, hη]
    norm_num
  · change τ (star (u : A) * p * (u : A)) = τ p
    rw [htr _ (u : A), ← mul_assoc, u.property.2, one_mul]

theorem pureExcisionNet_trace_null
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : A, IsStarProjection p ∧ π p ≠ 0 ∧ (τ p).re < ε) :
    Tendsto (fun i => τ (pureExcisionNet π ξ i)) atTop (𝓝 0) := by
  apply excision_trace_null_of_small_projections (pureExcisionNet π ξ)
    (fun a => ⟪ξ, π a ξ⟫_ℂ) (pureExcisionNet_nonneg π ξ) (pureExcisionNet_norm π ξ)
    (pureExcisionNet_excision π hπ ξ hξ) τ hτ htr
  intro ε hε
  obtain ⟨p, hp, hpne, hpt⟩ := hsmall ε hε
  obtain ⟨q, hq, hqv, hqt⟩ := irreducible_small_projection_value_one π hπ ξ hξ τ htr p hp hpne
  exact ⟨q, hq, hqv, hqt ▸ hpt⟩

open Filter Topology
open scoped ComplexOrder ComplexStarModule InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in

theorem vector_sandwich_tendsto
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (x : ι → A) (a : A)
    (ht : Tendsto (fun i => ρ (x i) (ρ a ξ)) l (𝓝 0)) :
    Tendsto (fun i => ⟪ξ, ρ (star a*x i*a) ξ⟫_ℂ) l (𝓝 0) := by
  have he (i : ι) : ⟪ξ, ρ (star a*x i*a) ξ⟫_ℂ =
      ⟪ρ a ξ, ρ (x i) (ρ a ξ)⟫_ℂ := by
    rw [map_mul,map_mul,map_star, mul_apply_eq_comp, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp_rw [he]
  simpa only [inner_zero_right] using tendsto_const_nhds.inner ht

def pureGNS (f : A →L[ℂ] ℂ) (hf : IsPureState f) :=
  (positiveOfSquares f hf.1.2).gnsNonUnitalStarAlgHom

theorem peaking_endpoint_of_excision [Preorder ι]
    {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (h : A →L[ℂ] ℂ) (hh : IsPureState h)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (x : ι → A) (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1) (hm : Antitone x)
    (htrace : Tendsto (fun i => τ (x i)) atTop (𝓝 0))
    (hexc : ∀ b : A, Tendsto (fun i => x i*(b-h b • (1:A))*x i) atTop (𝓝 0))
    (a : A) (hcase : ¬ UnitarilyEquivalent (pureGNS h hh) (pureGNS f hp.isPureState) ∨
      h = f ∧ f a = 0) :
    Tendsto (fun i => peakingCoefficients hp τ hτ hpos (star a*(x i*x i)*a)) atTop (𝓝 0) := by
  apply peaking_endpoint_decay hp τ hτ htr hpos x hx hxn hm htrace a
  let g := positiveOfSquares f hp.2.2.1.2
  let ρ := g.gnsNonUnitalStarAlgHom
  let ξ := gnsVector g
  have hρ : IsIrreducible ρ := pure_gns_irreducible f hp.2.2.1 hp.isPureState
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one g ((isState_iff f).mp hp.2.2.1).1
  have hcoeff (b : A) : ⟪ξ, ρ b ξ⟫_ℂ = f b := gnsVector_coefficient g b
  have ht : Tendsto (fun i => ρ (x i) (ρ a ξ)) atTop (𝓝 0) := by
    rcases hcase with hine | ⟨rfl, ha⟩
    · let g' := positiveOfSquares h hh.1.2
      let π := g'.gnsNonUnitalStarAlgHom
      let η := gnsVector g'
      have hπ : IsIrreducible π := pure_gns_irreducible h hh.1 hh
      have hη : ‖η‖ = 1 := gnsVector_norm_eq_one g' ((isState_iff h).mp hh.1).1
      have hcoeff' (b : A) : ⟪η, π b η⟫_ℂ = h b := gnsVector_coefficient g' b
      apply excision_inequivalent_strong π hπ η hη x hx hxn
        (fun b => ?_) ρ hρ hine (ρ a ξ)
      simpa only [hcoeff'] using hexc b
    · refine excision_orthogonal_strong ρ hρ ξ hξ x hx ?_ (ρ a ξ) ?_
      · intro b
        simpa only [hcoeff] using hexc b
      · simpa only [hcoeff] using ha
  simpa only [hcoeff] using
    vector_sandwich_tendsto ρ ξ x a ht

end NaimarkZFC

end

end OAI
