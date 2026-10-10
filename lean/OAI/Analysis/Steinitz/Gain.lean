import OAI.Analysis.Steinitz.Spectral

namespace OAI

/-! Contraction and gain potentials for positive semidefinite matrices. -/

namespace EuclideanSteinitz.Gain
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma transpose_bound {C : Matrix ι ι ℝ} {r : ℝ}
    (hC : C * C.transpose ≤ r • (1 : Matrix ι ι ℝ)) :
    C.transpose * C ≤ r • (1 : Matrix ι ι ℝ) := by
  have h₁ : (C * C.transpose).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_mul_conjTranspose_self C
  have h₂ : (C.transpose * C).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self C
  have heq := (h₂.eigenvalues_eq_eigenvalues_iff h₁).mpr (charpoly_mul_comm C.transpose C)
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le h₂.isSelfAdjoint]
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le h₁.isSelfAdjoint] at hC
  intro x hx
  rw [h₂.spectrum_real_eq_range_eigenvalues, heq, ← h₁.spectrum_real_eq_range_eigenvalues] at hx
  exact hC x hx

lemma cube_le_eight {K : Matrix ι ι ℝ} (hK : K.PosSemidef)
    (hK₂ : K ≤ (2 : ℝ) • (1 : Matrix ι ι ℝ)) :
    K ^ 3 ≤ (8 : ℝ) • (1 : Matrix ι ι ℝ) := by
  rw [← cfc_pow_id (R := ℝ) K 3 hK.1.isSelfAdjoint, ← Algebra.algebraMap_eq_smul_one,
    ← cfc_const (R := ℝ) (8 : ℝ) K hK.1.isSelfAdjoint,
    cfc_le_iff _ _ _ (by fun_prop) (by fun_prop) hK.1.isSelfAdjoint]
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le hK.1.isSelfAdjoint] at hK₂
  intro x hx
  have hx₀ := spectrum_nonneg_of_nonneg hK.nonneg hx
  have hx₂ := hK₂ x hx
  nlinarith [mul_nonneg hx₀ (sq_nonneg (x - 2)), sq_nonneg (x - 2)]

lemma relative_sqrt_bound {T H A : Matrix ι ι ℝ}
    (hT : IsUnit T) (hH : H.PosSemidef) (hA : A.PosSemidef)
    (hAeq : A = T * H * T.transpose)
    (hTT : T * T.transpose = 1 + A) (hA₁ : A ≤ 1) :
    T.transpose * CFC.sqrt A * T ≤ Real.sqrt 8 • CFC.sqrt H := by
  let K := T.transpose * T
  let B := T.transpose * CFC.sqrt A * T
  let R := CFC.sqrt A
  have hTt : IsUnit T.transpose := (Matrix.isUnit_transpose T).mpr hT
  let _ := hTt.invertible
  have hK : K.PosSemidef := by
    simpa only [K, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      (star_mul_self_nonneg T : (0 : Matrix ι ι ℝ) ≤ star T * T).posSemidef
  have hKH : K * H = K - 1 := by
    have h := congrArg (fun M : Matrix ι ι ℝ => T.transpose * M * T.transpose⁻¹) hTT
    rw [hAeq] at h
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.mul_one] at h
    change K = 1 + T.transpose * (T * H) at h
    rw [← Matrix.mul_assoc] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h.symm)
  have hHK : H * K = K - 1 := by
    have h := congrArg Matrix.conjTranspose hKH
    simpa only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
      hH.1.eq, hK.1.eq] using h
  have hcomm : Commute H K := by exact hHK.trans hKH.symm
  have hK₂ : K ≤ (2 : ℝ) • (1 : Matrix ι ι ℝ) := by
    apply transpose_bound
    rw [hTT, two_smul]
    exact add_le_add le_rfl hA₁
  have hB : B.PosSemidef := by
    simpa only [B, conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg A).posSemidef.conjTranspose_mul_mul_same T
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hBB : B * B = H * K ^ 3 := by
    calc
      B * B = T.transpose * (R * (T * T.transpose) * R) * T := by
        dsimp [B, R]; simp only [Matrix.mul_assoc]
      _ = T.transpose * (A * (1 + A)) * T := by
        rw [hTT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hRR]
        have hr : R * A * R = A * A := by
          rw [← hRR]; simp only [Matrix.mul_assoc]
        rw [hr]
        noncomm_ring
      _ = K * H * K * K := by
        rw [← hTT, hAeq]
        dsimp [K]
        simp only [Matrix.mul_assoc]
      _ = H * K ^ 3 := by rw [hcomm.eq.symm]; noncomm_ring
  have hsq : B * B ≤ (8 : ℝ) • H := by
    have hp := hcomm.pow_right 3
    have hc : Commute H ((8 : ℝ) • (1 : Matrix ι ι ℝ) - K ^ 3) :=
      (Commute.one_right H).smul_right 8 |>.sub_right hp
    have hh := hc.mul_nonneg hH.nonneg (sub_nonneg.mpr (cube_le_eight hK hK₂))
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← hBB] at hh
    exact sub_nonneg.mp hh
  have hroot : (Real.sqrt 8 • CFC.sqrt H : Matrix ι ι ℝ).PosSemidef :=
    (smul_nonneg (Real.sqrt_nonneg 8) (CFC.sqrt_nonneg H)).posSemidef
  apply MatrixEnergy.le_of_square_le hB hroot
  simpa only [smul_mul_assoc, mul_smul_comm, smul_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8),
    CFC.sqrt_mul_sqrt_self H hH.nonneg] using hsq

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Gain
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def inverseSqrt (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := (CFC.sqrt M)⁻¹

lemma inverseSqrt_psd (M : Matrix ι ι ℝ) : (inverseSqrt M).PosSemidef :=
  (CFC.sqrt_nonneg M).posSemidef.inv

lemma inverseSqrt_transpose (M : Matrix ι ι ℝ) : (inverseSqrt M).transpose = inverseSqrt M := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using (inverseSqrt_psd M).1.eq

lemma sqrt_transpose (M : Matrix ι ι ℝ) : (CFC.sqrt M).transpose = CFC.sqrt M := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg M).posSemidef.1.eq

lemma inverseSqrt_mul_sqrt {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    inverseSqrt M * CFC.sqrt M = 1 := by
  have h := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  let _ := h.invertible
  exact Matrix.inv_mul_of_invertible _

lemma sqrt_mul_inverseSqrt {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    CFC.sqrt M * inverseSqrt M = 1 := by
  have h := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  let _ := h.invertible
  exact Matrix.mul_inv_of_invertible _

lemma inverseSqrt_sandwich {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    inverseSqrt M * M * inverseSqrt M = 1 := by
  calc
    _ = inverseSqrt M * (CFC.sqrt M * CFC.sqrt M) * inverseSqrt M := by
      rw [CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg]
    _ = 1 := by rw [← Matrix.mul_assoc, inverseSqrt_mul_sqrt hM, Matrix.one_mul,
      sqrt_mul_inverseSqrt hM]

lemma inverseSqrt_unit {M : Matrix ι ι ℝ} (hM : M.PosDef) : IsUnit (inverseSqrt M) := by
  rw [inverseSqrt, nonsing_inv_eq_ringInverse, isUnit_ringInverse]
  exact (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit

omit [DecidableEq ι] in
lemma congruence_mono {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (L : Matrix ι ι ℝ) :
    L * A * L.transpose ≤ L * B * L.transpose := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, conjTranspose_eq_transpose_of_trivial]
    using (Matrix.le_iff.mp hAB).mul_mul_conjTranspose_same L

lemma trace_power_bound {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {a q : ℝ}
    (ha : 0 < a) (hq : 0 ≤ q) (htr : (cfc (fun x : ℝ => x ^ a) A).trace ≤ q ^ a) :
    A ≤ q • (1 : Matrix ι ι ℝ) := by
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le hA.1.isSelfAdjoint]
  rw [Spectral.trace_cfc hA.1] at htr
  intro x hx
  rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => hA.1.eigenvalues j ^ a)
    (fun j _ => Real.rpow_nonneg (hA.eigenvalues_nonneg j) a) (Finset.mem_univ i)
  exact (Real.rpow_le_rpow_iff (hA.eigenvalues_nonneg i) hq ha).mp (hs.trans htr)

lemma direct_coefficient_bound {S V D : Matrix ι ι ℝ}
    (hS : S.PosDef) (hV : V.PosSemidef) (hD : D.PosSemidef)
    (hVD : V ≤ D) (hJ : 1 + D = S + V)
    (hA : inverseSqrt S * V * inverseSqrt S ≤ 1) :
    inverseSqrt S * CFC.sqrt (inverseSqrt S * V * inverseSqrt S) * inverseSqrt S ≤
      Real.sqrt 8 • (inverseSqrt (1 + D) *
        CFC.sqrt (inverseSqrt (1 + D) * D * inverseSqrt (1 + D)) * inverseSqrt (1 + D)) := by
  let J := (1 : Matrix ι ι ℝ) + D
  let A := inverseSqrt S * V * inverseSqrt S
  let H := inverseSqrt J * V * inverseSqrt J
  let T := inverseSqrt S * CFC.sqrt J
  have hJp : J.PosDef := Matrix.PosDef.one.add_posSemidef hD
  have hAp : A.PosSemidef := by
    simpa only [A, inverseSqrt_transpose, conjTranspose_eq_transpose_of_trivial]
      using hV.mul_mul_conjTranspose_same (inverseSqrt S)
  have hHp : H.PosSemidef := by
    simpa only [H, inverseSqrt_transpose, conjTranspose_eq_transpose_of_trivial]
      using hV.mul_mul_conjTranspose_same (inverseSqrt J)
  have hTt : T.transpose = CFC.sqrt J * inverseSqrt S := by
    simp only [T, Matrix.transpose_mul, sqrt_transpose, inverseSqrt_transpose]
  have hAe : A = T * H * T.transpose := by
    rw [hTt]
    dsimp [T, H]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt J), sqrt_mul_inverseSqrt hJp, Matrix.one_mul]
    rw [← Matrix.mul_assoc (inverseSqrt J), inverseSqrt_mul_sqrt hJp, Matrix.one_mul]
    simp only [A, Matrix.mul_assoc]
  have hTT : T * T.transpose = 1 + A := by
    rw [hTt]
    dsimp only [T]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt J),
      CFC.sqrt_mul_sqrt_self J hJp.posSemidef.nonneg, ← Matrix.mul_assoc]
    change inverseSqrt S * ((1 : Matrix ι ι ℝ) + D) * inverseSqrt S = 1 + A
    rw [hJ, Matrix.mul_add, Matrix.add_mul, inverseSqrt_sandwich hS]
  have hTu : IsUnit T := (inverseSqrt_unit hS).mul
    ((CFC.isUnit_sqrt_iff J hJp.posSemidef.nonneg).mpr hJp.isUnit)
  have hrel := relative_sqrt_bound hTu hHp hAp hAe hTT hA
  have hh := congruence_mono hrel (inverseSqrt J)
  rw [inverseSqrt_transpose, hTt] at hh
  dsimp only [T] at hh
  simp only [← Matrix.mul_assoc, inverseSqrt_mul_sqrt hJp, Matrix.one_mul] at hh
  simp only [Matrix.mul_assoc, sqrt_mul_inverseSqrt hJp, Matrix.mul_one] at hh
  have hp : (inverseSqrt J * D * inverseSqrt J).PosSemidef := by
    simpa only [inverseSqrt_transpose, conjTranspose_eq_transpose_of_trivial]
      using hD.mul_mul_conjTranspose_same (inverseSqrt J)
  have hm : H ≤ inverseSqrt J * D * inverseSqrt J := by
    simpa only [H, inverseSqrt_transpose] using congruence_mono hVD (inverseSqrt J)
  have hsqrt := MatrixEnergy.sqrt_le_sqrt hHp hp hm
  have hout := congruence_mono hsqrt (inverseSqrt J)
  rw [inverseSqrt_transpose] at hout
  have hs := smul_le_smul_of_nonneg_left hout (Real.sqrt_nonneg 8)
  have hleft : inverseSqrt S * CFC.sqrt A * inverseSqrt S ≤
      Real.sqrt 8 • (inverseSqrt J * CFC.sqrt H * inverseSqrt J) := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using hh
  exact hleft.trans hs

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.GainScalar
open MatrixEnergy

noncomputable def rate (x : ℝ) : ℝ :=
  Real.sqrt x / ((1 + x) * Real.sqrt (1 + x))

noncomputable def extendedRate (x : ℝ) : ℝ := rate (max 0 x)

noncomputable def primitive (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, extendedRate u

lemma rate_eq {x : ℝ} (hx : 0 ≤ x) :
    rate x = x ^ (exponent - 1) / (1 + x) ^ exponent := by
  have hx1 : 0 < 1 + x := by positivity
  have hp : (1 + x) ^ exponent = (1 + x) * Real.sqrt (1 + x) := by
    rw [show exponent = 1 + (1 / 2 : ℝ) by norm_num [exponent],
      Real.rpow_add hx1, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hp, show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
  rfl

lemma extendedRate_eq {x : ℝ} (hx : 0 ≤ x) : extendedRate x = rate x := by
  simp only [extendedRate, max_eq_right hx]

lemma continuous_extendedRate : Continuous extendedRate := by
  unfold extendedRate rate
  fun_prop (disch := intro x; positivity)

lemma rate_continuousOn : ContinuousOn rate (Set.Ici 0) := by
  refine continuous_extendedRate.continuousOn.congr ?_
  intro x hx
  exact (extendedRate_eq hx).symm

lemma primitive_eq {x : ℝ} (hx : 0 ≤ x) : primitive x = gainPotential x := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hx] at hu
  rw [extendedRate_eq hu.1, rate_eq hu.1]

lemma primitive_derivative (x : ℝ) : HasDerivAt primitive (extendedRate x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_extendedRate.intervalIntegrable 0 x)
    continuous_extendedRate.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_extendedRate.continuousAt

lemma rate_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt rate ((1 - 2 * x) / (2 * Real.sqrt x * (1 + x) ^ 2 * Real.sqrt (1 + x))) x := by
  have hx1 : 0 < 1 + x := by positivity
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x)) (1 / (2 * Real.sqrt (1 + x))) x := by
    simpa only [Function.comp_def, mul_one] using (Real.hasDerivAt_sqrt (ne_of_gt hx1)).comp x
      ((hasDerivAt_id x).const_add 1)
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hx)).div
    (((hasDerivAt_id x).const_add 1).mul hs) (by positivity : (1 + x) * Real.sqrt (1 + x) ≠ 0)
  convert! h using 1
  simp only [Pi.mul_apply, id_eq]
  field_simp
  ring_nf
  rw [Real.sq_sqrt hx.le, Real.sq_sqrt hx1.le]
  ring

lemma rate_derivative_lower {x : ℝ} (hx : 0 < x) :
    -1 ≤ (1 - 2 * x) / (2 * Real.sqrt x * (1 + x) ^ 2 * Real.sqrt (1 + x)) := by
  have hx1 : 0 < 1 + x := by positivity
  have hxs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hys : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.mpr hx1
  have hs : Real.sqrt x ≤ Real.sqrt (1 + x) := Real.sqrt_le_sqrt (by linarith)
  have hprod : x ≤ Real.sqrt x * Real.sqrt (1 + x) := by
    nlinarith [Real.sq_sqrt hx.le]
  have hsq : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith
  have hp : x ≤ Real.sqrt x * Real.sqrt (1 + x) * (1 + x) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hxs.le hys.le)]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

lemma rate_add_linear_monotone : MonotoneOn (fun x : ℝ => rate x + 2 * x) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (rate_continuousOn.add (continuous_const.mul continuous_id).continuousOn)
    (f' := fun x => (1 - 2 * x) / (2 * Real.sqrt x * (1 + x) ^ 2 * Real.sqrt (1 + x)) + 2)
  · intro x hx
    rw [interior_Ici] at hx
    exact ((rate_derivative hx).fun_add (hasDerivAt_const_mul (x := x) 2)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have h := rate_derivative_lower hx
    linarith

lemma extendedRate_add_linear_monotone : Monotone (fun x : ℝ => extendedRate x + 2 * x) := by
  intro x y hxy
  change extendedRate x + 2 * x ≤ extendedRate y + 2 * y
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := hx.trans hxy
    simpa only [extendedRate_eq hx, extendedRate_eq hy] using rate_add_linear_monotone hx hy hxy
  · have hxn : x ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have he : extendedRate x = 0 := by simp [extendedRate, max_eq_left hxn, rate]
      have heg : 0 ≤ extendedRate y := by rw [extendedRate_eq hy]; unfold rate; positivity
      rw [he]
      linarith
    · have hyn : y ≤ 0 := le_of_not_ge hy
      simp only [extendedRate, max_eq_left hxn, max_eq_left hyn]
      linarith

lemma convexified_derivative (x : ℝ) :
    HasDerivAt (fun u : ℝ => primitive u + u ^ 2) (extendedRate x + 2 * x) x := by
  simpa using! (primitive_derivative x).fun_add ((hasDerivAt_id x).fun_pow 2)

lemma convexified_convex : ConvexOn ℝ Set.univ (fun x : ℝ => primitive x + x ^ 2) := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (convexified_derivative x).differentiableAt)
  have he : deriv (fun x : ℝ => primitive x + x ^ 2) = (fun x => extendedRate x + 2 * x) := by
    funext x
    exact (convexified_derivative x).deriv
  rw [he]
  exact extendedRate_add_linear_monotone

end EuclideanSteinitz.GainScalar

namespace EuclideanSteinitz.Gain
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_spectrum_continuous (f : ℝ → ℝ) (A : Matrix ι ι ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

lemma sqrt_eq_cfc_real {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    CFC.sqrt A = cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hA.nonneg]
  congr 1
  funext x
  exact (Real.sqrt_eq_rpow x).symm

lemma inverseSqrt_add_one {D : Matrix ι ι ℝ} (hD : D.PosSemidef) :
    inverseSqrt (1 + D) = cfc (fun x : ℝ => (Real.sqrt (1 + x))⁻¹) D := by
  have hJ : ((1 : Matrix ι ι ℝ) + D).PosSemidef := Matrix.PosSemidef.one.add hD
  have he : cfc (fun x : ℝ => 1 + x) D = 1 + D := by
    rw [cfc_const_add (1 : ℝ) (fun x : ℝ => x) D continuousOn_id hD.1.isSelfAdjoint,
      cfc_id' ℝ D hD.1.isSelfAdjoint, map_one]
  rw [inverseSqrt, sqrt_eq_cfc_real hJ, ← he, ← cfc_comp Real.sqrt (fun x : ℝ => 1 + x) D]
  rw [cfc_inv (fun x : ℝ => Real.sqrt (1 + x)) D]
  · exact nonsing_inv_eq_ringInverse _
  · intro x hx
    have hx₀ := spectrum_nonneg_of_nonneg hD.nonneg hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

lemma relative_rate_coefficient {D : Matrix ι ι ℝ} (hD : D.PosSemidef) :
    inverseSqrt (1 + D) *
      CFC.sqrt (inverseSqrt (1 + D) * D * inverseSqrt (1 + D)) * inverseSqrt (1 + D) =
      cfc GainScalar.rate D := by
  let f : ℝ → ℝ := fun x => (Real.sqrt (1 + x))⁻¹
  have hfc : ContinuousOn f (spectrum ℝ D) := finite_spectrum_continuous _ _
  have hs : (inverseSqrt (1 + D) * D * inverseSqrt (1 + D)).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, inverseSqrt_transpose]
      using hD.mul_mul_conjTranspose_same (inverseSqrt (1 + D))
  rw [sqrt_eq_cfc_real hs, inverseSqrt_add_one hD]
  change cfc f D * cfc Real.sqrt (cfc f D * D * cfc f D) * cfc f D = _
  have hmid : cfc f D * D * cfc f D = cfc (fun x => f x * id x * f x) D := by
    rw [cfc_mul (fun x => f x * id x) f D (finite_spectrum_continuous _ _) hfc,
      cfc_mul f id D hfc continuousOn_id, cfc_id ℝ D hD.1.isSelfAdjoint]
  rw [hmid, ← cfc_comp Real.sqrt (fun x => f x * id x * f x) D]
  rw [← cfc_mul f (Real.sqrt ∘ (fun x => f x * id x * f x)) D hfc
    (finite_spectrum_continuous _ _),
    ← cfc_mul (fun x => f x * (Real.sqrt ∘ (fun x => f x * id x * f x)) x) f D
      (finite_spectrum_continuous _ _) hfc]
  apply cfc_congr
  intro x hx
  have hx₀ := spectrum_nonneg_of_nonneg hD.nonneg hx
  have hx1 : 0 < 1 + x := by positivity
  have hs1 : Real.sqrt (1 + x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx1)
  have he : f x * id x * f x = x / (1 + x) := by
    dsimp [f]
    field_simp
    rw [Real.sq_sqrt hx1.le]
  simp only [Function.comp_apply, he, Real.sqrt_div hx₀]
  dsimp [f, GainScalar.rate]
  field_simp
  rw [Real.sq_sqrt hx1.le]

lemma direct_coefficient_bound_rate {S V D : Matrix ι ι ℝ}
    (hS : S.PosDef) (hV : V.PosSemidef) (hD : D.PosSemidef)
    (hVD : V ≤ D) (hJ : 1 + D = S + V)
    (hA : inverseSqrt S * V * inverseSqrt S ≤ 1) :
    inverseSqrt S * CFC.sqrt (inverseSqrt S * V * inverseSqrt S) * inverseSqrt S ≤
      Real.sqrt 8 • cfc GainScalar.rate D := by
  simpa only [relative_rate_coefficient hD] using direct_coefficient_bound hS hV hD hVD hJ hA

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Spectral
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_semiconvex_affine_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (f g : ℝ → ℝ)
    (hg : Continuous g) (hder : ∀ x, HasDerivAt f (g x) x)
    (hconv : ConvexOn ℝ Set.univ (fun x : ℝ => f x + x ^ 2)) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (cfc f (A + u • H)).trace)
      (cfc g (A + t • H) * H).trace t := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hder x).continuousAt)
  have hgf : Continuous (fun x : ℝ => g x + 2 * x) := by fun_prop
  have hdf (x : ℝ) : HasDerivAt (fun u : ℝ => f u + u ^ 2) (g x + 2 * x) x := by
    simpa using! (hder x).fun_add ((hasDerivAt_id x).fun_pow 2)
  have hd := trace_cfc_affine_derivative hA hH (fun x : ℝ => f x + x ^ 2)
    (fun x : ℝ => g x + 2 * x) (T := Set.univ) (S := Set.univ) (Set.mem_univ t)
    (fun _ _ => Set.subset_univ _) (fun x hx y hy =>
      convex_tangent hconv hx hy (hdf y).hasDerivWithinAt)
    (continuous_cfc_affine hA hH hgf).continuousWithinAt
  have hs := trace_cfc_affine_derivative hA hH (fun x : ℝ => x ^ 2)
    (fun x : ℝ => 2 * x) (T := Set.univ) (S := Set.univ) (Set.mem_univ t)
    (fun _ _ => Set.subset_univ _) (fun x _ y _ => by nlinarith [sq_nonneg (x - y)])
    (continuous_cfc_affine hA hH (by fun_prop)).continuousWithinAt
  have hh := (hasDerivWithinAt_univ.mp hd).sub (hasDerivWithinAt_univ.mp hs)
  convert! hh using 1
  · funext u
    dsimp only [Pi.sub_apply]
    rw [cfc_add (A + u • H) f (fun x : ℝ => x ^ 2) hf.continuousOn (by fun_prop), trace_add]
    ring
  · rw [cfc_add (A + t • H) g (fun x : ℝ => 2 * x) hg.continuousOn (by fun_prop), Matrix.add_mul, trace_add]
    ring

lemma trace_gainPotential_affine_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    (hpos : ∀ u ∈ T, (A + u • H).PosSemidef) :
    HasDerivWithinAt (fun u : ℝ => (cfc MatrixEnergy.gainPotential (A + u • H)).trace)
      (cfc (fun x : ℝ => x ^ (MatrixEnergy.exponent - 1) / (1 + x) ^ MatrixEnergy.exponent)
        (A + t • H) * H).trace T t := by
  have hd := trace_semiconvex_affine_derivative hA hH GainScalar.primitive
    GainScalar.extendedRate GainScalar.continuous_extendedRate
    GainScalar.primitive_derivative GainScalar.convexified_convex t
  have he (u : ℝ) (hu : u ∈ T) :
      cfc GainScalar.primitive (A + u • H) = cfc MatrixEnergy.gainPotential (A + u • H) := by
    apply cfc_congr
    intro x hx
    exact GainScalar.primitive_eq (spectrum_nonneg_of_nonneg (hpos u hu).nonneg hx)
  have hr : cfc GainScalar.extendedRate (A + t • H) =
      cfc (fun x : ℝ => x ^ (MatrixEnergy.exponent - 1) / (1 + x) ^ MatrixEnergy.exponent)
        (A + t • H) := by
    apply cfc_congr
    intro x hx
    have hx₀ := spectrum_nonneg_of_nonneg (hpos t ht).nonneg hx
    rw [GainScalar.extendedRate_eq hx₀, GainScalar.rate_eq hx₀]
  rw [hr] at hd
  exact hd.hasDerivWithinAt.congr (fun u hu => congrArg Matrix.trace (he u hu).symm)
    (congrArg Matrix.trace (he t ht).symm)

end EuclideanSteinitz.Spectral

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def relativeMoment (S V : Matrix ι ι ℝ) : ℝ :=
  (cfc (fun x : ℝ => x ^ exponent) (inverseSqrt S * V * inverseSqrt S)).trace

noncomputable def gainValue (D : Matrix ι ι ℝ) : ℝ := (cfc gainPotential D).trace

noncomputable def gainConstant : ℝ := exponent * 2 ^ exponent

lemma two_rpow_exponent : (2 : ℝ) ^ exponent = Real.sqrt 8 := by
  rw [show exponent = 1 + (1 / 2 : ℝ) by norm_num [exponent],
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h := Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num) 2
  norm_num at h
  exact h.symm

lemma gainConstant_pos : 0 < gainConstant := by
  unfold gainConstant
  exact mul_pos exponent_pos (Real.rpow_pos_of_pos (by norm_num) _)

lemma sandwich_psd {V : Matrix ι ι ℝ} (hV : V.PosSemidef) (S : Matrix ι ι ℝ) :
    (inverseSqrt S * V * inverseSqrt S).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial, inverseSqrt_transpose]
    using hV.mul_mul_conjTranspose_same (inverseSqrt S)

lemma sandwich_affine (S V W : Matrix ι ι ℝ) (u : ℝ) :
    inverseSqrt S * (V + u • W) * inverseSqrt S =
      inverseSqrt S * V * inverseSqrt S + u • (inverseSqrt S * W * inverseSqrt S) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma relativeMoment_derivative {S V W : Matrix ι ι ℝ}
    (hV : V.PosSemidef) (hW : W.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => relativeMoment S (V + u • W))
      (exponent * ((inverseSqrt S * CFC.sqrt (inverseSqrt S * (V + t • W) * inverseSqrt S) *
        inverseSqrt S) * W).trace) (Set.Ici 0) t := by
  have hVt : (V + t • W).PosSemidef := hV.add (hW.smul ht)
  have hd := Spectral.trace_rpow_affine_derivative (sandwich_psd hV S).1
    (sandwich_psd hW S).1 (show (1 : ℝ) ≤ exponent by norm_num [exponent])
    (T := Set.Ici 0) ht (fun u hu => by
      rw [← sandwich_affine]
      exact sandwich_psd (hV.add (hW.smul hu)) S)
  have hh : cfc (fun x : ℝ => x ^ (exponent - 1))
      (inverseSqrt S * V * inverseSqrt S + t • (inverseSqrt S * W * inverseSqrt S)) =
      CFC.sqrt (inverseSqrt S * (V + t • W) * inverseSqrt S) := by
    rw [← sandwich_affine, sqrt_eq_cfc_real (sandwich_psd hVt S)]
    congr 1
    funext x
    rw [show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], Real.sqrt_eq_rpow]
  rw [hh] at hd
  convert! hd using 1
  · funext u
    simp only [relativeMoment, sandwich_affine]
  · congr 1
    let A := CFC.sqrt (inverseSqrt S * (V + t • W) * inverseSqrt S)
    change ((inverseSqrt S * A * inverseSqrt S) * W).trace =
      (A * (inverseSqrt S * W * inverseSqrt S)).trace
    calc
      _ = (inverseSqrt S * (A * inverseSqrt S * W)).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((A * inverseSqrt S * W) * inverseSqrt S).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]

lemma gainValue_derivative {D W : Matrix ι ι ℝ}
    (hD : D.PosSemidef) (hW : W.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => gainValue (D + u • W))
      (cfc GainScalar.rate (D + t • W) * W).trace (Set.Ici 0) t := by
  have hd := Spectral.trace_gainPotential_affine_derivative hD.1 hW.1
    (T := Set.Ici 0) ht (fun u hu => hD.add (hW.smul hu))
  have he : cfc (fun x : ℝ => x ^ (exponent - 1) / (1 + x) ^ exponent) (D + t • W) =
      cfc GainScalar.rate (D + t • W) := by
    apply cfc_congr
    intro x hx
    exact (GainScalar.rate_eq (spectrum_nonneg_of_nonneg (hD.add (hW.smul ht)).nonneg hx)).symm
  rwa [he] at hd

lemma rate_nonneg {D : Matrix ι ι ℝ} (hD : D.PosSemidef) :
    (cfc GainScalar.rate D).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro x hx
  have hx₀ := spectrum_nonneg_of_nonneg hD.nonneg hx
  unfold GainScalar.rate
  positivity

lemma gainValue_monotone {D W : Matrix ι ι ℝ}
    (hD : D.PosSemidef) (hW : W.PosSemidef) :
    MonotoneOn (fun u : ℝ => gainValue (D + u • W)) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun u hu => (gainValue_derivative hD hW hu).continuousWithinAt)
    (f' := fun t => (cfc GainScalar.rate (D + t • W) * W).trace)
  · intro t ht
    exact (gainValue_derivative hD hW (interior_subset ht)).mono interior_subset
  · intro t ht
    exact MatrixEnergy.trace_mul_nonneg (rate_nonneg (hD.add (hW.smul (interior_subset ht)))) hW

lemma gain_derivative_bound {Z V W : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hV : V.PosSemidef) (hW : W.PosSemidef)
    (hG : relativeMoment (1 + Z) V ≤ 1) :
    exponent * ((inverseSqrt (1 + Z) *
      CFC.sqrt (inverseSqrt (1 + Z) * V * inverseSqrt (1 + Z)) * inverseSqrt (1 + Z)) * W).trace ≤
      gainConstant * (cfc GainScalar.rate (Z + V) * W).trace := by
  have hS : ((1 : Matrix ι ι ℝ) + Z).PosDef := Matrix.PosDef.one.add_posSemidef hZ
  have hA : inverseSqrt (1 + Z) * V * inverseSqrt (1 + Z) ≤ 1 := by
    have ht : (cfc (fun x : ℝ => x ^ exponent)
        (inverseSqrt (1 + Z) * V * inverseSqrt (1 + Z))).trace ≤ (1 : ℝ) ^ exponent := by
      simpa only [Real.one_rpow, relativeMoment] using hG
    simpa only [one_smul] using trace_power_bound (sandwich_psd hV (1 + Z)) exponent_pos
      (show (0 : ℝ) ≤ 1 by norm_num) ht
  have hVD : V ≤ Z + V := by
    exact le_add_of_nonneg_left hZ.nonneg
  have hc := direct_coefficient_bound_rate hS hV (hZ.add hV) hVD (by abel) hA
  have ht := MatrixEnergy.trace_mul_mono_right hc hW
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at ht
  have h := mul_le_mul_of_nonneg_left ht exponent_pos.le
  simpa only [gainConstant, two_rpow_exponent, mul_assoc] using h

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz

lemma conditional_derivative_comparison {f f' g g' : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1))
    (hfd : ∀ x ∈ Set.Ico 0 1, HasDerivWithinAt f (f' x) (Set.Ici x) x)
    (hgd : ∀ x ∈ Set.Ico 0 1, HasDerivWithinAt g (g' x) (Set.Ici x) x)
    (hbudget : ∀ x ∈ Set.Icc 0 1, f 0 + g x - g 0 ≤ 1 / 4)
    (hbound : ∀ x ∈ Set.Ico 0 1, f x ≤ 1 → f' x ≤ g' x) :
    ∀ x ∈ Set.Icc 0 1, f x ≤ f 0 + g x - g 0 := by
  have hB : ContinuousOn (fun x => f 0 + g x - g 0 + x / 2) (Set.Icc 0 1) :=
    ((continuousOn_const.add hg).sub continuousOn_const).add
      (continuous_id.div_const 2).continuousOn
  have hBd (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
      HasDerivWithinAt (fun x => f 0 + g x - g 0 + x / 2) (g' x + 1 / 2) (Set.Ici x) x := by
    simpa using! (((hgd x hx).const_add (f 0)).sub_const (g 0)).add
      ((hasDerivAt_id x).div_const 2).hasDerivWithinAt
  have hpre := image_le_of_deriv_right_lt_deriv_boundary' hf hfd
    (B := fun x => f 0 + g x - g 0 + x / 2) (B' := fun x => g' x + 1 / 2)
    (by simp) hB hBd (fun x hx he => by
      have hb := hbudget x ⟨hx.1, hx.2.le⟩
      have hx1 : f x ≤ 1 := by rw [he]; linarith [hx.2]
      linarith [hbound x hx hx1])
  have hfull (x : ℝ) (hx : x ∈ Set.Ico 0 1) : f' x ≤ g' x := by
    apply hbound x hx
    have hp := hpre (show x ∈ Set.Icc 0 1 from ⟨hx.1, hx.2.le⟩)
    have hb := hbudget x ⟨hx.1, hx.2.le⟩
    linarith [hx.2]
  apply fun x hx => image_le_of_deriv_right_le_deriv_boundary hf hfd
    (B := fun x => f 0 + g x - g 0) (B' := g') (by simp)
    ((continuousOn_const.add hg).sub continuousOn_const)
    (fun x hx => by simpa using! ((hgd x hx).const_add (f 0)).sub_const (g 0)) hfull hx

end EuclideanSteinitz

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma relativeMoment_gain {Z V W : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hV : V.PosSemidef) (hW : W.PosSemidef)
    (hbudget : relativeMoment (1 + Z) V +
      gainConstant * (gainValue (Z + V + W) - gainValue (Z + V)) ≤ 1 / 4) :
    relativeMoment (1 + Z) (V + W) ≤ relativeMoment (1 + Z) V +
      gainConstant * (gainValue (Z + V + W) - gainValue (Z + V)) := by
  let f : ℝ → ℝ := fun t => relativeMoment (1 + Z) (V + t • W)
  let f' : ℝ → ℝ := fun t => exponent * ((inverseSqrt (1 + Z) *
    CFC.sqrt (inverseSqrt (1 + Z) * (V + t • W) * inverseSqrt (1 + Z)) *
      inverseSqrt (1 + Z)) * W).trace
  let g : ℝ → ℝ := fun t => gainConstant * gainValue (Z + V + t • W)
  let g' : ℝ → ℝ := fun t => gainConstant * (cfc GainScalar.rate (Z + V + t • W) * W).trace
  have hfd (x : ℝ) (hx : 0 ≤ x) : HasDerivWithinAt f (f' x) (Set.Ici 0) x :=
    relativeMoment_derivative hV hW hx
  have hgd (x : ℝ) (hx : 0 ≤ x) : HasDerivWithinAt g (g' x) (Set.Ici 0) x :=
    (gainValue_derivative (hZ.add hV) hW hx).const_mul gainConstant
  have hbound : ∀ x ∈ Set.Ico 0 1, f x ≤ 1 → f' x ≤ g' x := by
    intro x hx hfx
    have hb := gain_derivative_bound hZ (hV.add (hW.smul hx.1)) hW hfx
    simpa only [f', g', add_assoc] using hb
  have hbud : ∀ x ∈ Set.Icc 0 1, f 0 + g x - g 0 ≤ 1 / 4 := by
    intro x hx
    have hm := gainValue_monotone (hZ.add hV) hW hx.1 (show (0 : ℝ) ≤ 1 by norm_num) hx.2
    simp only [one_smul] at hm
    have hc := mul_le_mul_of_nonneg_left hm gainConstant_pos.le
    dsimp only [f, g]
    simp only [zero_smul, add_zero]
    linarith
  have hf : ContinuousOn f (Set.Icc 0 1) := fun x hx =>
    (hfd x hx.1).continuousWithinAt.mono (fun _ hu => hu.1)
  have hg : ContinuousOn g (Set.Icc 0 1) := fun x hx =>
    (hgd x hx.1).continuousWithinAt.mono (fun _ hu => hu.1)
  have hc := EuclideanSteinitz.conditional_derivative_comparison hf hg
    (fun x hx => (hfd x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1))
    (fun x hx => (hgd x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1)) hbud hbound
    1 (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa only [f, g, zero_smul, one_smul, add_zero, sub_eq_add_neg, mul_add, mul_neg,
    add_assoc] using hc

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma relativeMoment_nonneg {S V : Matrix ι ι ℝ} (hV : V.PosSemidef) :
    0 ≤ relativeMoment S V := by
  apply Matrix.PosSemidef.trace_nonneg
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro x hx
  exact Real.rpow_nonneg (spectrum_nonneg_of_nonneg (sandwich_psd hV S).nonneg hx) _

lemma relativeMoment_zero (S : Matrix ι ι ℝ) : relativeMoment S 0 = 0 := by
  simp only [relativeMoment, Matrix.mul_zero, Matrix.zero_mul, cfc_apply_zero,
    Real.zero_rpow (ne_of_gt exponent_pos), map_zero, Matrix.trace_zero]

lemma relativeMoment_contraction {Z V C : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hV : V.PosSemidef) (hC : C * C.transpose ≤ 1) :
    relativeMoment (1 + C * Z * C.transpose) (C * V * C.transpose) ≤
      relativeMoment (1 + Z) V := by
  let S : Matrix ι ι ℝ := 1 + Z
  let Z' := C * Z * C.transpose
  let S' : Matrix ι ι ℝ := 1 + Z'
  let A := inverseSqrt S * V * inverseSqrt S
  let T := inverseSqrt S' * C * CFC.sqrt S
  have hS : S.PosDef := Matrix.PosDef.one.add_posSemidef hZ
  have hZ' : Z'.PosSemidef := by
    simpa only [Z', conjTranspose_eq_transpose_of_trivial] using hZ.mul_mul_conjTranspose_same C
  have hS' : S'.PosDef := Matrix.PosDef.one.add_posSemidef hZ'
  have hTt : T.transpose = CFC.sqrt S * C.transpose * inverseSqrt S' := by
    simp only [T, Matrix.transpose_mul, sqrt_transpose, inverseSqrt_transpose, Matrix.mul_assoc]
  have he : inverseSqrt S' * (C * V * C.transpose) * inverseSqrt S' = T * A * T.transpose := by
    rw [hTt]
    dsimp only [T, A]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt S), sqrt_mul_inverseSqrt hS, Matrix.one_mul]
    rw [← Matrix.mul_assoc (inverseSqrt S), inverseSqrt_mul_sqrt hS, Matrix.one_mul]
  have hCS : C * S * C.transpose ≤ S' := by
    simp only [S, S', Z', Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    exact add_le_add hC le_rfl
  have hTT : T * T.transpose ≤ 1 := by
    have hh := congruence_mono hCS (inverseSqrt S')
    rw [inverseSqrt_transpose, inverseSqrt_sandwich hS'] at hh
    convert! hh using 1
    rw [hTt]
    dsimp only [T]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt S), CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]
  have hb := Spectral.trace_rpow_contraction (sandwich_psd hV S) hTT
    (show (1 : ℝ) ≤ exponent by norm_num [exponent])
  unfold relativeMoment
  change (cfc (fun x : ℝ => x ^ exponent)
    (inverseSqrt S' * (C * V * C.transpose) * inverseSqrt S')).trace ≤ _
  rw [he]
  exact hb

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Move (ι : Type*) where
  contract : Matrix ι ι ℝ
  gain : Matrix ι ι ℝ

noncomputable def Move.old (p : Move ι) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  p.contract * M * p.contract.transpose

noncomputable def Move.next (p : Move ι) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := p.old M + p.gain

def Move.Admissible (p : Move ι) : Prop :=
  p.contract * p.contract.transpose ≤ 1 ∧ p.gain.PosSemidef

noncomputable def follow (Z V : Matrix ι ι ℝ) : List (Move ι) → Matrix ι ι ℝ × Matrix ι ι ℝ
  | [] => (Z, V)
  | p :: ps => follow (p.old Z) (p.next V) ps

noncomputable def gainCost (D : Matrix ι ι ℝ) : List (Move ι) → ℝ
  | [] => 0
  | p :: ps => gainValue (p.next D) - gainValue (p.old D) + gainCost (p.next D) ps

omit [DecidableEq ι] in
lemma Move.old_add (p : Move ι) (A B : Matrix ι ι ℝ) : p.old (A + B) = p.old A + p.old B := by
  simp only [Move.old, Matrix.mul_add, Matrix.add_mul]

omit [DecidableEq ι] in
lemma Move.old_psd (p : Move ι) {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (p.old A).PosSemidef := by
  simpa only [Move.old, conjTranspose_eq_transpose_of_trivial]
    using hA.mul_mul_conjTranspose_same p.contract

lemma Move.next_psd {p : Move ι} (hp : p.Admissible) {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (p.next A).PosSemidef := (p.old_psd hA).add hp.2

lemma Move.gain_nonneg {p : Move ι} (hp : p.Admissible) {D : Matrix ι ι ℝ} (hD : D.PosSemidef) :
    0 ≤ gainValue (p.next D) - gainValue (p.old D) := by
  have h := gainValue_monotone (p.old_psd hD) hp.2 (show (0 : ℝ) ≤ 0 by rfl)
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  simpa only [Move.next, zero_smul, one_smul, add_zero, sub_nonneg] using h

lemma gainCost_nonneg {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) : 0 ≤ gainCost D ps := by
  induction ps generalizing D with
  | nil => rfl
  | cons p ps ih =>
    have hpa := hp p (List.mem_cons_self ..)
    exact add_nonneg (p.gain_nonneg hpa hD)
      (ih (p.next_psd hpa hD) (fun q hq => hp q (List.mem_cons_of_mem p hq)))

lemma follow_psd {Z V : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (hV : V.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) :
    (follow Z V ps).1.PosSemidef ∧ (follow Z V ps).2.PosSemidef := by
  induction ps generalizing Z V with
  | nil => exact ⟨hZ, hV⟩
  | cons p ps ih =>
    exact ih (p.old_psd hZ) (p.next_psd (hp p (List.mem_cons_self ..)) hV)
      (fun q hq => hp q (List.mem_cons_of_mem p hq))

lemma relativeMoment_path {Z V : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (hV : V.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible)
    (hbudget : relativeMoment (1 + Z) V + gainConstant * gainCost (Z + V) ps ≤ 1 / 4) :
    relativeMoment (1 + (follow Z V ps).1) (follow Z V ps).2 ≤
      relativeMoment (1 + Z) V + gainConstant * gainCost (Z + V) ps := by
  induction ps generalizing Z V with
  | nil => simp only [follow, gainCost, mul_zero, add_zero, le_refl]
  | cons p ps ih =>
    have hpa := hp p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, q.Admissible := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hz := p.old_psd hZ
    have hv := p.old_psd hV
    have hnew := p.next_psd hpa hV
    have he : p.next (Z + V) = p.old Z + p.next V := by
      simp only [Move.next, p.old_add, add_assoc]
    have hc := relativeMoment_contraction hZ hV hpa.1
    change relativeMoment (1 + p.old Z) (p.old V) ≤ relativeMoment (1 + Z) V at hc
    have htail := gainCost_nonneg (p.next_psd hpa (hZ.add hV)) hps
    have hb : relativeMoment (1 + p.old Z) (p.old V) +
        gainConstant * (gainValue (p.old Z + p.old V + p.gain) - gainValue (p.old Z + p.old V)) ≤ 1 / 4 := by
      simp only [gainCost, Move.next, p.old_add] at hbudget htail
      nlinarith [gainConstant_pos]
    have hg := relativeMoment_gain hz hv hpa.2 hb
    change relativeMoment (1 + p.old Z) (p.next V) ≤ _ at hg
    simp only [Move.next] at hg
    have hbudget' : relativeMoment (1 + p.old Z) (p.next V) +
        gainConstant * gainCost (p.old Z + p.next V) ps ≤ 1 / 4 := by
      rw [← he]
      simp only [gainCost] at hbudget
      simp only [Move.next, p.old_add] at hbudget ⊢
      linarith
    have hi := ih hz hnew hps hbudget'
    change relativeMoment (1 + (follow (p.old Z) (p.next V) ps).1)
      (follow (p.old Z) (p.next V) ps).2 ≤ _
    rw [← he] at hi
    simp only [gainCost]
    simp only [Move.next, p.old_add] at hi hg ⊢
    linarith

end EuclideanSteinitz.Gain

end OAI
