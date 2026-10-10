import OAI.Analysis.Steinitz.Filter

namespace OAI

/-! Uniform dyadic scale-energy estimates. -/

namespace EuclideanSteinitz.Scale
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma size_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ sizeWeight x :=
  le_min (Real.rpow_nonneg hx _) (inv_nonneg.mpr hx)

lemma size_le_sqrt (x : ℝ) : sizeWeight x ≤ Real.sqrt x := by
  unfold sizeWeight
  rw [show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
  exact min_le_left _ _

lemma size_le_inv (x : ℝ) : sizeWeight x ≤ x⁻¹ := min_le_right _ _

lemma size_dyadic_nat {y : ℝ} (_hy : 0 ≤ y) (hy2 : y ≤ 2) (n : ℕ) :
    sizeWeight (y / (2 : ℝ) ^ n) ≤ 2 * (3 / 4 : ℝ) ^ n := by
  apply (size_le_sqrt _).trans
  have hn : (1 / 2 : ℝ) ^ n ≤ ((3 / 4 : ℝ) ^ 2) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hsq : y / (2 : ℝ) ^ n ≤ (2 * (3 / 4 : ℝ) ^ n) ^ 2 := by
    calc
      _ = y * (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow]; ring
      _ ≤ 4 * ((3 / 4 : ℝ) ^ 2) ^ n :=
        mul_le_mul (by linarith : y ≤ 4) hn (by positivity) (by norm_num)
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]; norm_num; ring
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hsq⟩

lemma size_dyadic_neg_nat {y : ℝ} (hy : 1 ≤ y) (n : ℕ) :
    sizeWeight (y / (2 : ℝ) ^ (-(n : ℤ))) ≤ 2 * (3 / 4 : ℝ) ^ n := by
  have hy0 : 0 < y := by linarith
  apply (size_le_inv _).trans
  have he : (y / (2 : ℝ) ^ (-(n : ℤ)))⁻¹ = y⁻¹ * (1 / 2 : ℝ) ^ n := by
    rw [_root_.zpow_neg, zpow_natCast, inv_div, div_eq_mul_inv, ← inv_pow]
    norm_num
    ring
  rw [he]
  have h₁ : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
  have h₂ : (1 / 2 : ℝ) ^ n ≤ (3 / 4 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h := mul_le_mul h₁ h₂ (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) n]

lemma size_normalized {y : ℝ} (hy : 1 ≤ y) (hy2 : y ≤ 2) (n : ℤ) :
    sizeWeight (y / (2 : ℝ) ^ n) ≤ 2 * (3 / 4 : ℝ) ^ n.natAbs := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [zpow_natCast, Int.natAbs_natCast] using size_dyadic_nat (by linarith) hy2 m
  · simpa only [Int.natAbs_neg, Int.natAbs_natCast] using size_dyadic_neg_nat hy m

lemma dyadic_normalize {x : ℝ} (hx : 0 < x) :
    ∃ k : ℤ, 1 ≤ x / (2 : ℝ) ^ k ∧ x / (2 : ℝ) ^ k ≤ 2 := by
  obtain ⟨k, hk, hk'⟩ := exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, (le_div_iff₀ (zpow_pos (by norm_num) k)).mpr (by simpa using hk), ?_⟩
  apply (div_le_iff₀ (zpow_pos (by norm_num) k)).mpr
  calc
    x ≤ (2 : ℝ) ^ (k + 1) := hk'.le
    _ = 2 * (2 : ℝ) ^ k := by rw [zpow_add_one₀ (by norm_num)]; ring

lemma size_shifted {x : ℝ} {k : ℤ} (hk : 1 ≤ x / (2 : ℝ) ^ k)
    (hk2 : x / (2 : ℝ) ^ k ≤ 2) (n : ℤ) :
    sizeWeight (x / (2 : ℝ) ^ n) ≤ 2 * (3 / 4 : ℝ) ^ (n - k).natAbs := by
  have he : x / (2 : ℝ) ^ n = (x / (2 : ℝ) ^ k) / (2 : ℝ) ^ (n - k) := by
    rw [zpow_sub₀ (by norm_num)]
    field_simp
  rw [he]
  exact size_normalized hk hk2 (n - k)

lemma hasSum_decay_nat : HasSum (fun n : ℕ => (3 / 4 : ℝ) ^ n) 4 := by
  have h := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)
  norm_num at h
  exact h

lemma hasSum_decay_neg :
    HasSum (fun n : ℕ => (3 / 4 : ℝ) ^ (-(n + 1 : ℤ)).natAbs) 3 := by
  have h := hasSum_decay_nat.mul_right (3 / 4 : ℝ)
  have he (n : ℕ) : (-(n + 1 : ℤ)).natAbs = n + 1 := by
    rw [Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add, Int.natAbs_natCast]
  simp only [he, pow_succ]
  norm_num at h
  exact h

lemma hasSum_decay : HasSum (fun n : ℤ => (3 / 4 : ℝ) ^ n.natAbs) 7 := by
  have h₁ : HasSum (fun n : ℕ => (3 / 4 : ℝ) ^ (n : ℤ).natAbs) 4 := by
    simpa only [Int.natAbs_natCast] using hasSum_decay_nat
  have h : HasSum (fun n : ℤ => (3 / 4 : ℝ) ^ n.natAbs) (4 + 3) :=
    HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => (3 / 4 : ℝ) ^ n.natAbs) h₁ hasSum_decay_neg
  norm_num at h
  exact h

lemma sum_decay_shift (S : Finset ℤ) (k : ℤ) :
    (∑ n ∈ S, (3 / 4 : ℝ) ^ (n - k).natAbs) ≤ 7 := by
  have hs : Summable (fun n : ℤ => (3 / 4 : ℝ) ^ (n - k).natAbs) :=
    hasSum_decay.summable.comp_injective (Equiv.subRight k).injective
  calc
    _ ≤ ∑' n : ℤ, (3 / 4 : ℝ) ^ (n - k).natAbs :=
      hs.sum_le_tsum S (fun _ _ => by positivity)
    _ = ∑' n : ℤ, (3 / 4 : ℝ) ^ n.natAbs :=
      by simpa only [Equiv.subRight_apply] using
        (Equiv.subRight k).tsum_eq (fun n : ℤ => (3 / 4 : ℝ) ^ n.natAbs)
    _ = 7 := hasSum_decay.tsum_eq

lemma sum_size_dyadic (S : Finset ℤ) {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ S, sizeWeight (x / (2 : ℝ) ^ n)) ≤ 14 := by
  obtain ⟨k, hk, hk2⟩ := dyadic_normalize hx
  calc
    _ ≤ ∑ n ∈ S, 2 * (3 / 4 : ℝ) ^ (n - k).natAbs :=
      Finset.sum_le_sum fun n _ => size_shifted hk hk2 n
    _ = 2 * ∑ n ∈ S, (3 / 4 : ℝ) ^ (n - k).natAbs := (Finset.mul_sum ..).symm
    _ ≤ 2 * 7 := mul_le_mul_of_nonneg_left (sum_decay_shift S k) (by norm_num)
    _ = 14 := by norm_num

lemma potential_rate_le_size {x : ℝ} (hx : 0 ≤ x) :
    PotentialScalar.rate x ≤ sizeWeight x := by
  by_cases h1 : x ≤ 1
  · rw [PotentialScalar.rate_small h1, PotentialScalar.sizeWeight_small hx h1]
  · have h1' : 1 ≤ x := le_of_lt (lt_of_not_ge h1)
    rw [PotentialScalar.rate_large h1', PotentialScalar.sizeWeight_large h1']
    have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx
    have hi1 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1'
    nlinarith

lemma gain_rate_le_size {x : ℝ} (hx : 0 ≤ x) :
    GainScalar.rate x ≤ sizeWeight x := by
  have hd : 0 < (1 + x) * Real.sqrt (1 + x) := by positivity
  apply le_min
  · rw [show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
    unfold GainScalar.rate
    apply (div_le_iff₀ hd).mpr
    have hs : 1 ≤ Real.sqrt (1 + x) := Real.one_le_sqrt.mpr (by linarith)
    have hm : 1 ≤ (1 + x) * Real.sqrt (1 + x) := by
      have h := mul_le_mul (by linarith : (1 : ℝ) ≤ 1 + x) hs
        (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 1 + x)
      simpa only [one_mul] using h
    nlinarith [Real.sqrt_nonneg x]
  · by_cases hx0 : x = 0
    · simp [hx0, GainScalar.rate]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      unfold GainScalar.rate
      apply (div_le_iff₀ hd).mpr
      apply (le_inv_mul_iff₀ hxpos).mpr
      calc
        x * Real.sqrt x ≤ (1 + x) * Real.sqrt (1 + x) :=
          mul_le_mul (by linarith) (Real.sqrt_le_sqrt (by linarith))
            (Real.sqrt_nonneg _) (by positivity)

lemma sum_rates_dyadic (S : Finset ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ S, (PotentialScalar.rate (x / (2 : ℝ) ^ n) +
      GainScalar.extendedRate (x / (2 : ℝ) ^ n))) ≤ 28 := by
  by_cases hx0 : x = 0
  · simp [hx0, PotentialScalar.rate_zero_of_nonpos (le_refl (0 : ℝ)),
      GainScalar.extendedRate, GainScalar.rate]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  calc
    _ ≤ ∑ n ∈ S, 2 * sizeWeight (x / (2 : ℝ) ^ n) := by
      apply Finset.sum_le_sum
      intro n _
      have hn : 0 ≤ x / (2 : ℝ) ^ n := by positivity
      rw [GainScalar.extendedRate_eq hn]
      linarith [potential_rate_le_size hn, gain_rate_le_size hn]
    _ = 2 * ∑ n ∈ S, sizeWeight (x / (2 : ℝ) ^ n) := (Finset.mul_sum ..).symm
    _ ≤ 2 * 14 := mul_le_mul_of_nonneg_left (sum_size_dyadic S hxpos) (by norm_num)
    _ = 28 := by norm_num

end EuclideanSteinitz.Scale

namespace EuclideanSteinitz.ScaleMatrix
open Matrix MatrixEnergy Gain Energy Spectral
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def primitiveTrace (A : Matrix ι ι ℝ) : ℝ :=
  (cfc PotentialScalar.primitive A).trace + (cfc GainScalar.primitive A).trace

noncomputable def rateMatrix (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  cfc PotentialScalar.rate A + cfc GainScalar.extendedRate A

noncomputable def scaleTrace (S : Finset ℤ) (A : Matrix ι ι ℝ) : ℝ :=
  ∑ n ∈ S, (2 : ℝ) ^ n * primitiveTrace (((2 : ℝ) ^ n)⁻¹ • A)

noncomputable def scaleRate (S : Finset ℤ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑ n ∈ S, rateMatrix (((2 : ℝ) ^ n)⁻¹ • A)

lemma primitiveTrace_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    primitiveTrace A = hTrace A := by
  unfold primitiveTrace hTrace pTrace gainValue
  rw [Spectral.cfc_primitive_eq hA]
  congr 1
  congr 1
  apply cfc_congr
  intro x hx
  exact GainScalar.primitive_eq (spectrum_nonneg_of_nonneg hA.nonneg hx)

lemma primitiveTrace_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (fun u : ℝ => primitiveTrace (A + u • H))
      (rateMatrix (A + t • H) * H).trace t := by
  have hp := trace_semiconvex_affine_derivative hA hH PotentialScalar.primitive
    PotentialScalar.rate PotentialScalar.continuous_rate PotentialScalar.primitive_derivative
    PotentialScalar.convexified_convex t
  have hg := trace_semiconvex_affine_derivative hA hH GainScalar.primitive
    GainScalar.extendedRate GainScalar.continuous_extendedRate GainScalar.primitive_derivative
    GainScalar.convexified_convex t
  simpa only [primitiveTrace, rateMatrix, Matrix.add_mul, trace_add] using hp.fun_add hg

lemma rateMatrix_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (n : ℤ) :
    rateMatrix (((2 : ℝ) ^ n)⁻¹ • A) =
      cfc (fun x : ℝ => PotentialScalar.rate (x / (2 : ℝ) ^ n) +
        GainScalar.extendedRate (x / (2 : ℝ) ^ n)) A := by
  let f : ℝ → ℝ := fun x => PotentialScalar.rate x + GainScalar.extendedRate x
  have hf : Continuous f := PotentialScalar.continuous_rate.add GainScalar.continuous_extendedRate
  have he : cfc (fun x : ℝ => x / (2 : ℝ) ^ n) A = ((2 : ℝ) ^ n)⁻¹ • A := by
    simp only [div_eq_mul_inv, mul_comm _ (((2 : ℝ) ^ n)⁻¹)]
    rw [cfc_const_mul (((2 : ℝ) ^ n)⁻¹) (fun x : ℝ => x) A continuousOn_id,
      cfc_id' ℝ A hA.isSelfAdjoint]
  have hc := cfc_comp f (fun x : ℝ => x / (2 : ℝ) ^ n) A hA.isSelfAdjoint
    hf.continuousOn (by fun_prop)
  rw [he] at hc
  unfold rateMatrix
  rw [← cfc_add _ PotentialScalar.rate GainScalar.extendedRate
    PotentialScalar.continuous_rate.continuousOn GainScalar.continuous_extendedRate.continuousOn]
  exact hc.symm

lemma scaleRate_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (S : Finset ℤ) :
    scaleRate S A = cfc (fun x : ℝ => ∑ n ∈ S,
      (PotentialScalar.rate (x / (2 : ℝ) ^ n) +
        GainScalar.extendedRate (x / (2 : ℝ) ^ n))) A := by
  unfold scaleRate
  simp_rw [rateMatrix_cfc hA]
  symm
  have he : (fun x : ℝ => ∑ n ∈ S, (PotentialScalar.rate (x / (2 : ℝ) ^ n) +
      GainScalar.extendedRate (x / (2 : ℝ) ^ n))) = ∑ n ∈ S,
      (fun x : ℝ => PotentialScalar.rate (x / (2 : ℝ) ^ n) +
        GainScalar.extendedRate (x / (2 : ℝ) ^ n)) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact cfc_sum _ A S (fun _ _ => finite_spectrum_continuous _ _)

lemma scaleRate_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (S : Finset ℤ) :
    scaleRate S A ≤ (28 : ℝ) • (1 : Matrix ι ι ℝ) := by
  rw [scaleRate_cfc hA.1]
  let f : ℝ → ℝ := fun x => ∑ n ∈ S,
    (PotentialScalar.rate (x / (2 : ℝ) ^ n) +
      GainScalar.extendedRate (x / (2 : ℝ) ^ n))
  have hb : 0 ≤ cfc (fun x : ℝ => 28 - f x) A := by
    apply cfc_nonneg
    intro x hx
    exact sub_nonneg.mpr (Scale.sum_rates_dyadic S (spectrum_nonneg_of_nonneg hA.nonneg hx))
  rw [cfc_sub (fun _ : ℝ => 28) f A continuousOn_const (finite_spectrum_continuous _ _),
    cfc_const (28 : ℝ) A hA.1.isSelfAdjoint, Algebra.algebraMap_eq_smul_one] at hb
  exact sub_nonneg.mp hb

lemma scaleTrace_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (S : Finset ℤ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => scaleTrace S (A + u • H))
      (scaleRate S (A + t • H) * H).trace t := by
  have hi (n : ℤ) : HasDerivAt
      (fun u : ℝ => (2 : ℝ) ^ n * primitiveTrace (((2 : ℝ) ^ n)⁻¹ • (A + u • H)))
      (rateMatrix (((2 : ℝ) ^ n)⁻¹ • (A + t • H)) * H).trace t := by
    have hd := (primitiveTrace_derivative (hA.smul (IsSelfAdjoint.all (((2 : ℝ) ^ n)⁻¹)))
      (hH.smul (IsSelfAdjoint.all (((2 : ℝ) ^ n)⁻¹))) t).const_mul ((2 : ℝ) ^ n)
    have he (u : ℝ) : ((2 : ℝ) ^ n)⁻¹ • (A + u • H) =
        ((2 : ℝ) ^ n)⁻¹ • A + u • (((2 : ℝ) ^ n)⁻¹ • H) := by
      simp only [smul_add, smul_smul, mul_comm]
    simp_rw [he]
    convert! hd using 1
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt (zpow_pos (by norm_num) n)), one_mul]
  have hs := HasDerivAt.sum (u := S) (fun n _ => hi n)
  convert! hs using 1
  · ext u
    simp only [scaleTrace, Finset.sum_apply]
  · simp only [scaleRate, Matrix.sum_mul, trace_sum]

lemma scaleTrace_mono_bound {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hAB : A ≤ B) (S : Finset ℤ) :
    scaleTrace S B - scaleTrace S A ≤ 28 * (B.trace - A.trace) := by
  have hH : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hd (t : ℝ) := scaleTrace_derivative hA.1 hH.1 S t
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      deriv (fun u : ℝ => scaleTrace S (A + u • (B - A))) t ≤ 28 * (B - A).trace := by
    rw [(hd t).deriv]
    have h := trace_mul_mono_right (scaleRate_le (hA.add (hH.smul ht.1)) S) hH
    simpa only [Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul] using h
  have hi := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun t ht => hb t (interior_subset ht)) 0 (by simp) 1 (by simp) (by norm_num)
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel, sub_zero, mul_one, trace_sub] using hi

lemma cfc_scaled {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) (c : ℝ) :
    cfc f (c • A) = cfc (fun x : ℝ => f (c * x)) A := by
  have he : cfc (fun x : ℝ => c * x) A = c • A := by
    rw [cfc_const_mul c (fun x : ℝ => x) A continuousOn_id, cfc_id' ℝ A hA.isSelfAdjoint]
  have hc := cfc_comp f (fun x : ℝ => c * x) A hA.isSelfAdjoint
    ((A.finite_real_spectrum.image _).continuousOn f) (by fun_prop)
  rw [he] at hc
  exact hc.symm

lemma scaleTrace_charpoly {A B : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A.charpoly = B.charpoly) (S : Finset ℤ) :
    scaleTrace S A = scaleTrace S B := by
  unfold scaleTrace
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  unfold primitiveTrace
  rw [cfc_scaled hA, cfc_scaled hA, cfc_scaled hB, cfc_scaled hB]
  rw [trace_cfc_eq_of_charpoly hA hB hAB, trace_cfc_eq_of_charpoly hA hB hAB]

lemma trace_charpoly {A B : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rw [trace_spectral hA, trace_spectral hB,
    (hA.eigenvalues_eq_eigenvalues_iff hB).mpr hAB]

lemma scaleTrace_contraction_bound {A C : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hC : C * C.transpose ≤ 1) (T : Finset ℤ) :
    scaleTrace T A - scaleTrace T (C * A * C.transpose) ≤
      28 * (A.trace - (C * A * C.transpose).trace) := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSS : S * S = A := by simpa only [← sq] using CFC.sq_sqrt A hA.nonneg
  have hCA : (C * A * C.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same C
  have hSC : (S * (C.transpose * C) * S).PosSemidef := by
    have hp : (C.transpose * C).PosSemidef := by
      simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
        (star_mul_self_nonneg C : (0 : Matrix ι ι ℝ) ≤ star C * C).posSemidef
    simpa only [hS.eq] using hp.conjTranspose_mul_mul_same S
  have hle : S * (C.transpose * C) * S ≤ A := by
    have hp := (Matrix.le_iff.mp (transpose_contraction hC)).conjTranspose_mul_mul_same S
    rw [hS.eq] at hp
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS] using hp
  have heq : (C * A * C.transpose).charpoly = (S * (C.transpose * C) * S).charpoly := by
    rw [← hSS]
    convert! charpoly_mul_comm (C * S) (S * C.transpose) using 1 <;> simp only [Matrix.mul_assoc]
  rw [scaleTrace_charpoly hCA.1 hSC.1 heq, trace_charpoly hCA.1 hSC.1 heq]
  exact scaleTrace_mono_bound hSC hle T

lemma scaleTrace_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (S : Finset ℤ) :
    scaleTrace S A = ∑ n ∈ S, (2 : ℝ) ^ n * hTrace (((2 : ℝ) ^ n)⁻¹ • A) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [primitiveTrace_eq (hA.smul (by positivity))]

end EuclideanSteinitz.ScaleMatrix

namespace EuclideanSteinitz.ScaleEnergy
open Matrix MatrixEnergy Gain Energy ScaleMatrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rescale (c : ℝ) (p : Move ι) : Move ι := ⟨p.contract, c • p.gain⟩

omit [DecidableEq ι] in
lemma rescale_old (c : ℝ) (p : Move ι) (A : Matrix ι ι ℝ) :
    (rescale c p).old (c • A) = c • p.old A := by
  simp only [rescale, Move.old, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq ι] in
lemma rescale_next (c : ℝ) (p : Move ι) (A : Matrix ι ι ℝ) :
    (rescale c p).next (c • A) = c • p.next A := by
  change (rescale c p).old (c • A) + c • p.gain = c • (p.old A + p.gain)
  rw [rescale_old, smul_add]

noncomputable def aggregateCost (S : Finset ℤ) (A : Matrix ι ι ℝ) : List (Move ι) → ℝ
  | [] => 0
  | p :: ps => scaleTrace S A - scaleTrace S (p.old A) + scaleTrace S (p.next A) -
      scaleTrace S (p.old A) + aggregateCost S (p.next A) ps

noncomputable def variation (A : Matrix ι ι ℝ) : List (Move ι) → ℝ
  | [] => 0
  | p :: ps => A.trace - (p.old A).trace + (p.next A).trace -
      (p.old A).trace + variation (p.next A) ps

noncomputable def gainSum (ps : List (Move ι)) : ℝ := (ps.map (fun p => p.gain.trace)).sum

lemma aggregateCost_le_variation {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) (S : Finset ℤ) :
    aggregateCost S A ps ≤ 28 * variation A ps := by
  induction ps generalizing A with
  | nil => simp [aggregateCost, variation]
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    have h₁ := scaleTrace_contraction_bound hA hp₀.1 S
    have h₂ := scaleTrace_mono_bound (p.old_psd hA) (Energy.Move.old_le_next hp₀ A) S
    have ht := ih (p.next_psd hp₀ hA) (fun q hq => hp q (List.mem_cons_of_mem p hq))
    change _ ≤ 28 * (_ + variation (p.next A) ps)
    dsimp only [aggregateCost]
    change scaleTrace S A - scaleTrace S (p.old A) ≤ 28 * (A.trace - (p.old A).trace) at h₁
    linarith

omit [DecidableEq ι] in
lemma variation_eq (A : Matrix ι ι ℝ) (ps : List (Move ι)) :
    variation A ps = A.trace + 2 * gainSum ps - (finish A ps).trace := by
  induction ps generalizing A with
  | nil => simp [variation, gainSum, finish]
  | cons p ps ih =>
    simp only [variation, gainSum, List.map_cons, List.sum_cons, finish, ih]
    rw [show (p.next A).trace = (p.old A).trace + p.gain.trace by
      simp only [Move.next, trace_add]]
    ring

lemma finish_psd {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) : (finish A ps).PosSemidef := by
  induction ps generalizing A with
  | nil => exact hA
  | cons p ps ih =>
    exact ih (p.next_psd (hp p (List.mem_cons_self ..)) hA)
      (fun q hq => hp q (List.mem_cons_of_mem p hq))

lemma variation_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) :
    variation A ps ≤ A.trace + 2 * gainSum ps := by
  rw [variation_eq]
  exact sub_le_self _ (finish_psd hA hp).trace_nonneg

lemma sum_stepCost_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {p : Move ι} (hp : p.Admissible) (S : Finset ℤ) :
    (∑ n ∈ S, (2 : ℝ) ^ n * stepCost (rescale (((2 : ℝ) ^ n)⁻¹) p)
      (((2 : ℝ) ^ n)⁻¹ • A)) =
      scaleTrace S A - scaleTrace S (p.old A) + scaleTrace S (p.next A) - scaleTrace S (p.old A) := by
  rw [scaleTrace_eq hA, scaleTrace_eq (p.old_psd hA), scaleTrace_eq (p.next_psd hp hA)]
  simp only [stepCost, rescale_old, rescale_next, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma aggregateCost_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) (S : Finset ℤ) :
    aggregateCost S A ps = ∑ n ∈ S, (2 : ℝ) ^ n *
      cost (((2 : ℝ) ^ n)⁻¹ • A) (ps.map (rescale (((2 : ℝ) ^ n)⁻¹))) := by
  induction ps generalizing A with
  | nil => simp [aggregateCost, cost]
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    simp only [List.map_cons, cost, rescale_next, mul_add, Finset.sum_add_distrib]
    rw [sum_stepCost_eq hA hp₀, ← ih (p.next_psd hp₀ hA)
      (fun q hq => hp q (List.mem_cons_of_mem p hq))]
    rfl

lemma scale_energy_bound {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) (S : Finset ℤ) :
    (∑ n ∈ S, (2 : ℝ) ^ n *
      cost (((2 : ℝ) ^ n)⁻¹ • A) (ps.map (rescale (((2 : ℝ) ^ n)⁻¹)))) ≤
      28 * (A.trace + 2 * gainSum ps) := by
  rw [← aggregateCost_eq hA hp]
  exact (aggregateCost_le_variation hA hp S).trans
    (mul_le_mul_of_nonneg_left (variation_le hA hp) (by norm_num))

end EuclideanSteinitz.ScaleEnergy

end OAI
