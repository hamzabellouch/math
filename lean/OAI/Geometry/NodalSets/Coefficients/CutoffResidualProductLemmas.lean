import OAI.Geometry.NodalSets.Coefficients.ResidualProduct

namespace OAI

noncomputable section

namespace Yau.Jets

open scoped ContDiff

theorem cutoff_residual_times_exponential_bound (k0 : ℕ) : ∃ B > 0,
    ∀ (phi f : Coord → ℂ), ContDiff ℝ ∞ phi → ContDiff ℝ ∞ f →
    ∀ (x y : Coord) (C D N K S : ℝ), 0 ≤ C → 1 ≤ D → 1 ≤ N →
    DerivativeBound k0 f x (C * N ^ (-K-k0)) →
    DerivativeBound k0 phi x D → (phi x).re ≤ S →
    ‖iteratedFDeriv ℝ k0 (fun z ↦ Yau.Waves.scaledCutoff N y z •
      (f z * waveExp phi N z)) x‖ ≤
      B * C * (k0.factorial : ℝ) * D ^ k0 * N ^ (-K) * Real.exp (N*S) := by
  obtain ⟨B, hB, hcut⟩ := Yau.Waves.cutoff_preserves_derivative_exponent (E := Coord) (F := ℂ) k0
  refine ⟨2^k0*B*2^k0, by positivity, ?_⟩
  intro phi f hp hf x y C D N K S hC hD hN hcore hphase hgap
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let Q := (k0.factorial : ℝ) * D ^ k0
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have he (j : ℕ) (hj : j ≤ k0) :
      ‖iteratedFDeriv ℝ j (waveExp phi N) x‖ ≤ Q * N ^ j * Real.exp (N*S) := by
    apply (waveExp_derivative_bound hp j x hD hN
      (fun i _ hi ↦ hphase i (hi.trans hj))).trans
    have hfact : (j.factorial : ℝ) ≤ k0.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpow : D ^ j ≤ D ^ k0 := pow_le_pow_right₀ hD hj
    have hexp : Real.exp (N*(phi x).re) ≤ Real.exp (N*S) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgap hNp.le)
    dsimp [Q]
    gcongr
  have hau (j : ℕ) (hj : j ≤ k0) :
      ‖iteratedFDeriv ℝ j (fun z ↦ f z * waveExp phi N z) x‖ ≤
      (2^k0 * (C * N ^ (-K-k0)) * Q) * N ^ j * Real.exp (N*S) := by
    apply (mul_derivative_power_bound hf (waveExp_contDiff hp N) j x
      (by positivity : 0 ≤ C * N ^ (-K-k0)) hNp.le _
      (fun i hi ↦ he i (hi.trans hj))).trans
    · have hjpow : (2:ℝ)^j ≤ 2^k0 := pow_le_pow_right₀ (by norm_num) hj
      gcongr
    · intro i hi
      exact (hcore i (hi.trans hj)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hN))
  have h := hcut N hN y x (fun z ↦ f z * waveExp phi N z)
    (hf.mul (waveExp_contDiff hp N)) (2^k0*(C*N^(-K-k0))*Q) (Real.exp (N*S))
    (by positivity) (Real.exp_pos _).le hau
  have hpow : N ^ (-K) = N ^ (-K-k0) * N ^ k0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNp]
    congr 1
    ring
  convert h using 1
  rw [hpow]
  dsimp [Q]
  ring

def finiteResidualCore (E a t0 : Coord → ℂ) (tj : ℕ → Coord → ℂ)
    (L : Coord → ℂ) (J : ℕ) (N : ℝ) : Coord → ℂ := fun x ↦
  (N : ℂ)^2 * (E x * a x) + (N : ℂ) * t0 x +
    (∑ j ∈ Finset.range J, ((N : ℂ)⁻¹^j) * tj j x) + ((N : ℂ)⁻¹^J) * L x

lemma finiteResidualCore_contDiff {E a t0 : Coord → ℂ} {tj : ℕ → Coord → ℂ}
    {L : Coord → ℂ} (hE : ContDiff ℝ ∞ E) (ha : ContDiff ℝ ∞ a)
    (ht0 : ContDiff ℝ ∞ t0) (htj : ∀ j, ContDiff ℝ ∞ (tj j))
    (hL : ContDiff ℝ ∞ L) (J : ℕ) (N : ℝ) :
    ContDiff ℝ ∞ (finiteResidualCore E a t0 tj L J N) :=
  (((contDiff_const.mul (hE.mul ha)).add (contDiff_const.mul ht0)).add
    (ContDiff.sum (fun j _ ↦ contDiff_const.mul (htj j)))).add (contDiff_const.mul hL)

theorem finiteResidualCore_bound {E a t0 : Coord → ℂ} {tj : ℕ → Coord → ℂ}
    {L : Coord → ℂ} (hE : ContDiff ℝ ∞ E) (ha : ContDiff ℝ ∞ a)
    (ht0 : ContDiff ℝ ∞ t0) (htj : ∀ j, ContDiff ℝ ∞ (tj j))
    (hL : ContDiff ℝ ∞ L) (k J : ℕ) (x : Coord) {K C A N : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hN : 1 ≤ N) (hJ : K+k ≤ J)
    (hEb : DerivativeBound k E x (C * N ^ (-K-k-2)))
    (hab : DerivativeBound k a x A)
    (ht0b : DerivativeBound k t0 x (C * N ^ (-K-k-2)))
    (htjb : ∀ j, j < J → DerivativeBound k (tj j) x (C * N ^ (-K-k-2)))
    (hLb : DerivativeBound k L x C) :
    DerivativeBound k (finiteResidualCore E a t0 tj L J N) x
      ((2^k*C*A + (J+2)*C) * N ^ (-K-k)) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hea : DerivativeBound k (fun z ↦ E z * a z) x
      ((2^k*C*A) * N ^ (-K-k-2)) := by
    convert hEb.mul hE ha (by positivity) hA hab using 1
    ring
  have hlead : DerivativeBound k (fun z ↦ (N:ℂ)^2 * (E z * a z)) x
      ((2^k*C*A) * N ^ (-K-k)) := by
    have h := hea.scale_power (hE.mul ha) (by positivity) hNp ((N:ℂ)^2)
      (q := 2) (by simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp])
    convert h using 1
    congr 2
    ring
  have htfirst : DerivativeBound k (fun z ↦ (N:ℂ) * t0 z) x (C * N ^ (-K-k)) := by
    apply (ht0b.scale_power ht0 hC hNp (N:ℂ) (q := 1)
      (by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp])).exponent_mono hC hN
    linarith
  have htlater (j : ℕ) (hj : j < J) :
      DerivativeBound k (fun z ↦ ((N:ℂ)⁻¹^j) * tj j z) x (C * N ^ (-K-k)) := by
    apply ((htjb j hj).scale_power (htj j) hC hNp ((N:ℂ)⁻¹^j)
      (le_of_eq (norm_complex_inv_pow hNp j))).exponent_mono hC hN
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hlast : DerivativeBound k (fun z ↦ ((N:ℂ)⁻¹^J) * L z) x (C * N ^ (-K-k)) := by
    have hLb' : DerivativeBound k L x (C * N^ (0:ℝ)) := by simpa using hLb
    apply (hLb'.scale_power hL hC hNp ((N:ℂ)⁻¹^J)
      (le_of_eq (norm_complex_inv_pow hNp J))).exponent_mono hC hN
    linarith
  have hsum := DerivativeBound.sum (Finset.range J)
    (fun j _ ↦ contDiff_const.mul (htj j)) (fun j hj ↦ htlater j (Finset.mem_range.mp hj))
  have h := ((hlead.add (contDiff_const.mul (hE.mul ha)) (contDiff_const.mul ht0) htfirst).add
    ((contDiff_const.mul (hE.mul ha)).add (contDiff_const.mul ht0))
    (ContDiff.sum (fun j _ ↦ contDiff_const.mul (htj j))) hsum).add
    (((contDiff_const.mul (hE.mul ha)).add (contDiff_const.mul ht0)).add
      (ContDiff.sum (fun j _ ↦ contDiff_const.mul (htj j)))) (contDiff_const.mul hL) hlast
  apply h.enlarge
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by ring)

end Yau.Jets

end

end OAI
