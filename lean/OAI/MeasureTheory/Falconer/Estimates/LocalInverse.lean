import OAI.MeasureTheory.Falconer.Fourier.MaskedStationaryJets

namespace OAI

/-! # Finite inverse amplitudes built from the actual local jets

Each recursive amplitude is globally smooth and supported in the same fixed
pole patch. The diagonal cancellation is pointwise on the prepared inner
patch and does not assume a spherical differential-operator identity.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def localInverseAmplitude (m : ℕ) (B : Space (m+3) → ℂ) :
    ℕ → Space (m+3) → ℂ
  | 0 => fun x => (sphereStationaryConstant (m+2))⁻¹ * (stationaryPatchMask m x : ℂ) * B x
  | j+1 => fun x => -(sphereStationaryConstant (m+2))⁻¹ *
      ∑ h ∈ Finset.range (j+1),
        maskedStationaryCoefficient m (h+1) (localInverseAmplitude m B (j-h)) x
termination_by j => j
decreasing_by omega

theorem localInverseAmplitude_contDiff (m : ℕ) {B : Space (m+3) → ℂ}
    (hB : ContDiff ℝ ∞ B) (j : ℕ) : ContDiff ℝ ∞ (localInverseAmplitude m B j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      simp only [localInverseAmplitude]
      exact (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m))).mul hB
    | succ j =>
      rw [localInverseAmplitude]
      apply contDiff_const.mul
      exact ContDiff.sum (fun h _ => maskedStationaryCoefficient_contDiff m (h+1)
        (ih (j-h) (by omega)))

theorem localInverseAmplitude_zero_of_mask_zero (m j : ℕ) (B : Space (m+3) → ℂ)
    (x : Space (m+3)) (hx : stationaryPatchMask m x = 0) :
    localInverseAmplitude m B j x = 0 := by
  cases j with
  | zero => simp only [localInverseAmplitude,hx,Complex.ofReal_zero,mul_zero,zero_mul]
  | succ j =>
    simp only [localInverseAmplitude,maskedStationaryCoefficient,hx,Complex.ofReal_zero,
      zero_mul,Finset.sum_const_zero,mul_zero]

theorem localInverseAmplitude_tsupport (m j : ℕ) (B : Space (m+3) → ℂ) :
    tsupport (localInverseAmplitude m B j) ⊆ tsupport (stationaryPatchMask m) := by
  apply closure_mono
  intro x hx hzero
  exact hx (localInverseAmplitude_zero_of_mask_zero m j B x hzero)

theorem localInverseAmplitude_cancellation (m k : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) (he : stationaryPatchMask m e = 1) :
    (∑ h ∈ Finset.range (k+1), actualStationaryCoefficient m h
      (localInverseAmplitude m B (k-h)) e) = if k = 0 then B e else 0 := by
  have hc := sphereStationaryConstant_ne_zero (m+2)
  cases k with
  | zero =>
    simp only [Nat.zero_add,Finset.sum_range_one,Nat.sub_self,
      actualStationaryCoefficient_zero,localInverseAmplitude,he,
      Complex.ofReal_one,mul_one,↓reduceIte]
    rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul]
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,actualStationaryCoefficient_zero,
      localInverseAmplitude,maskedStationaryCoefficient,he,Complex.ofReal_one,
      one_mul,Nat.succ_ne_zero,↓reduceIte]
    rw [← mul_assoc,mul_neg,mul_inv_cancel₀ hc,neg_one_mul]
    exact add_neg_cancel _

theorem localInverseAmplitude_cancellation_reverse (m k : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) (he : stationaryPatchMask m e = 1) :
    (∑ h ∈ Finset.range (k+1), actualStationaryCoefficient m (k-h)
      (localInverseAmplitude m B h) e) = if k = 0 then B e else 0 := by
  rw [← localInverseAmplitude_cancellation m k B e he,
    ← Finset.sum_range_reflect (fun h => actualStationaryCoefficient m h
      (localInverseAmplitude m B (k-h)) e) (k+1)]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' : h ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  simp [Nat.sub_sub_self hh']

theorem localInverseAmplitude_triangle (m J : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) (he : stationaryPatchMask m e = 1) (t : ℂ) :
    (∑ j ∈ Finset.range (J+1), t^j *
      ∑ h ∈ Finset.range (J+1-j), t^h * actualStationaryCoefficient m h
        (localInverseAmplitude m B j) e) = B e := by
  have hid : (∑ j ∈ Finset.range (J+1), ∑ h ∈ Finset.range (J+1-j),
      t^(j+h)*actualStationaryCoefficient m h (localInverseAmplitude m B j) e) = B e := by
    rw [← Finset.sum_range_diag_flip]
    have hh : ∀ k ∈ Finset.range (J+1),
        (∑ j ∈ Finset.range (k+1), t^(j+(k-j))*
          actualStationaryCoefficient m (k-j) (localInverseAmplitude m B j) e) =
            t^k*(if k = 0 then B e else 0) := by
      intro k _
      rw [← localInverseAmplitude_cancellation_reverse m k B e he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [Nat.add_sub_of_le hj']
    rw [Finset.sum_congr rfl hh]
    simp
  rw [← hid]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [pow_add,mul_assoc]

end Falconer

end OAI
