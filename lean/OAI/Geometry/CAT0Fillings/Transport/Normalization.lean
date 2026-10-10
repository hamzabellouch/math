import Mathlib
import OAI.Geometry.CAT0Fillings.Bubble.Moments
import OAI.Geometry.CAT0Fillings.Transport.Integrals
import OAI.Geometry.CAT0Fillings.Transport.Cauchy

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma finite_transport_estimate {n : ℕ} {ω p q R D : ℝ} {f g : ℝ → ℝ} {K : ℝ≥0}
    (hR : 0 ≤ R) (hD : 0 < D) (hn : 2 ≤ n) (hω : 0 < ω)
    (hf : LipschitzWith K f) (hg : Continuous g) (hp : 0 < p) (hq : 1 ≤ q)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r, 0 < g r) (hfR : f R = 0)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D)
    (hexp : q+p/(n:ℝ)=p) (hexp2 : 2*(q-1)=p) :
    (n:ℝ)^2*(∫ s in (0:ℝ)..D,s^(n-1)*(g s)^q)^2 ≤
      q^2*(∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2)*
        (∫ s in (0:ℝ)..D,s^(n-1)*(g s)^p*s^2) := by
  have hn0 : 0 < n := by omega
  let t := radialTransport (f := f) hD.le hn0 hω hg hp (fun r _ => hgp r)
  have ht : Continuous t := radialTransport_continuous _ _ _ hf.continuous hg hp _
  have hz : Continuous (fun r => (f r)^(q-1)*t r) :=
    (hf.continuous.rpow_const (fun _ => Or.inr (sub_nonneg.mpr hq))).mul ht
  have hcs := weighted_interval_cs hR (continuous_id.pow (n-1)) hz hf
    (fun r hr => pow_nonneg hr.1 (n-1))
  have hI : (∫ r in (0:ℝ)..R,r^(n-1)*deriv f r*((f r)^(q-1)*t r)) =
      ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r := by
    apply intervalIntegral.integral_congr
    intro r hr
    ring
  have hM : (∫ r in (0:ℝ)..R,r^(n-1)*((f r)^(q-1)*t r)^2) =
      ∫ s in (0:ℝ)..D,s^(n-1)*(g s)^p*s^2 := by
    rw [radialTransport_integral_moment_unscaled hR hD hn0 hω hf.continuous hg hp hfp
      (fun r _ => hgp r) hmass (fun s => s^2)]
    apply intervalIntegral.integral_congr_Ioo_of_le hR
    intro r hr
    dsimp only
    rw [mul_pow,←Real.rpow_mul_natCast (hfp r hr).le]
    have he : (q-1)*(2:ℝ)=p := by linarith
    rw [Nat.cast_ofNat,he]
    ring
  dsimp only [Pi.pow_apply, id_eq] at hcs
  rw [hI,hM] at hcs
  have hibp := finite_transport_ibp hR hD hn hω hf hg hp hq hfp hgp hfR hmass hexp
  have hJ0 : 0 ≤ (n:ℝ)*(∫ s in (0:ℝ)..D,s^(n-1)*(g s)^q) := by
    apply mul_nonneg (Nat.cast_nonneg n)
    apply intervalIntegral.integral_nonneg hD.le
    intro s hs
    exact mul_nonneg (pow_nonneg hs.1 _) (Real.rpow_nonneg (hgp s).le _)
  have hsq := (sq_le_sq₀ hJ0 (hJ0.trans hibp)).mpr hibp
  have hsq' := mul_le_mul_of_nonneg_left hcs (sq_nonneg q)
  calc
    _ ≤ (-q*(∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r))^2 := by
      simpa only [mul_pow] using hsq
    _ = q^2*(∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r)^2 := by ring
    _ ≤ _ := by simpa only [mul_assoc] using hsq'

end CAT0Fillings.RadialSobolev
end

section

open Real Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma radial_integral_smul (n : ℕ) (p A D : ℝ) (g : ℝ → ℝ)
    (hA : 0 ≤ A) (hg : ∀ r, 0 ≤ g r) :
    (∫ r in (0:ℝ)..D,r^(n-1)*(A*g r)^p) =
      A^p*∫ r in (0:ℝ)..D,r^(n-1)*(g r)^p := by
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [Real.mul_rpow hA (hg r)]
  ring

lemma radial_second_moment_smul (n : ℕ) (p A D : ℝ) (g : ℝ → ℝ)
    (hA : 0 ≤ A) (hg : ∀ r, 0 ≤ g r) :
    (∫ r in (0:ℝ)..D,r^(n-1)*(A*g r)^p*r^2) =
      A^p*∫ r in (0:ℝ)..D,r^(n-1)*(g r)^p*r^2 := by
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [Real.mul_rpow hA (hg r)]
  ring

lemma radial_integral_pos {n : ℕ} {p R : ℝ} {f : ℝ → ℝ}
    (hn : 0 < n) (hp : 0 < p) (hR : 0 < R) (hf : Continuous f)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) :
    0 < ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^p := by
  have h := radialCDF_strictMonoOn (ω := 1) hn zero_lt_one hf hp hfp
    (show (0:ℝ) ∈ Icc 0 R from ⟨le_rfl,hR.le⟩) (show R ∈ Icc 0 R from ⟨hR.le,le_rfl⟩) hR
  rw [radialCDF_zero,radialCDF, mul_one] at h
  exact (mul_pos_iff.mp h).resolve_right (by rintro ⟨hneg,_⟩; exact (not_lt_of_ge (Nat.cast_nonneg _)) hneg) |>.2

lemma normalization_power {p F I : ℝ} (hp : 0 < p) (hF : 0 < F) (hI : 0 < I) :
    ((F/I)^(1/p))^p = F/I := by
  rw [←Real.rpow_mul (div_nonneg hF.le hI.le),one_div_mul_cancel hp.ne',Real.rpow_one]

lemma normalize_transport_estimate {n : ℕ} {R D : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hn : 2 < n) (hR : 0 < R) (hD : 0 < D) (hf : LipschitzWith K f)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hfR : f R = 0) :
    let F := ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n)
    let I := ∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)
    let J := ∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevQ n)
    let M := ∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)*r^2
    (n:ℝ)^2*J^2*(F/I)^(2/sobolevP n) ≤
      (sobolevQ n)^2*(∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2)*M := by
  dsimp only
  let F := ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n)
  let I := ∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)
  let A := (F/I)^(1/sobolevP n)
  have hs := sobolev_exponents hn
  have hF : 0 < F := radial_integral_pos (by omega) hs.1 hR hf.continuous hfp
  have hI : 0 < I := radial_integral_pos (by omega) hs.1 hD (bubble_continuous n) (fun r _ => bubble_pos n r)
  have hA : 0 < A := Real.rpow_pos_of_pos (div_pos hF hI) _
  have hAp : A^(sobolevP n) = F/I := normalization_power hs.1 hF hI
  have hm : radialCDF n 1 f (sobolevP n) R =
      radialCDF n 1 (fun r => A*bubble n r) (sobolevP n) D := by
    rw [radialCDF,radialCDF,radial_integral_smul n _ A D _ hA.le (fun r => (bubble_pos n r).le),hAp]
    change (n:ℝ)*1*F = (n:ℝ)*1*(F/I*I)
    rw [div_mul_cancel₀ _ hI.ne']
  have ht := finite_transport_estimate hR.le hD (by omega) zero_lt_one hf
    ((bubble_continuous n).const_mul A) hs.1 hs.2.1 hfp
    (fun r => mul_pos hA (bubble_pos n r)) hfR hm hs.2.2.1 hs.2.2.2.1
  rw [radial_integral_smul _ _ _ _ _ hA.le (fun r => (bubble_pos n r).le),
    radial_second_moment_smul _ _ _ _ _ hA.le (fun r => (bubble_pos n r).le),mul_pow] at ht
  have he : (A^(sobolevQ n))^2 = A^(sobolevP n)*A^2 := by
    rw [←Real.rpow_mul_natCast hA.le, ←Real.rpow_natCast, ←Real.rpow_add hA]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith [hs.2.2.2.2]
  have heA : A^2 = (F/I)^(2/sobolevP n) := by
    rw [←Real.rpow_mul_natCast (div_nonneg hF.le hI.le)]
    change (F/I)^((1/sobolevP n)*(2:ℝ)) = _
    congr 1
    ring
  rw [he] at ht
  have hout := (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hA (sobolevP n))).mp
    (show A^(sobolevP n)*((n:ℝ)^2*
      (∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevQ n))^2*A^2) ≤
      A^(sobolevP n)*((sobolevQ n)^2*(∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2)*
        (∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)*r^2)) by convert ht using 1 <;> first | rfl | ring)
  rwa [heA] at hout

end CAT0Fillings.RadialSobolev
end

end OAI
