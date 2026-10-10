import OAI.NumberTheory.TwoPoint.Halasz.HalaszRootScale

namespace OAI

/-! The classical step in the power-bound form used by iteration. -/
namespace TwoPointCorrelations

def halaszStepExponent (s k : ℕ) : ℕ := 2*s+k*(k-1)/2

theorem halasz_normalize_classical_bound {s k N R : ℕ} {A e : ℝ}
    (hN : 0<N) (hR : 0<R) (hRN : R≤N)
    (hroot : (R:ℝ)≤2*(N:ℝ)^(1/(k:ℝ))) (hA : 0≤A)
    (he : 0≤e) (hea : e≤(halaszStepExponent s k:ℝ))
    (hshort : (halaszVinogradovCount s k (N/R+1):ℝ)≤A*((N/R+1:ℕ):ℝ)^e)
    (hstep : halaszVinogradovCount (k+s) k N ≤
      2*(2*(k^2*k)+1)*((16*R)^(2*s)*((k^k*(16*R)^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/R+1))))) :
    (halaszVinogradovCount (k+s) k N:ℝ) ≤
      (A*(2*(2*(k^2*k)+1)*(k:ℝ)^k*32^(halaszStepExponent s k)))*
        (N:ℝ)^((k:ℝ)+e+((halaszStepExponent s k:ℝ)-e)/(k:ℝ)) := by
  let a := halaszStepExponent s k
  let C : ℝ := 2*(2*(k^2*k)+1)*(k:ℝ)^k*16^a
  have hC : 0≤C := by dsimp [C]; positivity
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hR0 : (0:ℝ)<R := by exact_mod_cast hR
  have hnat : halaszVinogradovCount (k+s) k N ≤
      (2*(2*(k^2*k)+1)*k^k*16^a)*R^a*N^k*halaszVinogradovCount s k (N/R+1) := by
    convert hstep using 1
    simp only [a,halaszStepExponent,pow_add,mul_pow]
    ring
  have hreal : (halaszVinogradovCount (k+s) k N:ℝ) ≤
      C*(R:ℝ)^a*(N:ℝ)^k*(halaszVinogradovCount s k (N/R+1):ℝ) := by
    dsimp only [C]
    exact_mod_cast hnat
  have hscale := halasz_scale_factor hN0 hR0 (by positivity : (0:ℝ)≤(N/R+1:ℕ))
    he hea (halasz_division_endpoint hR hRN) hroot
  rw [Real.rpow_natCast] at hscale
  have hmul := mul_le_mul_of_nonneg_left hscale (mul_nonneg hA hC)
  have h32 : (16:ℝ)^a*2^a=(32:ℝ)^a := by rw [← mul_pow]; norm_num
  calc
    (halaszVinogradovCount (k+s) k N:ℝ)
        ≤ C*(R:ℝ)^a*(N:ℝ)^k*(A*((N/R+1:ℕ):ℝ)^e) :=
      hreal.trans (mul_le_mul_of_nonneg_left hshort (by positivity))
    _ = (A*C)*((R:ℝ)^a*(N:ℝ)^k*((N/R+1:ℕ):ℝ)^e) := by ring
    _ ≤ (A*C)*(2^a*(N:ℝ)^((k:ℝ)+e+((a:ℝ)-e)/(k:ℝ))) := by
      simpa only [Real.rpow_natCast] using hmul
    _ = _ := by
      dsimp only [C]
      rw [show A*(2*(2*(k^2*k)+1)*(k:ℝ)^k*16^a)*
          (2^a*(N:ℝ)^((k:ℝ)+e+((a:ℝ)-e)/(k:ℝ))) =
          (A*(2*(2*(k^2*k)+1)*(k:ℝ)^k)*(16^a*2^a))*
            (N:ℝ)^((k:ℝ)+e+((a:ℝ)-e)/(k:ℝ)) by ring,h32]
      dsimp only [a]
      ring

theorem halasz_normalized_classical_step : ∃ R₀ : ℕ, ∀ s k N : ℕ, ∀ A e : ℝ,
    0<s → 2≤k → 2^k≤N → (4*(k:ℝ)^2)^2<(N:ℝ) →
    R₀≤halaszRootScale N k → (2*(k^2*k)+1)^2≤halaszRootScale N k →
    k<halaszRootScale N k → 0≤A → 0≤e → e≤(halaszStepExponent s k:ℝ) →
    ((halaszVinogradovCount s k (N/halaszRootScale N k+1):ℝ)≤
      A*((N/halaszRootScale N k+1:ℕ):ℝ)^e) →
    (halaszVinogradovCount (k+s) k N:ℝ) ≤
      (A*(2*(2*(k^2*k)+1)*(k:ℝ)^k*32^(halaszStepExponent s k)))*
        (N:ℝ)^((k:ℝ)+e+((halaszStepExponent s k:ℝ)-e)/(k:ℝ)) := by
  obtain ⟨R₀,hstep⟩ := halasz_classical_step
  refine ⟨R₀,?_⟩
  intro s k N A e hs hk hN hsize hR0 hmany hkR hA he hea hshort
  have hN0 : 0<N := (pow_pos (by omega : 0<(2:ℕ)) k).trans_le hN
  have h := hstep s k N (halaszRootScale N k) hs hk hsize hkR
    (halasz_root_scale_lt (by omega)) hR0 hmany
  exact halasz_normalize_classical_bound hN0 (halasz_root_scale_pos N k)
    (halasz_root_scale_le_endpoint hk hN) (halasz_root_scale_upper (by omega)) hA he hea hshort h

end TwoPointCorrelations

end OAI
