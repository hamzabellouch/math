import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrectionRowsBasic
import OAI.NumberTheory.Ostmann.QuadraticSieveRecursionNumerics

namespace OAI

namespace Ostmann.QuadraticSieve

theorem dual_window_root_eq {M H e B : ℝ} (_hM : 0 < M) (hH : 0 < H)
    (he : 0 < e) (_hB : 0 < B) :
    Real.sqrt (e*H^2/(M*B)) = Real.sqrt e*H/Real.sqrt (M*B) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul he.le, Real.sqrt_sq hH.le]

theorem dual_root_product {M B : ℝ} (hM : 0 < M) (hB : 0 < B) :
    Real.sqrt (M/B)*Real.sqrt (M*B) = M := by
  rw [←Real.sqrt_mul (div_nonneg hM.le hB.le)]
  rw [show M/B*(M*B) = M^2 by field_simp, Real.sqrt_sq hM.le]

theorem dual_zero_min_scale {M N B H e T P : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hH : 0 < H)
    (he : 1 ≤ e) (hT : 1 ≤ T) (hP : 0 < P) (hNH : N ≤ 2*H)
    (hcut : P ≤ 4*T*Real.sqrt (e*H^2/(M*B))) :
    M/(e*H) ≤ (4*T)*(M/N)*min 1 (N/(Real.sqrt (M*B)*P)) := by
  have hep : 0 < e := by linarith
  have hTp : 0 < T := by linarith
  have hs : 0 < Real.sqrt (M*B) := Real.sqrt_pos.mpr (mul_pos hM hB)
  have hse : Real.sqrt e ≤ e := by
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hfirst : M/(e*H) ≤ (4*T)*(M/N) := by
    have hNN : N ≤ 4*T*e*H := by
      have hh := mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hT he) hH.le
      nlinarith
    have hh : M/(e*H) ≤ (4*T*M)/N :=
      (div_le_div_iff₀ (mul_pos hep hH) hN).mpr (by nlinarith)
    simpa only [mul_div_assoc] using hh
  have hupper : Real.sqrt (M*B)*P ≤ 4*T*e*H := by
    calc
      _ ≤ Real.sqrt (M*B)*(4*T*Real.sqrt (e*H^2/(M*B))) :=
        mul_le_mul_of_nonneg_left hcut hs.le
      _ = 4*T*Real.sqrt e*H := by
        rw [dual_window_root_eq hM hH hep hB]
        field_simp
      _ ≤ _ := by gcongr
  have hsecond : M/(e*H) ≤ (4*T)*(M/N)*(N/(Real.sqrt (M*B)*P)) := by
    have hh : M/(e*H) ≤ (4*T)*M/(Real.sqrt (M*B)*P) := by
      apply (div_le_div_iff₀ (mul_pos hep hH) (mul_pos hs hP)).mpr
      nlinarith
    convert hh using 1
    field_simp
  rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
  exact le_min hfirst hsecond

theorem dual_reciprocal_min_scale {M N B H e T P D : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hH : 0 < H)
    (he : 1 ≤ e) (hT : 1 ≤ T) (hP : 0 < P) (hD : 0 < D) (hNH : N ≤ 2*H)
    (hPD : P ≤ 2*D) (hcut : Real.sqrt (e*H^2/(M*B)) ≤ 4*T*D) :
    (N/H)*(Real.sqrt (M/(e*B))/D) ≤
      (16*T)*(M/N)*min 1 (N/(Real.sqrt (M*B)*P)) := by
  have hep : 0 < e := by linarith
  have hTp : 0 < T := by linarith
  have hs : 0 < Real.sqrt (M*B) := Real.sqrt_pos.mpr (mul_pos hM hB)
  have hscalar : Real.sqrt (M/(e*B))*H = (M/e)*Real.sqrt (e*H^2/(M*B)) := by
    simpa only [Real.sqrt_sq hH.le] using
      (dual_correction_root_scale (q := H^2) hM hep hB (sq_nonneg H)).symm
  have hfirst : (N/H)*(Real.sqrt (M/(e*B))/D) ≤ (16*T)*(M/N) := by
    have hroot : Real.sqrt (M/(e*B))*H ≤ (M/e)*(4*T*D) := by
      rw [hscalar]
      exact mul_le_mul_of_nonneg_left hcut (div_nonneg hM.le hep.le)
    have heH : 0 < e*H := by positivity
    have hroot' : Real.sqrt (M/(e*B)) ≤ 4*T*M*D/(e*H) := by
      apply (le_div_iff₀ heH).mpr
      have hh := mul_le_mul_of_nonneg_left hroot hep.le
      field_simp at hh
      nlinarith
    calc
      _ ≤ (N/H)*((4*T*M*D/(e*H))/D) := by gcongr
      _ = 4*T*M*N/(e*H^2) := by field_simp
      _ ≤ (16*T)*(M/N) := by
        apply (div_le_iff₀ (by positivity : 0 < e*H^2)).mpr
        have hNN : N^2 ≤ 4*e*H^2 := by nlinarith
        apply (mul_le_mul_iff_right₀ hN).mp
        field_simp
        nlinarith
  have hroot : Real.sqrt (M/(e*B)) ≤ Real.sqrt (M/B) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hM.le hB (by nlinarith)
  have hsecond : (N/H)*(Real.sqrt (M/(e*B))/D) ≤
      (16*T)*(M/N)*(N/(Real.sqrt (M*B)*P)) := by
    have hr : (N/H)*(Real.sqrt (M/(e*B))/D) ≤ 4*Real.sqrt (M/B)/P := by
      calc
        _ ≤ 2*(Real.sqrt (M/B)/D) := by
          gcongr
          exact (div_le_iff₀ hH).mpr hNH
        _ ≤ 4*Real.sqrt (M/B)/P := by
          rw [← mul_div_assoc]
          apply (div_le_div_iff₀ hD hP).mpr
          nlinarith [Real.sqrt_nonneg (M/B)]
    have hid : (M/N)*(N/(Real.sqrt (M*B)*P)) = Real.sqrt (M/B)/P := by
      have hh := dual_root_product hM hB
      apply (eq_div_iff hP.ne').mpr
      field_simp
      nlinarith
    rw [mul_assoc (16*T) (M/N), hid]
    have hh := mul_le_mul_of_nonneg_right (by linarith : 4 ≤ 16*T)
      (show 0 ≤ Real.sqrt (M/B)/P by positivity)
    exact hr.trans (by simpa only [mul_div_assoc] using hh)
  rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
  exact le_min hfirst hsecond

theorem dual_range_bootstrap_scale {M N B x d₁ d₂ Q₁ Q₂ R κ F : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hx : 0 ≤ x)
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hR : 0 ≤ R) (hκ : 0 ≤ κ)
    (_hF : 0 ≤ F) (_hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂)
    (h1 : Q₁ ≤ R*(x+N/d₁)) (h2 : Q₂ ≤ R*(x+N/d₂))
    (hscale : F ≤ κ*(M/N)*min 1 (N/(Real.sqrt (M*B)*(d₁*d₂)))) :
    F*Real.sqrt ((d₁*d₂)*Q₁*Q₂) ≤ κ*R*(M+Real.sqrt (M/B)*x) := by
  have hprod : 0 ≤ d₁*d₂ := by positivity
  have hrad : Real.sqrt (Q₁*Q₂) ≤ R*Real.sqrt ((x+N/d₁)*(x+N/d₂)) := by
    have h := Real.sqrt_le_sqrt (mul_le_mul h1 h2 hQ₂ (by positivity))
    rw [show (R*(x+N/d₁))*(R*(x+N/d₂)) = R^2*((x+N/d₁)*(x+N/d₂)) by ring,
      Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR] at h
    exact h
  rw [mul_assoc (d₁*d₂) Q₁ Q₂, Real.sqrt_mul hprod]
  calc
    _ ≤ (κ*(M/N)*min 1 (N/(Real.sqrt (M*B)*(d₁*d₂)))) *
        (Real.sqrt (d₁*d₂)*(R*Real.sqrt ((x+N/d₁)*(x+N/d₂)))) := by gcongr
    _ = κ*R*((M/N)*Real.sqrt (d₁*d₂)*min 1 (N/(Real.sqrt (M*B)*(d₁*d₂))) *
        Real.sqrt ((x+N/d₁)*(x+N/d₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (recursion_E3 hM hN hB hx hd₁ hd₂) (by positivity)

end Ostmann.QuadraticSieve

end OAI
