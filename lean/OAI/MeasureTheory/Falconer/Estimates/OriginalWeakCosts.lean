import OAI.MeasureTheory.Falconer.Incidence.IncidencePowerBudget

namespace OAI

/-! All preparation costs fit one fixed polynomial. This converts the
original block-incidence estimate to the published weak-power conclusion. -/
namespace Falconer

noncomputable def originalIncidenceCost (B : ℕ) : ℝ :=
  max (165888*(4*(2:ℝ)^B)*(2*(B:ℝ)+13)*(64*(2:ℝ)^B+1)^2)
    (162*(64*(2:ℝ)^B+1)^2*(4*(2:ℝ)^B)^2)

theorem original_weak_costs {N B : ℕ} {δ ε lam ζ s t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/8)
    (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hs1 : s ≤ 1) (_ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hscale : 1/(2:ℝ)^N ≤ (4*(2:ℝ)^B)*δ)
    (hpoly : originalIncidenceCost B*((N:ℝ)+1)*(2:ℝ)^(ε*(N:ℝ)) ≤ (2:ℝ)^((lam/4)*(N:ℝ)))
    (hfinal : originalIncidenceCost B*(2:ℝ)^((2*ε)*(N:ℝ)) ≤ (2:ℝ)^(ζ*(N:ℝ))) :
    let K := δ^(-ε);
    let J : ℝ := (Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ);
    let F := (16*(1/(2:ℝ)^N)/δ+1)^2;
    (41472*K*J*F*2^t ≤ (2:ℝ)^((lam/4)*(N:ℝ)) ∧
      41472*K*J*F*4^s ≤ (2:ℝ)^(lam*(N:ℝ)) ∧
      81*F ≤ (2:ℝ)^(lam*(N:ℝ))) ∧
    (162*K*δ^s*F)*δ^(-2*s-ε) ≤ (2:ℝ)^((s+ζ)*(N:ℝ)) := by
  dsimp only
  let K := δ^(-ε)
  let J : ℝ := (Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ)
  let F := (16*(1/(2:ℝ)^N)/δ+1)^2
  let C := 4*(2:ℝ)^B
  let D := 2*(B:ℝ)+13
  let F0 := (64*(2:ℝ)^B+1)^2
  have hC1 : 1 ≤ C := by
    have hh : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
    dsimp [C]
    linarith
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hF0 : 0 ≤ F0 := sq_nonneg _
  have hK1 : 1 ≤ K := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hJ1 : 1 ≤ J := by dsimp [J]; exact_mod_cast (show 1 ≤ Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1 by omega)
  have hF : 0 ≤ F := sq_nonneg _
  have hCb : C^ε ≤ C := by
    calc
      _ ≤ C^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hC1 (by linarith)
      _ = _ := Real.rpow_one _
  have hKb : K ≤ C*(2:ℝ)^(ε*(N:ℝ)) :=
    (incidence_inverse_scale_power hδ (zero_le_one.trans hC1) hε N hscale).trans
      (mul_le_mul_of_nonneg_right hCb (by positivity))
  have hJb : J ≤ D*((N:ℝ)+1) := incidence_bucket_linear_bound hδ N B hscale
  have hFb : F ≤ F0 := incidence_packing_factor_bound hδ (by positivity) B hscale
  have hweak : 41472*K*J*F*4 ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
    calc
      _ ≤ 41472*(C*(2:ℝ)^(ε*(N:ℝ)))*(D*((N:ℝ)+1))*F0*4 := by gcongr
      _ = (165888*C*D*F0)*((N:ℝ)+1)*(2:ℝ)^(ε*(N:ℝ)) := by ring
      _ ≤ originalIncidenceCost B*((N:ℝ)+1)*(2:ℝ)^(ε*(N:ℝ)) := by
        gcongr
        exact le_max_left _ _
      _ ≤ _ := hpoly
  have hweakbig : (2:ℝ)^((lam/4)*(N:ℝ)) ≤ (2:ℝ)^(lam*(N:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by linarith : lam/4 ≤ lam) (Nat.cast_nonneg N))
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · apply le_trans _ hweak
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht2
      _ = 4 := by norm_num
  · apply le_trans _ (hweak.trans hweakbig)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (4:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
      _ = 4 := by norm_num
  · apply le_trans _ (hweak.trans hweakbig)
    have hKJ := one_le_mul_of_one_le_of_one_le hK1 hJ1
    have hh := mul_le_mul_of_nonneg_right hKJ (show 0 ≤ 165888*F by positivity)
    nlinarith only [hh,hF]
  · have ha : 0 ≤ s+2*ε := by positivity
    have ha2 : s+2*ε ≤ 2 := by linarith
    have hCa : C^(s+2*ε) ≤ C^2 := by
      calc
        _ ≤ C^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hC1 ha2
        _ = C^2 := by norm_num
    have he : K*δ^s*δ^(-2*s-ε) = δ^(-(s+2*ε)) := by
      dsimp [K]
      rw [← Real.rpow_add hδ,← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ = 162*F*(K*δ^s*δ^(-2*s-ε)) := by ring
      _ = 162*F*δ^(-(s+2*ε)) := by rw [he]
      _ ≤ 162*F0*(C^(s+2*ε)*(2:ℝ)^((s+2*ε)*(N:ℝ))) := by
        gcongr
        exact incidence_inverse_scale_power hδ (zero_le_one.trans hC1) ha N hscale
      _ ≤ 162*F0*(C^2*(2:ℝ)^((s+2*ε)*(N:ℝ))) := by gcongr
      _ ≤ originalIncidenceCost B*(2:ℝ)^((s+2*ε)*(N:ℝ)) := by
        have hh : 162*F0*C^2 ≤ originalIncidenceCost B := le_max_right _ _
        nlinarith only [mul_le_mul_of_nonneg_right hh (show 0 ≤ (2:ℝ)^((s+2*ε)*(N:ℝ)) by positivity)]
      _ = (2:ℝ)^(s*(N:ℝ))*(originalIncidenceCost B*(2:ℝ)^((2*ε)*(N:ℝ))) := by
        rw [show (s+2*ε)*(N:ℝ) = s*(N:ℝ)+(2*ε)*(N:ℝ) by ring,
          Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        ring
      _ ≤ (2:ℝ)^(s*(N:ℝ))*(2:ℝ)^(ζ*(N:ℝ)) := mul_le_mul_of_nonneg_left hfinal (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring

end Falconer

end OAI
