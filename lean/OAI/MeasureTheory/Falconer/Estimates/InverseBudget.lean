import OAI.MeasureTheory.Falconer.Estimates.LocalInverse
import OAI.MeasureTheory.Falconer.Fourier.MaskedJetBudget

namespace OAI

/-! # Quantitative inverse amplitudes

The inverse coefficient of order `j` loses exactly `2*j` derivatives. Its
derivative bounds are asserted on sphere points, the set used by every
subsequent stationary chart.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem localInverseAmplitude_zero_budget (m r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ k (localInverseAmplitude m B 0) w‖ ≤ A*C*D^k := by
  choose A hA hAb using fun k => poleLocalizedAmbient_uniform_budget (m+3) k
  let H := ∑ k ∈ Finset.range (r+1), A k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hA k)
  let c := (sphereStationaryConstant (m+2))⁻¹
  refine ⟨‖c‖*H,mul_nonneg (norm_nonneg _) hH,?_⟩
  intro B hB C D hC hD hb k hk w
  let e := gnomonicChart (0 : Space (m+2))
  have he : localInverseAmplitude m B 0 = c • poleLocalizedAmbient e B := by
    funext x
    simp only [localInverseAmplitude,Pi.smul_apply,smul_eq_mul,poleLocalizedAmbient,
      stationaryPatchMask,c,e]
    ring
  rw [he,iteratedFDeriv_const_smul_apply
    ((poleLocalizedAmbient_contDiff e hB).contDiffAt.of_le (by simp)),norm_smul]
  have hh := hAb k e B hB C D hC hD (fun l hl => hb l (hl.trans hk)) k le_rfl w
  have hAH : A k ≤ H := Finset.single_le_sum (fun k _ => hA k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  apply (mul_le_mul_of_nonneg_left hh (norm_nonneg c)).trans
  calc
    _ ≤ ‖c‖*(H*C*D^k) := by gcongr
    _ = _ := by ring

theorem localInverseAmplitude_scaled_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ k (localInverseAmplitude m B j) w‖ ≤ A*C*D^(k+2*j) := by
  induction j using Nat.strong_induction_on generalizing r with
  | h j ih =>
    cases j with
    | zero => simpa using localInverseAmplitude_zero_budget m r
    | succ j =>
      choose A hA hAb using fun h : ℕ =>
        ih (j-h) (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self j)) (r+2*(h+1))
      choose M hM hMb using fun h : ℕ => maskedStationaryCoefficient_scaled_budget m (h+1) r
      let S := ∑ h ∈ Finset.range (j+1), M h*A h
      have hS : 0 ≤ S := Finset.sum_nonneg (fun h _ => mul_nonneg (hM h) (hA h))
      let c := (sphereStationaryConstant (m+2))⁻¹
      refine ⟨‖c‖*S,mul_nonneg (norm_nonneg _) hS,?_⟩
      intro B hB C D hC hD hb k hk w
      let F : Space (m+3) → ℂ := fun x => ∑ h ∈ Finset.range (j+1),
        maskedStationaryCoefficient m (h+1) (localInverseAmplitude m B (j-h)) x
      have hF : ContDiff ℝ ∞ F := ContDiff.sum (fun h _ =>
        maskedStationaryCoefficient_contDiff m (h+1) (localInverseAmplitude_contDiff m hB (j-h)))
      have he : localInverseAmplitude m B (j+1) = (-c) • F := by
        funext x
        rw [localInverseAmplitude]
        rfl
      rw [he,iteratedFDeriv_const_smul_apply (hF.contDiffAt.of_le (by simp)),norm_smul,norm_neg]
      have hsum : iteratedFDeriv ℝ k F w = ∑ h ∈ Finset.range (j+1),
          iteratedFDeriv ℝ k
            (maskedStationaryCoefficient m (h+1) (localInverseAmplitude m B (j-h))) w :=
        iteratedFDeriv_fun_sum_apply (fun h _ =>
          ((maskedStationaryCoefficient_contDiff m (h+1)
            (localInverseAmplitude_contDiff m hB (j-h))).of_le (by simp)).contDiffAt)
      rw [hsum]
      have hterm (h : ℕ) (hh : h ∈ Finset.range (j+1)) :
          ‖iteratedFDeriv ℝ k
            (maskedStationaryCoefficient m (h+1) (localInverseAmplitude m B (j-h))) w‖ ≤
            M h*A h*C*D^(k+2*(j+1)) := by
        have hhj : h ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
        have hinput := hAb h B hB C D hC hD (fun l hl v => hb l (by omega) v)
        have hC' : 0 ≤ A h*C*D^(2*(j-h)) :=
          mul_nonneg (mul_nonneg (hA h) hC) (pow_nonneg (zero_le_one.trans hD) _)
        have hshift : ∀ l ≤ r+2*(h+1), ∀ v : Sphere (m+3),
            ‖iteratedFDeriv ℝ l (localInverseAmplitude m B (j-h)) v‖ ≤
              (A h*C*D^(2*(j-h)))*D^l := by
          intro l hl v
          apply (hinput l hl v).trans_eq
          rw [pow_add]
          ring
        have hbound := hMb h (localInverseAmplitude m B (j-h))
          (localInverseAmplitude_contDiff m hB (j-h))
          (A h*C*D^(2*(j-h))) D hC' hD hshift k hk w
        apply hbound.trans_eq
        calc
          _ = M h*A h*C*(D^(2*(j-h))*D^(k+2*(h+1))) := by ring
          _ = _ := by
            rw [← pow_add,show 2*(j-h)+(k+2*(h+1)) = k+2*(j+1) by omega]
      have ht := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
      apply (mul_le_mul_of_nonneg_left ht (norm_nonneg c)).trans_eq
      have hfactor : (∑ h ∈ Finset.range (j+1), M h*A h*C*D^(k+2*(j+1))) =
          S*C*D^(k+2*(j+1)) := by rw [← Finset.sum_mul,← Finset.sum_mul]
      rw [hfactor]
      ring

end Falconer

end OAI
