import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.OriginalAnnularOscillationBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma net_oscillation_scale {u d A E D V w : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hw : 0 ≤ w) (hA : 0 ≤ A)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hV : 0 ≤ V) (hd : d ≤ u^2) :
    A/u*d*(E+D*u^(-3*w)+V) ≤ A*(E+D)*u^(1-3*w)+A*u*V := by
  have hp : 1 ≤ u^(-3*w) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith)
  have hEp : E ≤ E*u^(-3*w) := by simpa using mul_le_mul_of_nonneg_left hp hE
  have heq : u*u^(-3*w) = u^(1-3*w) := by
    rw [sub_eq_add_neg,Real.rpow_add hu,Real.rpow_one]
    simp only [neg_mul]
  calc
    _ ≤ A/u*u^2*(E+D*u^(-3*w)+V) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity)
    _ = A*u*(E+D*u^(-3*w)+V) := by field_simp
    _ ≤ A*u*((E+D)*u^(-3*w)+V) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hEp]) (by positivity)
    _ = A*(E+D)*(u*u^(-3*w))+A*u*V := by ring
    _ = _ := by rw [heq]

theorem exists_original_net_field_variation_constant :
    ∃ A : ℝ, 0 < A ∧ ∀ {N K : ℕ} (F : fermionGraph N)
      (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ},
      0 < c₁ → 0 < r₀ → 0 < s → r₀ ≤ s →
      ∀ (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
        (u C D : ℝ), 0 < u → u ≤ 1/96 → 0 ≤ C → 0 ≤ D →
      capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z) ≤ 1 →
      (∀ t : Space, u ≤ ‖t‖ → ‖t‖ ≤ 2*u →
        originalQueryDensity F r j c₁ r₀ s z t ≤ D*u^(-6-3*masterExponent)) →
      ∀ y x : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ‖x-y‖ ≤ u^2 →
        |‖x‖^4*originalQueryField F Z lam r j c₁ r₀ s z x-
          ‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y| ≤
        A*(16*(C+1)*100000^4+D)*u^(1-3*masterExponent)+
          A*u*max (-(‖y‖^4*originalQueryField F Z lam r j c₁ r₀ s z y)) 0 := by
  obtain ⟨A,hA,hbound⟩ := exists_original_scaled_oscillation_constant
  refine ⟨A,hA,?_⟩
  intro N K F Z lam r j c₁ r₀ s hc hr₀ hs hrs z u C D hu hu96 hC hD hstat hden y x hyl hyh hxy
  have hdist : ‖x-y‖ ≤ u/96 := hxy.trans (by nlinarith)
  exact (hbound F Z lam r j hc hr₀ hs hrs z u C D hu hC hD hstat hden y x hyl hyh hdist).trans
    (net_oscillation_scale hu (by linarith) (by norm_num [masterExponent]) hA.le
      (by positivity) hD (le_max_right _ _) hxy)

lemma net_field_high_transfer {a b h xi α β : ℝ}
    (_hxi : 0 ≤ xi) (hh : xi ≤ h) (hα : α ≤ xi/4) (hβ : β ≤ 1)
    (hov : |b-a| ≤ α+β*max (-a) 0) (ha : a ≤ h-xi) :
    b ≤ h-3*xi/4 := by
  have hb := (abs_le.mp hov).2
  by_cases hn : 0 ≤ a
  · rw [max_eq_right (by linarith : -a ≤ 0),mul_zero,add_zero] at hb
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ -a)] at hb
    have hp : β*(-a) ≤ -a := by simpa using mul_le_mul_of_nonneg_right hβ (by linarith : 0 ≤ -a)
    linarith

lemma net_field_low_transfer {a b h xi α β : ℝ}
    (hxi : 0 ≤ xi) (hh : 0 ≤ h) (hα : α ≤ xi/4)
    (hov : |b-a| ≤ α+β*max (-a) 0) (ha : h+xi ≤ a) :
    h+3*xi/4 ≤ b := by
  rw [max_eq_right (by linarith : -a ≤ 0),mul_zero,add_zero] at hov
  have hb := (abs_le.mp hov).1
  linarith

end CoulombAtom

end

end OAI
