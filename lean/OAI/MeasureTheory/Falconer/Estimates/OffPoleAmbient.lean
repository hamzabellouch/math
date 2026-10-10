import OAI.MeasureTheory.Falconer.Geometry.AmbientChartBudget
import OAI.MeasureTheory.Falconer.Estimates.QuadraticBudget
import OAI.MeasureTheory.Falconer.Angular.SphereOffPole

namespace OAI

/-! # The off-pole estimate with the original ambient derivative budget -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def offPoleLocalizedAmbient {d : ℕ} (e : Sphere d) (B : Space d → ℂ)
    (x : Space d) : ℂ := (offPoleCutoff e x : ℂ)*B x

theorem offPoleLocalizedAmbient_contDiff {d : ℕ} (e : Sphere d) {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (offPoleLocalizedAmbient e B) :=
  (Complex.ofRealCLM.contDiff.comp (offPoleCutoff_contDiff e)).mul hB

theorem offPoleLocalizedAmbient_eq {d : ℕ} (e : Sphere d) (B : Space d → ℂ) :
    offPoleLocalizedAmbient e B = B-poleLocalizedAmbient e B-
      poleLocalizedAmbient (oppositePole e) B := by
  funext x
  simp only [offPoleLocalizedAmbient,offPoleCutoff,poleLocalizedAmbient,Pi.sub_apply,
    Complex.ofReal_sub,Complex.ofReal_one]
  ring

theorem offPoleLocalizedAmbient_scaled_budget (d r : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (e : Sphere d) (B : Space d → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ r, ∀ w : Sphere d, ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ k ≤ r, ∀ w : Sphere d,
        ‖iteratedFDeriv ℝ k (offPoleLocalizedAmbient e B) w‖ ≤ L*C*D^k := by
  choose A hA hAb using fun k => poleLocalizedAmbient_uniform_budget d k
  let H := ∑ k ∈ Finset.range (r+1), A k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hA k)
  refine ⟨1+2*H,by positivity,?_⟩
  intro e B hB C D hC hD hb k hk w
  have hp := poleLocalizedAmbient_contDiff e hB
  have hm := poleLocalizedAmbient_contDiff (oppositePole e) hB
  rw [offPoleLocalizedAmbient_eq,
    iteratedFDeriv_sub_apply (i := k) (f := B-poleLocalizedAmbient e B)
      (g := poleLocalizedAmbient (oppositePole e) B) ((hB.sub hp).contDiffAt.of_le (by simp))
      (hm.contDiffAt.of_le (by simp)),
    iteratedFDeriv_sub_apply (i := k) (f := B) (g := poleLocalizedAmbient e B)
      (hB.contDiffAt.of_le (by simp)) (hp.contDiffAt.of_le (by simp))]
  have hbp := hAb k e B hB C D hC hD (fun j hj => hb j (hj.trans hk)) k le_rfl w
  have hbm := hAb k (oppositePole e) B hB C D hC hD
    (fun j hj => hb j (hj.trans hk)) k le_rfl w
  have hAH : A k ≤ H := Finset.single_le_sum (fun k _ => hA k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hpow : 0 ≤ D^k := pow_nonneg (zero_le_one.trans hD) k
  calc
    _ ≤ (‖iteratedFDeriv ℝ k B w‖+
        ‖iteratedFDeriv ℝ k (poleLocalizedAmbient e B) w‖)+
        ‖iteratedFDeriv ℝ k (poleLocalizedAmbient (oppositePole e) B) w‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (C*D^k+A k*C*D^k)+A k*C*D^k := by gcongr; exact hb k hk w
    _ ≤ (C*D^k+H*C*D^k)+H*C*D^k := by gcongr
    _ = _ := by ring

theorem sphere_offPole_decay_of_ambient_bounds (hpublished : PublishedGnomonicSurface)
    (n M : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (n+2)) (B : Space (n+2) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ M, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 0 < Λ →
      ‖sphereOscillation Λ e (fun w => offPoleLocalizedAmbient e B w)‖ ≤
        A*C*(D/Λ)^M := by
  obtain ⟨A,hA,hdecay⟩ := sphere_offPole_decay hpublished n M hn (ε := 1/16) (by norm_num)
  obtain ⟨L,hL,hLb⟩ := offPoleLocalizedAmbient_scaled_budget (n+2) M
  obtain ⟨H,hH,hHb⟩ := ambient_symbol_rotated_chart_budget n M
  refine ⟨A*H*L,by positivity,?_⟩
  intro e B hB C D hC hD hb Λ hΛ
  let F := offPoleLocalizedAmbient e B
  have hF : ContDiff ℝ ∞ F := offPoleLocalizedAmbient_contDiff e hB
  have hder : ∀ j ≤ M, ∀ w : Sphere (n+2),
      ‖iteratedFDeriv ℝ j F w‖ ≤ (L*C)*D^j := by
    intro j hj w
    exact (hLb e B hB C D hC hD hb j hj w).trans_eq (by ring)
  have hFb : ∀ w : Sphere (n+2), ‖F w‖ ≤ L*C := by
    intro w
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hder 0 (Nat.zero_le _) w
  have hh := hdecay e (fun w => F w) (sphere_norm e)
    (hF.continuous.measurable.comp continuous_subtype_val.measurable)
    (fun w hw => offPoleCutoff_gap e w (by
      intro hz
      exact hw (by simp only [F,offPoleLocalizedAmbient,hz,Complex.ofReal_zero,zero_mul])))
    (fun T y _ => ambient_symbol_chart_smooth T F hF y)
    (L*C) (H*(L*C)) D Λ (by positivity) hD hΛ hFb
    (fun T y hy k hk u hu => hHb F hF (L*C) D (by positivity) hD hder T y hy u hu k hk)
  exact hh.trans_eq (by ring)

end Falconer

end OAI
