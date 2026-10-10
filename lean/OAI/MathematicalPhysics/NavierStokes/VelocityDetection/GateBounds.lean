import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TranslationGates
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.TranslationGates
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open UniformDerivatives

theorem compactSupport_window : HasCompactSupport window := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-3 : ℝ) 3))
  intro s hs
  have h : |s| < 3 := lt_of_not_ge (fun h => hs (window_zero_outside h))
  exact ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

theorem compactSupport_windowD : HasCompactSupport windowD := by
  rw [← deriv_window]
  exact compactSupport_window.deriv

def moment (f : ℝ → ℝ) (s : ℝ) : ℝ := s * f s

@[fun_prop] theorem contDiff_moment {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (moment f) := contDiff_id.mul hf

theorem compactSupport_moment {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (moment f) := hf.mul_left

theorem field_zero_shape (R : ℝ) (c G X : Coord 2) :
    field R c G X 0 =
      (window ((X 0 - c 0) / R) *
        (window ((X 1 - c 1) / R) + moment windowD ((X 1 - c 1) / R))) * G 0 -
      (moment window ((X 0 - c 0) / R) * windowD ((X 1 - c 1) / R)) * G 1 := by
  rw [field_apply_zero]
  simp only [moment, div_eq_mul_inv]
  ring

theorem field_one_shape (R : ℝ) (c G X : Coord 2) :
    field R c G X 1 =
      ((window ((X 0 - c 0) / R) + moment windowD ((X 0 - c 0) / R)) *
        window ((X 1 - c 1) / R)) * G 1 -
      (windowD ((X 0 - c 0) / R) * moment window ((X 1 - c 1) / R)) * G 0 := by
  rw [field_apply_one]
  simp only [moment, div_eq_mul_inv]
  ring

theorem bounded_movingField {I : Type*} (R : I → ℝ) (hR : ∀ a, 1 ≤ R a)
    (c : I → ℝ → Coord 2) (hc : ∀ a, ContDiff ℝ ∞ (c a))
    (hcB : ∀ i, Positive (fun a t => c a t i)) (i : Fin 2) :
    Bounded (fun a (q : ℝ × Coord 2) => field (R a) (c a q.1) (deriv (c a) q.1) q.2 i) := by
  let z (j : Fin 2) (a : I) (q : ℝ × Coord 2) := (q.2 j - c a q.1 j) / R a
  let v (j : Fin 2) (a : I) (q : ℝ × Coord 2) := deriv (c a) q.1 j
  have hcs (j : Fin 2) (a : I) : ContDiff ℝ ∞ (fun t => c a t j) :=
    (contDiff_apply ℝ ℝ j).comp (hc a)
  have hzs (j : Fin 2) (a : I) : ContDiff ℝ ∞ (z j a) := by
    dsimp [z]
    exact ((contDiff_apply ℝ ℝ j).comp contDiff_snd |>.sub
      ((hcs j a).comp contDiff_fst)).div_const _
  have hvs (j : Fin 2) (a : I) : ContDiff ℝ ∞ (v j a) :=
    (contDiff_apply ℝ ℝ j).comp
      (((contDiff_infty_iff_deriv.mp (hc a)).2).comp contDiff_fst)
  have hzb (j : Fin 2) : Positive (z j) := by
    let L : (ℝ × Coord 2) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ (Coord 2))
    have hLj : ∀ a : I, ContDiff ℝ ∞ (fun q : ℝ × Coord 2 => q.2 j) := fun _ => L.contDiff
    exact ((Positive.linear (I := I) L).sub hLj
      (fun a => (hcs j a).comp contDiff_fst)
      ((hcB j).precomp (hcs j) (ContinuousLinearMap.fst ℝ ℝ (Coord 2))
        (ContinuousLinearMap.norm_fst_le _ _ _))).div (fun a => (hLj a).sub
          ((hcs j a).comp contDiff_fst)) R hR
  have hvb (j : Fin 2) : Bounded (v j) := by
    have h := ((hcB j).deriv).precomp (fun a => (contDiff_infty_iff_deriv.mp (hcs j a)).2)
      (ContinuousLinearMap.fst ℝ ℝ (Coord 2)) (ContinuousLinearMap.norm_fst_le _ _ _)
    have heq : v j = fun a (q : ℝ × Coord 2) => deriv (fun t => c a t j) q.1 := by
      funext a q
      dsimp [v]
      rw [deriv_pi (fun k => (hcs k a).differentiable (by simp) q.1)]
    rwa [heq]
  have hp (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (j : Fin 2) :
      Bounded (fun a q => ψ (z j a q)) :=
    (compact (I := I) hψ hψc).comp (fun _ => hψ) (hzs j) (hzb j)
  have hW (j : Fin 2) := hp window contDiff_window compactSupport_window j
  have hD (j : Fin 2) := hp windowD contDiff_windowD compactSupport_windowD j
  have hM (j : Fin 2) := hp (moment window) (contDiff_moment contDiff_window)
    (compactSupport_moment compactSupport_window) j
  have hMD (j : Fin 2) := hp (moment windowD) (contDiff_moment contDiff_windowD)
    (compactSupport_moment compactSupport_windowD) j
  have hsW (j : Fin 2) (a : I) := contDiff_window.comp (hzs j a)
  have hsD (j : Fin 2) (a : I) := contDiff_windowD.comp (hzs j a)
  have hsM (j : Fin 2) (a : I) := (contDiff_moment contDiff_window).comp (hzs j a)
  have hsMD (j : Fin 2) (a : I) := (contDiff_moment contDiff_windowD).comp (hzs j a)
  fin_cases i
  · change Bounded (fun a (q : ℝ × Coord 2) =>
      field (R a) (c a q.1) (deriv (c a) q.1) q.2 0)
    simp_rw [field_zero_shape]
    exact ((hW 0).mul (hsW 0) (fun a => (hsW 1 a).add (hsMD 1 a))
      ((hW 1).add (hsW 1) (hsMD 1) (hMD 1)) |>.mul
        (fun a => (hsW 0 a).mul ((hsW 1 a).add (hsMD 1 a))) (hvs 0) (hvb 0)).sub
      (fun a => ((hsW 0 a).mul ((hsW 1 a).add (hsMD 1 a))).mul (hvs 0 a))
      (fun a => ((hsM 0 a).mul (hsD 1 a)).mul (hvs 1 a))
      (((hM 0).mul (hsM 0) (hsD 1) (hD 1)).mul
        (fun a => (hsM 0 a).mul (hsD 1 a)) (hvs 1) (hvb 1))
  · change Bounded (fun a (q : ℝ × Coord 2) =>
      field (R a) (c a q.1) (deriv (c a) q.1) q.2 1)
    simp_rw [field_one_shape]
    exact (((hW 0).add (hsW 0) (hsMD 0) (hMD 0)).mul
      (fun a => (hsW 0 a).add (hsMD 0 a)) (hsW 1) (hW 1) |>.mul
        (fun a => ((hsW 0 a).add (hsMD 0 a)).mul (hsW 1 a)) (hvs 1) (hvb 1)).sub
      (fun a => (((hsW 0 a).add (hsMD 0 a)).mul (hsW 1 a)).mul (hvs 1 a))
      (fun a => ((hsD 0 a).mul (hsM 1 a)).mul (hvs 0 a))
      (((hD 0).mul (hsD 0) (hsM 1) (hM 1)).mul
        (fun a => (hsD 0 a).mul (hsM 1 a)) (hvs 0) (hvb 0))

end VelocityDetection.TranslationGates
end

end OAI
