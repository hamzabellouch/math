import Mathlib

namespace OAI

noncomputable section

namespace Problem340.TranslationDerivative

section General

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem fderiv_add_eq (f : E → F) (p : E) (q : F)
    (hf : ∀ x, f (x + p) = f x + q) (x : E) :
    fderiv 𝕜 f (x + p) = fderiv 𝕜 f x := by
  rw [← fderiv_comp_add_right p]
  simp_rw [hf]
  exact fderiv_add_const q

theorem differentiableAt_add_iff (f : E → F) (p : E) (q : F)
    (hf : ∀ x, f (x + p) = f x + q) (x : E) :
    DifferentiableAt 𝕜 f (x + p) ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableAt_comp_add_right p]
  simp_rw [hf]
  exact differentiableAt_add_const_iff q

theorem iterate_add_eq (f : E → E) (p : E)
    (hf : ∀ x, f (x + p) = f x + p) (n : ℕ) (x : E) :
    f^[n] (x + p) = f^[n] x + p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hf]

theorem fderiv_iterate_add_eq (f : E → E) (p : E)
    (hf : ∀ x, f (x + p) = f x + p) (n : ℕ) (x : E) :
    fderiv 𝕜 (f^[n]) (x + p) = fderiv 𝕜 (f^[n]) x :=
  fderiv_add_eq (f^[n]) p p (iterate_add_eq f p hf n) x

theorem fderiv_readout_add_eq (f : E → E) (p : E)
    (hf : ∀ x, f (x + p) = f x + p) (P : E →L[𝕜] F)
    (n : ℕ) (x : E) :
    fderiv 𝕜 (fun y => P (f^[n] y)) (x + p) =
      fderiv 𝕜 (fun y => P (f^[n] y)) x := by
  apply fderiv_add_eq _ p (P p)
  intro y
  rw [iterate_add_eq f p hf, map_add]

theorem fderiv_zsmul_add_eq (f : E → F) (p : E) (q : F)
    (hf : ∀ x, f (x + p) = f x + q) (k : ℤ) (x : E) :
    fderiv 𝕜 f (x + k • p) = fderiv 𝕜 f x :=
  (show Function.Periodic (fderiv 𝕜 f) p from fderiv_add_eq f p q hf).zsmul k x

end General

section Clock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def clockSkew (h : ℝ × E → ℝ) (g : E → E) : ℝ × E → ℝ × E :=
  fun x => (x.1 + h x, g x.2)

omit [NormedSpace ℝ E] in
theorem clockSkew_add_eq (h : ℝ × E → ℝ) (g : E → E) (T : ℝ)
    (hh : ∀ t z, h (t + T, z) = h (t, z)) (x : ℝ × E) :
    clockSkew h g (x + (T, 0)) = clockSkew h g x + (T, 0) := by
  rcases x with ⟨t, z⟩
  simp only [clockSkew, Prod.mk_add_mk, add_zero, hh]
  congr 1
  ring

theorem clockSkew_fderiv_iterate_periodic (h : ℝ × E → ℝ) (g : E → E) (T : ℝ)
    (hh : ∀ t z, h (t + T, z) = h (t, z)) (n : ℕ) (z : E) :
    Function.Periodic (fun t => fderiv ℝ ((clockSkew h g)^[n]) (t, z)) T := by
  intro t
  simpa only [Prod.mk_add_mk, add_zero] using
    fderiv_iterate_add_eq (𝕜 := ℝ) (clockSkew h g) (T, 0)
      (clockSkew_add_eq h g T hh) n (t, z)

theorem clockPrediction_fderiv_periodic (h : ℝ × E → ℝ) (g : E → E) (T : ℝ)
    (hh : ∀ t z, h (t + T, z) = h (t, z)) (n : ℕ) (z : E) :
    Function.Periodic
      (fun t => fderiv ℝ (fun y => ((clockSkew h g)^[n] y).1) (t, z)) T := by
  intro t
  simpa only [Prod.mk_add_mk, add_zero, ContinuousLinearMap.coe_fst'] using
    fderiv_readout_add_eq (clockSkew h g) (T, 0)
      (clockSkew_add_eq h g T hh) (ContinuousLinearMap.fst ℝ ℝ E) n (t, z)

end Clock

end Problem340.TranslationDerivative

end

end OAI
