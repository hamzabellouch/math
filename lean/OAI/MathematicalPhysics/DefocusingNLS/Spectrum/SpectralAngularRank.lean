import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularPhysical
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace OAI

/-! Restoring an angular factor preserves the rank of the regular columns away from zero. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralAngularState (ell : ℕ) (r : ℝ) (Z : E₄) : E₄ :=
  (((r : ℂ)^ell*Z.1.1,(r : ℂ)^ell*((ell : ℂ)/(r : ℂ)*Z.1.1+Z.1.2)),
   ((r : ℂ)^ell*Z.2.1,(r : ℂ)^ell*((ell : ℂ)/(r : ℂ)*Z.2.1+Z.2.2)))

noncomputable def spectralAngularStateLinear (ell : ℕ) (r : ℝ) : E₄ →ₗ[ℂ] E₄ where
  toFun := spectralAngularState ell r
  map_add' := by
    intro Z W
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [spectralAngularState,Prod.fst_add,Prod.snd_add]
    all_goals ring
  map_smul' := by
    intro a Z
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [spectralAngularState,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RingHom.id_apply]
    all_goals ring

theorem spectralAngularState_injective (ell : ℕ) (r : ℝ) (hr : r ≠ 0) :
    Function.Injective (spectralAngularStateLinear ell r) := by
  intro Z W he
  have hp : (r : ℂ)^ell ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr)
  have h11 := congrArg (fun z : E₄ => z.1.1) he
  have h12 := congrArg (fun z : E₄ => z.1.2) he
  have h21 := congrArg (fun z : E₄ => z.2.1) he
  have h22 := congrArg (fun z : E₄ => z.2.2) he
  change (r : ℂ)^ell*Z.1.1=(r : ℂ)^ell*W.1.1 at h11
  change (r : ℂ)^ell*Z.2.1=(r : ℂ)^ell*W.2.1 at h21
  have hZ11 := mul_left_cancel₀ hp h11
  have hZ21 := mul_left_cancel₀ hp h21
  change (r : ℂ)^ell*((ell : ℂ)/(r : ℂ)*Z.1.1+Z.1.2)=
    (r : ℂ)^ell*((ell : ℂ)/(r : ℂ)*W.1.1+W.1.2) at h12
  change (r : ℂ)^ell*((ell : ℂ)/(r : ℂ)*Z.2.1+Z.2.2)=
    (r : ℂ)^ell*((ell : ℂ)/(r : ℂ)*W.2.1+W.2.2) at h22
  have hZ12 := mul_left_cancel₀ hp h12
  have hZ22 := mul_left_cancel₀ hp h22
  rw [hZ11] at hZ12
  rw [hZ21] at hZ22
  exact Prod.ext (Prod.ext hZ11 (add_left_cancel hZ12))
    (Prod.ext hZ21 (add_left_cancel hZ22))

theorem spectralAngularPair_rank (ell : ℕ) (Yp Ym : ℝ → E₄)
    (r : ℝ) (hr : r ≠ 0) (hY : LinearIndependent ℂ ![Yp r,Ym r]) :
    LinearIndependent ℂ ![spectralAngularPair ell Yp r,spectralAngularPair ell Ym r] := by
  have h := hY.map' (spectralAngularStateLinear ell r)
    (LinearMap.ker_eq_bot.mpr (spectralAngularState_injective ell r hr))
  have he : spectralAngularStateLinear ell r ∘ ![Yp r,Ym r]=
      ![spectralAngularPair ell Yp r,spectralAngularPair ell Ym r] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h

end DefocusingNLS

end OAI
