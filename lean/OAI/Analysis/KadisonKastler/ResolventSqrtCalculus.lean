import OAI.Analysis.KadisonKastler.ResolventContinuousCalculus
import OAI.Analysis.KadisonKastler.ResolventCoordinateMultiplier
import OAI.Analysis.KadisonKastler.TomitaMiddleCore

namespace OAI

/-! # Square-root functions in the real resolvent calculus -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventSqrtFunction (R : H →L[ℂ] H) : C(spectrum ℝ R, ℂ) :=
  ⟨fun s => (Real.sqrt s.val : ℂ), by fun_prop⟩

def resolventComplementSqrtFunction (R : H →L[ℂ] H) : C(spectrum ℝ R, ℂ) :=
  ⟨fun s => (Real.sqrt (1 - s.val) : ℂ), by fun_prop⟩

theorem resolventContinuousCalculus_coordinate (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    resolventContinuousCalculus R hR (resolventCoordinateFunction R) = R :=
  (resolventContinuousCalculus_ofReal R hR
    ((ContinuousMap.id ℝ).restrict (spectrum ℝ R))).trans (cfcHom_id hR)

theorem resolventContinuousCalculus_sqrt (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hp : 0 ≤ R) :
    resolventContinuousCalculus R hR (resolventSqrtFunction R) = CFC.sqrt R := by
  let f : C(spectrum ℝ R, ℝ) := ⟨fun s => Real.sqrt s.val, by fun_prop⟩
  change resolventContinuousCalculus R hR
    ⟨fun s => (f s : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ = _
  rw [resolventContinuousCalculus_ofReal]
  rw [CFC.sqrt_eq_real_sqrt R hp, cfcₙ_eq_cfc]
  exact (cfc_apply Real.sqrt R hR (by fun_prop)).symm

theorem resolventContinuousCalculus_complement_sqrt (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hp : 0 ≤ 1 - R) :
    resolventContinuousCalculus R hR (resolventComplementSqrtFunction R) = CFC.sqrt (1 - R) := by
  let f : C(spectrum ℝ R, ℝ) := ⟨fun s => Real.sqrt (1 - s.val), by fun_prop⟩
  change resolventContinuousCalculus R hR
    ⟨fun s => (f s : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ = _
  rw [resolventContinuousCalculus_ofReal]
  have he : cfc (fun s : ℝ => 1 - s) R = 1 - R := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) R (by fun_prop) (by fun_prop),
      cfc_const_one ℝ R hR, cfc_id' ℝ R hR]
  rw [CFC.sqrt_eq_real_sqrt (1 - R) hp, cfcₙ_eq_cfc, ← he,
    ← cfc_comp Real.sqrt (fun s : ℝ => 1 - s) R (ha := hR)]
  exact (cfc_apply (fun s : ℝ => Real.sqrt (1 - s)) R hR (by fun_prop)).symm

end

end KadisonKastler

end OAI
