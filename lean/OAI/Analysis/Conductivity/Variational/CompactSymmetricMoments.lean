import Mathlib
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma potential_component_fderiv {u : Coord3 → Fin 2 → ℝ}
    (hu : Differentiable ℝ u) (j : Fin 2) (x v : Coord3) :
    fderiv ℝ (fun y => u y j) x v=fderiv ℝ u x v j := by
  rw [(hasFDerivAt_pi'.mp (hu x).hasFDerivAt j).fderiv]
  rfl

lemma symmetric_potential_pairing (D : Coord3 →L[ℝ] (Fin 2 → ℝ))
    (B : Mat3) (hB : B.IsSymm) :
    D ((B*gradientColumns D).col 0) 1=D ((B*gradientColumns D).col 1) 0 := by
  rw [gradientColumns_pairing,gradientColumns_pairing]
  have hs : ((gradientColumns D)ᵀ*(B*gradientColumns D)).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul,transpose_mul,transpose_transpose,hB]
    exact Matrix.mul_assoc _ _ _
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hs

theorem compact_symmetric_source_moments
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (H : Coord3 → Mat3) (hH : ∀ x,(H x).IsSymm)
    (r : Fin 2 → Coord3 → ℝ)
    (hr : ∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (r j))
    (hsr : ∀ j,HasCompactSupport (r j))
    (hw : ∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*r j x)) :
    (∫ x,r 0 x)=0 ∧ (∫ x,r 1 x)=0 ∧
      (∫ x,u x 1*r 0 x-u x 0*r 1 x)=0 := by
  have hz (j : Fin 2) : (∫ x,r j x)=0 := by
    have hh := hw j (fun _ => 1) contDiff_const
    simpa using hh
  have huj (j : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => u x j) :=
    (contDiff_pi.mp hu) j
  have he : (∫ x,u x 1*r 0 x)=(∫ x,u x 0*r 1 x) := by
    have hw₁ := hw 0 (fun x => u x 1) (huj 1)
    have hw₂ := hw 1 (fun x => u x 0) (huj 0)
    have hp : (fun x => fderiv ℝ (fun y => u y 1) x ((H x*gradientColumns (fderiv ℝ u x)).col 0))=
        (fun x => fderiv ℝ (fun y => u y 0) x ((H x*gradientColumns (fderiv ℝ u x)).col 1)) := by
      funext x
      rw [potential_component_fderiv (hu.differentiable (by simp)),
        potential_component_fderiv (hu.differentiable (by simp))]
      exact symmetric_potential_pairing _ _ (hH x)
    rw [hp] at hw₁
    linarith
  refine ⟨hz 0,hz 1,?_⟩
  have hi₁ : Integrable (fun x => u x 1*r 0 x) :=
    ((huj 1).continuous.mul (hr 0).continuous).integrable_of_hasCompactSupport (hsr 0).mul_left
  have hi₂ : Integrable (fun x => u x 0*r 1 x) :=
    ((huj 0).continuous.mul (hr 1).continuous).integrable_of_hasCompactSupport (hsr 1).mul_left
  rw [integral_sub hi₁ hi₂,he,sub_self]

end ScalarConductivity

end

end OAI
