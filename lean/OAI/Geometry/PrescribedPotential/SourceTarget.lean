import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Source Target. -/

section

 

namespace Anticanonical.SourceSmooth
open Filter
open scoped ContDiff
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma levi_congr {φ ψ : Coordinates d → ℝ} {z : Coordinates d}
    (h : φ =ᶠ[nhds z] ψ) (v : Coordinates d) : levi φ z v = levi ψ z v := by
  have h' := h.fderiv (𝕜 := ℝ)
  simp only [levi, h'.fderiv_eq]

lemma levi_sub_const (φ : Coordinates d → ℝ) (c : ℝ) (z v : Coordinates d) :
    levi (fun w => φ w - c) z v = levi φ z v := by
  have h : fderiv ℝ (fun w => φ w - c) = fderiv ℝ φ := by
    funext w
    exact fderiv_sub_const c
  simp only [levi, h]

theorem KaehlerMetric.ricci_eq_of_volume
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {c : ℝ} (hc : 0 < c)
    (heq : ∀ i z, z ∈ (A.chart i).target →
      g.volumeCoefficient i z = c * Real.exp (-h.weight i z))
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target)
    (v : Coordinates d) : g.ricciQuadratic i z v = levi (h.weight i) z v := by
  have hlocal : g.ricciPotential i =ᶠ[nhds z]
      (fun w => h.weight i w - Real.log c) := by
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with w hw
    dsimp [KaehlerMetric.ricciPotential]
    rw [heq i w hw, Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp]
    ring
  exact (levi_congr hlocal v).trans (levi_sub_const _ _ _ _)

 

def HasPrescribedVolumePotential (P : A.ProjectiveEmbedding)
    (h : SemipositiveAnticanonicalMetric A) : Prop :=
  ∃ (φ : SmoothRealFunction A) (c : ℝ), 0 < c ∧
    (projectiveBackground P).PositivePotential φ ∧
    ∀ i z, z ∈ (A.chart i).target →
      ((projectiveBackground P).matrix i z + φ.hessian i z).det.re =
        c * Real.exp (-h.weight i z)

 

theorem prescribedRicci_of_potential (P : A.ProjectiveEmbedding)
    (h : SemipositiveAnticanonicalMetric A) (φ : SmoothRealFunction A)
    (hp : (projectiveBackground P).PositivePotential φ) {c : ℝ} (hc : 0 < c)
    (heq : ∀ i z, z ∈ (A.chart i).target →
      ((projectiveBackground P).matrix i z + φ.hessian i z).det.re =
        c * Real.exp (-h.weight i z)) :
    ∃ g : KaehlerMetric A, (∀ i z, g.matrix i z =
        (projectiveBackground P).matrix i z + φ.hessian i z) ∧
      ∀ i z, z ∈ (A.chart i).target →
        ∀ v : Coordinates d, g.ricciQuadratic i z v = levi (h.weight i) z v := by
  refine ⟨(projectiveBackground P).deform φ hp, fun _ _ => rfl, ?_⟩
  intro i z hz v
  exact KaehlerMetric.ricci_eq_of_volume ((projectiveBackground P).deform φ hp) h hc heq i hz v

end Anticanonical.SourceSmooth

end

end OAI
