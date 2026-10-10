import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedSeries
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticEulerInverse
import Mathlib.Analysis.Complex.RemovableSingularity

namespace OAI

/-! Removal of the actual completion factor, including its contribution
to the residue. This is an internal analytic bridge: the completed
continuation must still be constructed from the Voronoi identity. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

def metaplecticCompletedResidue (r : Eisenstein) : ℂ :=
  (metaplecticA0*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ)

lemma metaplectic_completed_residue_div (r : Eisenstein) :
    metaplecticCompletedResidue r/metaplecticCompletionEuler r (5/6) =
      metaplecticResidue r := by
  rw [metaplecticCompletionEuler_at_pole]
  simp only [metaplecticCompletedResidue,metaplecticResidue,Complex.ofReal_div]

/-- The regular part after division includes the divided difference of
the inverse Euler factor. In particular its value at the pole is obtained
by the derivative, without changing any value away from the pole. -/
lemma metaplectic_decompletion_regular {r : Eisenstein} (hr : r ≠ 0)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {s : ℂ | (1/2:ℝ) < s.re}) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h {s : ℂ | (1/2:ℝ) < s.re} ∧
      ∀ s : ℂ, (1/2:ℝ) < s.re → s ≠ (5/6:ℂ) →
        (g s+metaplecticCompletedResidue r/(s-5/6))/metaplecticCompletionEuler r s =
          h s+metaplecticResidue r/(s-5/6) := by
  let e (s : ℂ) := (metaplecticCompletionEuler r s)⁻¹
  have he : DifferentiableOn ℂ e {s : ℂ | (1/2:ℝ) < s.re} :=
    metaplecticCompletionEuler_inverse_differentiableOn hr
  have hp : {s : ℂ | (1/2:ℝ) < s.re} ∈ 𝓝 (5/6:ℂ) := by
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    norm_num
  refine ⟨fun s => g s*e s+metaplecticCompletedResidue r*dslope e (5/6) s,
    (hg.mul he).add (((Complex.differentiableOn_dslope hp).mpr he).const_mul _),?_⟩
  intro s hs hsp
  have hE := metaplecticCompletionEuler_ne_zero hr hs
  have hEp := metaplecticCompletionEuler_ne_zero hr (s := (5/6:ℂ)) (by norm_num)
  change (g s+metaplecticCompletedResidue r/(s-5/6))/metaplecticCompletionEuler r s =
    (g s*e s+metaplecticCompletedResidue r*dslope e (5/6) s)+metaplecticResidue r/(s-5/6)
  rw [dslope_of_ne e hsp,slope,smul_eq_mul,←metaplectic_completed_residue_div r]
  dsimp only [e]
  simp only [vsub_eq_sub]
  have hsp' : s-(5/6:ℂ) ≠ 0 := sub_ne_zero.mpr hsp
  field_simp
  ring

lemma metaplectic_decompletion_right {r : Eisenstein} (hr : primary r)
    {G : ℂ → ℂ} (hG : ∀ s : ℂ, 1 < s.re → G s = metaplecticCompletedSeries r s)
    {s : ℂ} (hs : 1 < s.re) :
    G s/metaplecticCompletionEuler r s = metaplecticGaussSeries r s := by
  rw [hG s hs,metaplecticCompletedSeries_factor hr hs,mul_div_cancel_left₀]
  exact metaplecticCompletionEuler_ne_zero (primary_ne_zero hr) (by linarith)

end CubicFirstMoment

end

end OAI
