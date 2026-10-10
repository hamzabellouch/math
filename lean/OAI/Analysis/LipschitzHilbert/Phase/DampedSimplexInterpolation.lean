import OAI.Analysis.LipschitzHilbert.Estimates.SimplexBarycenter
import OAI.Analysis.LipschitzHilbert.Phase.GaussianPhaseDamping

namespace OAI

/-! The damped scalar simplex estimate gives the undamped estimate at
its real barycenter. These are precisely the interpolation and damping
operations used for the source family in manuscript §11. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem gaussianPhaseDamping_real_ge_one (a : ι → ℝ) :
    1 ≤ ‖gaussianPhaseDamping (phaseTubePoint a (fun _ => 0))‖ := by
  rw [gaussianPhaseDamping_norm]
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),Finset.sum_const_zero,sub_zero]
  exact Real.one_le_exp_iff.mpr (Finset.sum_nonneg fun i _ => sq_nonneg (a i))

theorem gaussian_undamp_real (F : (ι → ℂ) → ℂ) (a : ι → ℝ) (C : ℝ)
    (h : ‖gaussianPhaseDamping (phaseTubePoint a (fun _ => 0))*
      F (phaseTubePoint a (fun _ => 0))‖ ≤ C) :
    ‖F (phaseTubePoint a (fun _ => 0))‖ ≤ C := by
  calc
    _ ≤ ‖gaussianPhaseDamping (phaseTubePoint a (fun _ => 0))‖*
        ‖F (phaseTubePoint a (fun _ => 0))‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (gaussianPhaseDamping_real_ge_one a)
    _ = ‖gaussianPhaseDamping (phaseTubePoint a (fun _ => 0))*
        F (phaseTubePoint a (fun _ => 0))‖ := (norm_mul _ _).symm
    _ ≤ C := h

theorem damped_simplex_barycenter [DecidableEq ι] [Nonempty ι]
    (F : (ι → ℂ) → ℂ) (D : Set (ι → ℝ)) (hD : Convex ℝ D)
    (C mu : ℝ) (hC : 0 < C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D,
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) M a)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι,
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) C (Pi.single i mu)) :
    ‖F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))‖ ≤ C := by
  have h := phaseTubeBound_barycenter (fun z => gaussianPhaseDamping z*F z) D hD C mu hC
    (fun a ha b hb eta => (gaussianPhaseDamping_affine_entire a b eta).mul
      (hentire a ha b hb eta)) hbounded hvertices hvertex
  exact gaussian_undamp_real F _ C (h (fun _ => 0))

end LipschitzHilbert

end

end OAI
