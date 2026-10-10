import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import OAI.Geometry.NodalSets.Elliptic.RealCoordinateDual

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_jet_limit_hasFDerivAt (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (ht : ∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (g ds) atTop Q)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x := by
  have hu := real_uniform_coordinate_dual (fun i ↦ ht (i::ds) (closedBall x 1) (isCompact_closedBall x 1))
  apply hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hu.mono ball_subset_closedBall)
    (f := fun j ↦ partialJet (W j) ds)
  · intro j y _
    change HasFDerivAt (partialJet (W j) ds)
      (realCoordinateDual (fun i ↦ fderiv ℝ (partialJet (W j) ds) y (Pi.single i 1))) y
    rw [← real_fderiv_coordinateDual]
    exact ((partialJet_smooth _ (hW j) ds).differentiable (by simp) y).hasFDerivAt
  · intro y _
    exact (ht ds {y} isCompact_singleton).tendsto_at (mem_singleton y)
  · exact mem_ball_self (by norm_num)

theorem real_jet_limit_smooth (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hc : ∀ ds, Continuous (g ds))
    (hd : ∀ ds x, HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x) :
    ∀ ds, ContDiff ℝ ∞ (g ds) := by
  have hn (n : ℕ) : ∀ ds, ContDiff ℝ n (g ds) := by
    induction n with
    | zero => intro ds; exact contDiff_zero.mpr (hc ds)
    | succ n ih =>
      intro ds
      rw [show ((n+1:ℕ) : ℕ∞ω) = (n:ℕ∞ω)+1 by simp,contDiff_succ_iff_fderiv]
      refine ⟨fun x ↦ (hd ds x).differentiableAt,by simp,?_⟩
      have he : fderiv ℝ (g ds) = fun x ↦ realCoordinateDual (fun i ↦ g (i::ds) x) :=
        funext (fun x ↦ (hd ds x).fderiv)
      rw [he]
      exact realCoordinateDual.contDiff.comp (contDiff_pi.mpr (fun i ↦ ih (i::ds)))
  intro ds
  exact contDiff_infty.mpr (fun n ↦ hn n ds)

theorem real_jet_limit_identification (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hd : ∀ ds x, HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x)
    (ds : List (Fin 4)) : partialJet (g []) ds = g ds := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    funext x
    change fderiv ℝ (partialJet (g []) ds) x (Pi.single i 1) = _
    rw [ih,(hd ds x).fderiv,realCoordinateDual_single]

end
end Yau.Geometry

end OAI
