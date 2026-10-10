import OAI.Geometry.NodalSets.Elliptic.PartialJetGerm
import OAI.Geometry.NodalSets.Elliptic.RealJetLimitDerivative

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_finite_local_jet_limit_derivative (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (W : ℕ → Yau.Jets.Coord → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (N : ℕ) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (ht : ∀ ds : List (Fin 4), ds.length ≤ N →
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (g ds) atTop O)
    (ds : List (Fin 4)) (hd : ds.length < N) (x : Yau.Jets.Coord) (hx : x ∈ O) :
    HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x := by
  have hu := real_uniform_coordinate_dual (fun i ↦ ht (i::ds) (by simp; omega))
  apply hasFDerivAt_of_tendstoUniformlyOn hO hu (f := fun j ↦ partialJet (W j) ds)
  · intro j y _
    change HasFDerivAt (partialJet (W j) ds)
      (realCoordinateDual (fun i ↦ fderiv ℝ (partialJet (W j) ds) y (Pi.single i 1))) y
    rw [← real_fderiv_coordinateDual]
    exact ((partialJet_smooth _ (hW j) ds).differentiable (by simp) y).hasFDerivAt
  · intro y hy
    exact (ht ds hd.le).tendsto_at hy
  · exact hx

theorem real_finite_local_jet_limit_identification (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (N : ℕ) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hd : ∀ ds : List (Fin 4), ds.length < N → ∀ x ∈ O,
      HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x)
    (ds : List (Fin 4)) (hds : ds.length ≤ N) :
    EqOn (partialJet (g []) ds) (g ds) O := by
  induction ds with
  | nil => intro x hx; rfl
  | cons i ds ih =>
    intro x hx
    have hlen : ds.length < N := by simp only [List.length_cons] at hds; omega
    have he : partialJet (g []) ds =ᶠ[𝓝 x] g ds := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact ih hlen.le hy
    change fderiv ℝ (partialJet (g []) ds) x (Pi.single i 1) = _
    rw [he.fderiv_eq,(hd ds hlen x hx).fderiv,realCoordinateDual_single]

theorem real_finite_local_jet_limit_contDiffOn (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (N : ℕ) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hc : ∀ ds : List (Fin 4), ds.length ≤ N → ContinuousOn (g ds) O)
    (hd : ∀ ds : List (Fin 4), ds.length < N → ∀ x ∈ O,
      HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x) :
    ContDiffOn ℝ N (g []) O := by
  have hn (k : ℕ) : ∀ ds : List (Fin 4), ds.length+k ≤ N → ContDiffOn ℝ k (g ds) O := by
    induction k with
    | zero => intro ds hh; exact contDiffOn_zero.mpr (hc ds (by omega))
    | succ k ih =>
      intro ds hh
      rw [show ((k+1:ℕ) : ℕ∞ω) = (k:ℕ∞ω)+1 by simp,contDiffOn_succ_iff_fderiv_of_isOpen hO]
      refine ⟨fun x hx ↦ (hd ds (by omega) x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
      have hs : ContDiffOn ℝ k (fun x ↦ realCoordinateDual (fun i ↦ g (i::ds) x)) O :=
        realCoordinateDual.contDiff.comp_contDiffOn
          (contDiffOn_pi.mpr (fun i ↦ ih (i::ds) (by simp only [List.length_cons]; omega)))
      apply hs.congr
      intro x hx
      exact (hd ds (by omega) x hx).fderiv
  exact hn N [] (by simp)

end
end Yau.Geometry

end OAI
