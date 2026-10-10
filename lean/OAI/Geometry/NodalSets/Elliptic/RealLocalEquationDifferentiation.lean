import OAI.Geometry.NodalSets.Elliptic.RealCutoffIntegralsLemmas

namespace OAI

namespace Yau.Geometry
open Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_local_inhomogeneous_differentiation
    (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W f : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i))
    (he : ∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x)
    (k : Fin 4) :
    ∀ x ∈ O, Yau.coordDiv (realMatrixFlux C (fun y ↦ Yau.coordPartial W y k)) x+
      V x*Yau.coordPartial W x k =
      Yau.coordDiv (fun y i ↦ Yau.coordPartial (fun z ↦ F z i) y k-realDerivativeErrorFlux C W k y i) x+
        (Yau.coordPartial f x k-Yau.coordPartial V x k*W x) := by
  have hflux := realMatrixFlux_smooth C W hC hW
  have hdiv : ContDiff ℝ ∞ (Yau.coordDiv (realMatrixFlux C W)) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hflux i) i)
  have hdivF : ContDiff ℝ ∞ (Yau.coordDiv F) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hF i) i)
  intro x hx
  have heg : (fun y ↦ Yau.coordDiv (realMatrixFlux C W) y+V y*W y) =ᶠ[𝓝 x]
      (fun y ↦ Yau.coordDiv F y+f y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact he y hy
  have hd := congrArg (fun D : Yau.Jets.Coord →L[ℝ] ℝ ↦ D (Pi.single k 1))
    (heg.fderiv_eq (𝕜 := ℝ))
  change Yau.coordPartial (fun y ↦ Yau.coordDiv (realMatrixFlux C W) y+V y*W y) x k =
    Yau.coordPartial (fun y ↦ Yau.coordDiv F y+f y) x k at hd
  rw [Yau.real_coordPartial_add _ _ hdiv (hV.mul hW),Yau.real_coordPartial_mul _ _ hV hW,
    Yau.real_coordPartial_add _ _ hdivF hf,real_coordDiv_partial _ hflux,real_coordDiv_partial _ hF] at hd
  have hpart : (fun y i ↦ Yau.coordPartial (fun z ↦ realMatrixFlux C W z i) y k) =
      fun y i ↦ realDerivativeErrorFlux C W k y i+realMatrixFlux C (fun z ↦ Yau.coordPartial W z k) y i := by
    funext y i; exact realMatrixFlux_partial C W hC hW y i k
  rw [hpart,real_coordDiv_add _ _ (realDerivativeErrorFlux_smooth C W k hC hW)
    (realMatrixFlux_smooth C _ hC (Yau.real_coordPartial_smooth W hW k))] at hd
  rw [real_coordDiv_sub _ _ (fun i ↦ Yau.real_coordPartial_smooth _ (hF i) k)
    (realDerivativeErrorFlux_smooth C W k hC hW)]
  linarith only [hd]

end
end Yau.Geometry

end OAI
