import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators
open Filter

namespace SmoothLocal.Geometry

abbrev Coord := Fin 2 → ℝ

def coordPartial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : Fin 2) (f : Coord → V) (p : Coord) : V :=
  fderiv ℝ f p (Pi.single i 1)

section Height
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {F : Coord → V} {p : Coord} {U : Set Coord}

theorem partial_height (hF : DifferentiableAt ℝ F p) (e : V) (i : Fin 2) :
    coordPartial i (fun q => inner ℝ (F q) e) p = inner ℝ (coordPartial i F p) e := by
  simpa [coordPartial] using
    (fderiv_inner_apply ℝ hF (differentiableAt_const (c := e)) (Pi.single i 1))

theorem partial_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordPartial i F) U := by
  exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem second_partial_height (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (e : V) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => inner ℝ (F q) e)) p =
      inner ℝ (coordPartial i (coordPartial j F) p) e := by
  have hlocal : coordPartial j (fun q => inner ℝ (F q) e) =ᶠ[𝓝 p]
      (fun q => inner ℝ (coordPartial j F q) e) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact partial_height
      (((hF q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)) e j
  have hd : DifferentiableAt ℝ (coordPartial j F) p :=
    (((partial_contDiffOn hF hU j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  change fderiv ℝ (coordPartial j (fun q => inner ℝ (F q) e)) p (Pi.single i 1) = _
  rw [hlocal.fderiv_eq]
  exact partial_height hd e i

theorem height_differential_zero (hF : DifferentiableAt ℝ F p) (e : V)
    (he : ∀ v, inner ℝ (fderiv ℝ F p v) e = 0) :
    fderiv ℝ (fun q => inner ℝ (F q) e) p = 0 := by
  ext v
  simpa [he v] using
    (fderiv_inner_apply ℝ hF (differentiableAt_const (c := e)) v)

theorem hessian_height_eq_residual_inner (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (e : V) (Γ : Fin 2 → Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => inner ℝ (F q) e)) p -
      ∑ k, Γ k i j * coordPartial k (fun q => inner ℝ (F q) e) p =
    inner ℝ (coordPartial i (coordPartial j F) p - ∑ k, Γ k i j • coordPartial k F p) e := by
  have hd : DifferentiableAt ℝ F p :=
    ((hF p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [second_partial_height hF hU hp, partial_height hd,
    inner_sub_left, sum_inner, real_inner_smul_left]

end Height
end SmoothLocal.Geometry

end

end OAI
