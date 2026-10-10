import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryModulusBounded
import OAI.Geometry.Cannon.Energy.ApproxSelfSimilar

namespace OAI

section
section
section
noncomputable section
namespace CannonRelease
open CannonGraph CannonVisual CannonGeometry CannonNet CannonCells CannonCharts Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniformization_inputs (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d κ : ℝ, 0 < d → d < diam (univ : Set (Boundary D))/10 →
      d ≤ 1/(LE*3^2) → 2*a < κ →
    PathConnectedSpace (Boundary D) ∧ ApproxSelfSimilar (Boundary D) ∧
    ∃ T : ℕ → Finset (Boundary D), ∃ N : ℕ → ℕ, ∃ B : ℝ, ∀ m,
      IsApproximation (fun i : T (N m) => i.val)
        (fun i : T (N m) => ball i.val (2*(a^(N m))⁻¹)) ((2:ℝ)^m)⁻¹ κ ∧
      modulus (fun i : T (N m) => ball i.val (2*(a^(N m))⁻¹)) (macroFamily d) ≤ B := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro d κ hd hdia hdc hκ
  let a := Real.exp (2*visualExponent δ)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  let _ : PathConnectedSpace SphereTwo := CannonCharts.sphere_pathConnected
  refine ⟨φ.symm.surjective.pathConnectedSpace φ.symm.continuous,
    boundary_approx_self_similar D hδ,?_⟩
  obtain ⟨T,hT⟩ := exists_net_sequence (X:=Boundary D) ha
  have hscale (m : ℕ) : ∃ n : ℕ,
      ((2:ℝ)^m)⁻¹/a < (a^n)⁻¹ ∧ (a^n)⁻¹ ≤ ((2:ℝ)^m)⁻¹ := by
    apply exists_scale_below ha (by positivity)
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  choose N hNlow hNupp using hscale
  have hsep (n : ℕ) (i j : T n) (hij : i ≠ j) : (a^n)⁻¹ ≤ dist i.val j.val :=
    (hT n).1 i.val i.property j.val j.property (fun hh => hij (Subtype.ext hh))
  have hnet (n : ℕ) (x : Boundary D) : ∃ i : T n, dist i.val x ≤ (a^n)⁻¹ := by
    obtain ⟨y,hy,hh⟩ := (hT n).2 x
    exact ⟨⟨y,hy⟩,hh⟩
  have hdia' : d < diam (univ : Set (Boundary D)) := by
    have := diam_nonneg (s:= (univ : Set (Boundary D)))
    linarith
  obtain ⟨B,hB⟩ := boundary_modulus_bounded D hδ φ d hd hdia' hdc
    (fun n => ↥(T n)) (fun n i => i.val) hsep hnet
  refine ⟨T,N,B,?_⟩
  intro m
  exact ⟨balls_isApproximation (fun i : T (N m) => i.val) ha (by positivity) hκ
    (hNlow m) (hNupp m) (hsep (N m)) (hnet (N m)),hB (N m)⟩

end CannonRelease

end
end
end
end

end OAI
