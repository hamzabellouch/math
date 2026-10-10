import OAI.Geometry.SurfaceImmersion.Primitive.AdmissibleCrossingPath
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Localize a crossing-normal path by a smooth cutoff.  The resulting
section stays smooth even where the first pure vector vanishes outside
the cutoff support. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem supported_crossing_adjustment {U W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hWU : W ⊆ U) {n p q m : E → Vec} {χ : E → ℝ}
    (hn : ContDiffOn ℝ ∞ n U) (hp : ContDiffOn ℝ ∞ p W)
    (hχ : ContDiff ℝ ∞ χ) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hχsupport : tsupport χ ⊆ W) (hnunit : ∀ x ∈ U, n x ⬝ᵥ n x = 1)
    (hgeom : ∀ x ∈ W, n x ⬝ᵥ m x = 0 ∧ 0 < p x ⬝ᵥ m x ∧
      0 < q x ⬝ᵥ m x ∧ 0 < p x ⬝ᵥ q x) :
    let g := fun x => first (n x) (normalize (p x)) (χ x)
    ContDiffOn ℝ ∞ g U ∧
      (∀ x ∈ U, g x ⬝ᵥ g x = 1) ∧
      (∀ x ∈ U, x ∉ tsupport χ → g x = n x) ∧
      (∀ x ∈ W, g x ≠ -normalize (p x) ∧ g x ≠ -normalize (q x)) ∧
      (∀ x ∈ W, χ x = 1 → 0 < p x ⬝ᵥ g x ∧ 0 < q x ⬝ᵥ g x) ∧
      (∀ x ∈ U, ∀ v : Vec, v ⬝ᵥ n x = 0 → v ⬝ᵥ p x = 0 → v ⬝ᵥ g x = 0) := by
  dsimp only
  have hzero (x : E) (hx : x ∉ tsupport χ) : χ x = 0 := by
    by_contra he
    exact hx (subset_tsupport χ (Function.mem_support.mpr he))
  have heq (x : E) (hxU : x ∈ U) (hx : x ∉ tsupport χ) :
      first (n x) (normalize (p x)) (χ x) = n x := by
    rw [hzero x hx,first_zero (hnunit x hxU)]
  refine ⟨?_,?_,heq,?_,?_,?_⟩
  · intro x hxU
    by_cases hxW : x ∈ W
    · exact (crossing_normal_path_smoothAt
        (hn.contDiffAt (hU.mem_nhds hxU)) (hp.contDiffAt (hW.mem_nhds hxW))
        hχ.contDiffAt (hnunit x hxU) (hgeom x hxW).1 (hgeom x hxW).2.1
        (hχrange x)).contDiffWithinAt
    · have hx : x ∉ tsupport χ := fun h => hxW (hχsupport h)
      apply ((hn.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx,hU.mem_nhds hxU] with y hy hyU
      simp only [Pi.zero_apply] at hy
      rw [hy,first_zero (hnunit y hyU)]
  · intro x hxU
    by_cases hxW : x ∈ W
    · exact (crossing_normal_path (hnunit x hxU) (hgeom x hxW).1
        (hgeom x hxW).2.1 (hgeom x hxW).2.2.1 (hχrange x)).1
    · rw [heq x hxU (fun h => hxW (hχsupport h))]
      exact hnunit x hxU
  · intro x hx
    exact (crossing_normal_path (hnunit x (hWU hx)) (hgeom x hx).1
      (hgeom x hx).2.1 (hgeom x hx).2.2.1 (hχrange x)).2
  · intro x hx hχx
    rw [hχx]
    exact crossing_normal_path_endpoint (hgeom x hx).2.1 (hgeom x hx).2.2.2
  · intro x _ v hvn hvp
    change v ⬝ᵥ normalize (blend (n x) (normalize (p x)) (χ x)) = 0
    apply dot_normalize_zero
    simp only [blend,dotProduct_add,dotProduct_smul,smul_eq_mul,hvn,
      show v ⬝ᵥ normalize (p x) = 0 from dot_normalize_zero hvp,mul_zero,add_zero]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
