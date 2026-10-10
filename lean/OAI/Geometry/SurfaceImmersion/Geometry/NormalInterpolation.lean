import OAI.Geometry.SurfaceImmersion.Primitive.VelocityFrame

namespace OAI

/-! Convex interpolation of unit normals on the exterior collar retains
normality and every strictly positive pairing along the later curves. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma dot_gt_neg_one_of_ne_antipode {u v : Vec}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (hne : u ≠ -v) : -1 < u ⬝ᵥ v := by
  have hsum : u+v ≠ 0 := by
    intro hz
    exact hne (eq_neg_of_add_eq_zero_left hz)
  have hp := dot_self_pos hsum
  simp only [add_dotProduct,dotProduct_add,hu,hv,dotProduct_comm v u] at hp
  linarith

lemma first_pairing_pos {u v w : Vec} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : 0 < w ⬝ᵥ u) (hv : 0 < w ⬝ᵥ v) :
    0 < w ⬝ᵥ first u v t := by
  have hp : 0 < w ⬝ᵥ blend u v t := by
    simp only [blend,dotProduct_add,dotProduct_smul,smul_eq_mul]
    by_cases ht0 : t = 0
    · simpa only [ht0,sub_zero,one_mul,zero_mul,add_zero] using hu
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) hu.le) (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hv)
  have hn : blend u v t ≠ 0 := by
    intro hz
    rw [hz,dotProduct_zero] at hp
    exact lt_irrefl 0 hp
  change 0 < w ⬝ᵥ normalize (blend u v t)
  rw [normalize,dotProduct_smul]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (dot_self_pos hn))) hp

theorem normal_interpolation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {u v : E → Vec} {t : E → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (ht : ContDiffOn ℝ ∞ t U)
    (hu1 : ∀ x ∈ U, u x ⬝ᵥ u x = 1) (hv1 : ∀ x ∈ U, v x ⬝ᵥ v x = 1)
    (hne : ∀ x ∈ U, u x ≠ -v x) (htr : ∀ x ∈ U, t x ∈ Icc (0 : ℝ) 1) :
    let n := fun x => first (u x) (v x) (t x)
    ContDiffOn ℝ ∞ n U ∧ (∀ x ∈ U, n x ⬝ᵥ n x = 1) ∧
      (∀ x ∈ U, t x = 0 → n x = u x) ∧
      (∀ x ∈ U, t x = 1 → n x = v x) ∧
      (∀ x ∈ U, ∀ w : Vec, w ⬝ᵥ u x = 0 → w ⬝ᵥ v x = 0 → w ⬝ᵥ n x = 0) ∧
      (∀ x ∈ U, ∀ w : Vec, 0 < w ⬝ᵥ u x → 0 < w ⬝ᵥ v x → 0 < w ⬝ᵥ n x) := by
  dsimp only
  have hdot (x : E) (hx : x ∈ U) : -1 < u x ⬝ᵥ v x :=
    dot_gt_neg_one_of_ne_antipode (hu1 x hx) (hv1 x hx) (hne x hx)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact (first_smoothAt (hu.contDiffAt (hU.mem_nhds hx))
      (hv.contDiffAt (hU.mem_nhds hx)) (ht.contDiffAt (hU.mem_nhds hx))
      (hu1 x hx) (hv1 x hx) (hdot x hx) (htr x hx)).contDiffWithinAt
  · intro x hx
    exact first_unit (hu1 x hx) (hv1 x hx) (hdot x hx) (htr x hx)
  · intro x hx hzero
    rw [hzero,first_zero (hu1 x hx)]
  · intro x hx hone
    rw [hone,first_one (hv1 x hx)]
  · intro x _ w hwu hwv
    exact first_perp hwu hwv _
  · intro x hx w hwu hwv
    exact first_pairing_pos (htr x hx) hwu hwv

end ClosedSurfaceR4.VelocityFrame

end

end OAI
