import OAI.Combinatorics.Crossing.OffsetVectors
import Mathlib.Tactic.FunProp

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

def dot2 (u v : Plane) : ℝ := u.1*v.1+u.2*v.2

theorem planar_vector_decomposition (u v : Plane) :
    squaredLength u • v = dot2 u v • u+det2 u v • rotateQuarter u := by
  apply Prod.ext <;> dsimp [squaredLength,dot2,det2,rotateQuarter] <;> ring

theorem vector_parallel_of_det_zero (u v : Plane) (hu : u ≠ 0) (h : det2 u v=0) :
    v = (dot2 u v/squaredLength u) • u := by
  have hs := ne_of_gt (squaredLength_pos u hu)
  have hh := planar_vector_decomposition u v
  rw [h,zero_smul,add_zero] at hh
  calc
    v = (squaredLength u)⁻¹ • (squaredLength u • v) := by rw [smul_smul,inv_mul_cancel₀ hs,one_smul]
    _ = (squaredLength u)⁻¹ • (dot2 u v • u) := by rw [hh]
    _ = _ := by rw [smul_smul,div_eq_mul_inv,mul_comm]

theorem offset_direction_det_zero (a b qa qb : Plane) (ε : ℝ)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) :
    det2 (b-a) ((b+ε • qb)-(a+ε • qa)) = 0 := by
  dsimp [det2] at *
  linear_combination ε*hb-ε*ha

theorem exists_forward_offset_radius (a b qa qb : Plane) (hab : b ≠ a)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ →
      ∃ r : ℝ, 0<r ∧ (b+ε • qb)-(a+ε • qa) = r • (b-a) := by
  have hn : b-a ≠ 0 := sub_ne_zero.mpr hab
  have hlen := squaredLength_pos (b-a) hn
  let f : ℝ → ℝ := fun ε => dot2 (b-a) ((b+ε • qb)-(a+ε • qa)) / squaredLength (b-a)
  have hf : Continuous f := by
    dsimp [f,dot2,squaredLength]
    fun_prop
  have hf0 : 0<f 0 := by
    have he : f 0=1 := by
      dsimp [f]
      simp only [zero_smul,add_zero]
      have hd : dot2 (b-a) (b-a)=squaredLength (b-a) := by dsimp [dot2,squaredLength]; ring
      rw [hd]
      exact div_self (ne_of_gt hlen)
    rw [he]
    norm_num
  have hevent : ∀ᶠ ε : ℝ in 𝓝 0, 0<f ε := continuousAt_const.eventually_lt hf.continuousAt hf0
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  refine ⟨f ε,hd (by simpa [Real.dist_eq] using hε),?_⟩
  exact vector_parallel_of_det_zero (b-a) _ hn (offset_direction_det_zero a b qa qb ε ha hb)

end Zarankiewicz

end

end OAI
