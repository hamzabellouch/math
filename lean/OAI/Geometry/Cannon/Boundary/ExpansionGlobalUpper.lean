import Mathlib
import OAI.Geometry.Cannon.Boundary.ImageAwayPuncture

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonPaths
lemma expansion_global_upper {R C d q a b : ℝ} (hR : 0<R) (hq : 0≤q)
    (hexp : q*max R a*max R b≤C*R*d) : q*R≤C*d := by
  have hh : q*R*R≤C*R*d := by
    calc
      q*R*R ≤ q*max R a*max R b := by gcongr <;> exact le_max_left ..
      _ ≤ C*R*d := hexp
  apply (mul_le_mul_iff_right₀ hR).mp
  nlinarith
end CannonPaths

namespace CannonRelease
open CannonGraph CannonVisual CannonPaths Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance expansionGlobalUpperSetoid : Setoid (BasedRay D) := raySetoid D

theorem boundary_uniform_expanding_homeomorphs :
    let _ := visualMetricSpace D hδ
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (x : Boundary D) (s : ℝ), 0<s → s≤1 →
      ∃ f : Boundary D ≃ₜ Boundary D,
        (∀ y z, dist (f y) (f z)*s≤C*dist y z) ∧
        (∀ y, s≤dist x y → η≤dist (f x) (f y)) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  let C := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let B := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hC : 0<C := by dsimp [C]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hA : 1≤A := Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (visualExponent_pos δ).le)
  have hAp : 0<A := zero_lt_one.trans_le hA
  refine ⟨C,1/(B*A),hC,by positivity,?_⟩
  intro x s hs hs₁
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hs hs₁
  obtain ⟨r,hr⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹
  refine ⟨f,?_,?_⟩
  · intro y z
    have h := expansion_global_upper (visualScale_pos δ k) dist_nonneg
      (visual_expansion_ray D hδ r k y z).1
    change dist (f y) (f z)*visualScale δ k≤C*dist y z at h
    exact (mul_le_mul_of_nonneg_left hk dist_nonneg).trans h
  · intro y hy
    have h := (visual_expansion_ray D hδ r k (Quotient.mk' r) y).2
    change visualScale δ k*boundaryDist D hδ (Quotient.mk' r) y ≤
      B*(boundaryDist D hδ (f (Quotient.mk' r)) (f y)*
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)) *
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) y)) at h
    have hself : boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)=0 := dist_self _
    rw [hself,max_eq_left (visualScale_pos δ k).le] at h
    exact expansion_endpoint_clearance (visualScale_pos δ k) hB hA hs dist_nonneg hy hk' h

end CannonRelease

end
end
end
end
end
end

end OAI
