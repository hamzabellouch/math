import OAI.Geometry.SurfaceImmersion.Primitive.SupportedCrossingAdjustment

namespace OAI

/-! Extend a pointwise common half-plane to a neighborhood, with an
explicit smooth transverse vector field. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem crossing_halfplane_neighborhood {U : Set E} (hU : IsOpen U)
    {n p q : E → Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    (hunit : ∀ x ∈ U, n x ⬝ᵥ n x = 1) {x : E} (hx : x ∈ U) {w : Vec}
    (hnw : n x ⬝ᵥ w = 0) (hpw : 0 < p x ⬝ᵥ w) (hqw : 0 < q x ⬝ᵥ w)
    (hpq : 0 < p x ⬝ᵥ q x) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ m : E → Vec, ContDiffOn ℝ ∞ m U ∧
        ∀ y ∈ W, n y ⬝ᵥ m y = 0 ∧ 0 < p y ⬝ᵥ m y ∧
          0 < q y ⬝ᵥ m y ∧ 0 < p y ⬝ᵥ q y := by
  let m : E → Vec := fun y => w-(n y ⬝ᵥ w) • n y
  have hm : ContDiffOn ℝ ∞ m U :=
    contDiffOn_const.sub ((dot_smoothOn hn contDiffOn_const).smul hn)
  have hmx : m x = w := by simp [m,hnw]
  have hP : ∀ᶠ y in 𝓝 x, 0 < p y ⬝ᵥ m y :=
    ((dot_smoothOn hp hm).contDiffAt (hU.mem_nhds hx)).continuousAt
      (Ioi_mem_nhds (by simpa only [hmx] using hpw))
  have hQ : ∀ᶠ y in 𝓝 x, 0 < q y ⬝ᵥ m y :=
    ((dot_smoothOn hq hm).contDiffAt (hU.mem_nhds hx)).continuousAt
      (Ioi_mem_nhds (by simpa only [hmx] using hqw))
  have hPQ : ∀ᶠ y in 𝓝 x, 0 < p y ⬝ᵥ q y :=
    ((dot_smoothOn hp hq).contDiffAt (hU.mem_nhds hx)).continuousAt (Ioi_mem_nhds hpq)
  have hnb : {y | y ∈ U ∧ 0 < p y ⬝ᵥ m y ∧ 0 < q y ⬝ᵥ m y ∧ 0 < p y ⬝ᵥ q y} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hx,hP,hQ,hPQ] with y hy hyP hyQ hyPQ
    exact ⟨hy,hyP,hyQ,hyPQ⟩
  obtain ⟨W,hsub,hW,hxW⟩ := mem_nhds_iff.mp hnb
  refine ⟨W,hW,hxW,fun y hy => (hsub hy).1,m,hm,?_⟩
  intro y hy
  obtain ⟨hyU,hyP,hyQ,hyPQ⟩ := hsub hy
  refine ⟨?_,hyP,hyQ,hyPQ⟩
  simp only [m,dotProduct_sub,dotProduct_smul,smul_eq_mul,hunit y hyU,mul_one,sub_self]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
