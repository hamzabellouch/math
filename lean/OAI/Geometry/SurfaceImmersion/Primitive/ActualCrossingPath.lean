import OAI.Geometry.SurfaceImmersion.Primitive.AdmissibleCrossingPath
import OAI.Geometry.SurfaceImmersion.Primitive.CompactCrossingNormal

namespace OAI

/-! The admissible crossing path is a unit section of the actual normal
plane, and its endpoint pairs positively with both actual pure forms. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
namespace SecondFormFrame
variable {F : RField 4} {p : Base} {k : ℝ} (d : SecondFormFrame F p k)

theorem actual_crossing_path (hF : ContDiff ℝ ∞ F) (t u : ℝ)
    (hchoice :
      (0 < inner ℝ (frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (slopePure d.S d.D d.N d.L k t)) (spaceCoordinates.symm d.n) ∧
       0 < inner ℝ (frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (slopePure d.S d.D d.N d.L k u)) (spaceCoordinates.symm d.n)) ∨
      (0 < inner ℝ (frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (slopePure d.S d.D d.N d.L k t))
        (frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (slopePure d.S d.D d.N d.L k u)) ∧
       ∃ w : Space, inner ℝ (spaceCoordinates.symm d.n) w = 0 ∧
        0 < inner ℝ (frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
          (slopePure d.S d.D d.N d.L k t)) w ∧
        0 < inner ℝ (frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
          (slopePure d.S d.D d.N d.L k u)) w)) :
    ∃ γ : ℝ → Vec, ContDiffOn ℝ ∞ γ (Icc (0 : ℝ) 1) ∧ γ 0 = d.n ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        γ s ⬝ᵥ γ s = 1 ∧
        γ s ≠ -normalize (realSecondForm F (1,t) (1,t) p) ∧
        γ s ≠ -normalize (realSecondForm F (1,u) (1,u) p) ∧
        coordDeriv dx F p ⬝ᵥ γ s = 0 ∧ coordDeriv dy F p ⬝ᵥ γ s = 0) ∧
      0 < realSecondForm F (1,t) (1,t) p ⬝ᵥ γ 1 ∧
      0 < realSecondForm F (1,u) (1,u) p ⬝ᵥ γ 1 := by
  rw [← d.slope_space_components hF t,← d.slope_space_components hF u] at hchoice
  have hraw :
      (0 < realSecondForm F (1,t) (1,t) p ⬝ᵥ d.n ∧
       0 < realSecondForm F (1,u) (1,u) p ⬝ᵥ d.n) ∨
      (0 < realSecondForm F (1,t) (1,t) p ⬝ᵥ realSecondForm F (1,u) (1,u) p ∧
       ∃ w : Vec, d.n ⬝ᵥ w = 0 ∧
        0 < realSecondForm F (1,t) (1,t) p ⬝ᵥ w ∧
        0 < realSecondForm F (1,u) (1,u) p ⬝ᵥ w) := by
    rcases hchoice with hpos | ⟨hpq,w,hnw,hpw,hqw⟩
    · left
      simpa only [spaceCoordinates_symm_inner] using hpos
    · right
      refine ⟨by simpa only [spaceCoordinates_symm_inner] using hpq,spaceCoordinates w,?_,?_,?_⟩
      · simpa only [← spaceCoordinates_symm_inner,ContinuousLinearEquiv.symm_apply_apply] using hnw
      · simpa only [← spaceCoordinates_symm_inner,ContinuousLinearEquiv.symm_apply_apply] using hpw
      · simpa only [← spaceCoordinates_symm_inner,ContinuousLinearEquiv.symm_apply_apply] using hqw
  obtain ⟨γ,hγ,hzero,hunit,hend⟩ := admissible_crossing_path d.unit_n hraw
  refine ⟨γ,hγ,hzero,?_,hend⟩
  intro s hs
  obtain ⟨hu,hp,hq,hperp⟩ := hunit s hs
  have htangent (v : Base) (hv : coordDeriv v F p ⬝ᵥ d.n = 0)
      (hvm : coordDeriv v F p ⬝ᵥ d.m = 0) : coordDeriv v F p ⬝ᵥ γ s = 0 := by
    apply hperp _ hv
    rw [d.pure_components hF]
    simp only [dotProduct_add,dotProduct_smul,smul_eq_mul,hv,hvm,mul_zero,add_zero]
  exact ⟨hu,hp,hq,htangent dx d.tangent_n.1 d.tangent_m.1,
    htangent dy d.tangent_n.2 d.tangent_m.2⟩

end SecondFormFrame
end ClosedSurfaceR4.GeometryPreservation

end

end OAI
