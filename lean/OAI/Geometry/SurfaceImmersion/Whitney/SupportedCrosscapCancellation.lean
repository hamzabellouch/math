import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapCancellationHeight

namespace OAI

/-! A compactly supported removal of the standard pair of crosscaps.
The replacement is an actual smooth immersion of the coordinate plane. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_supported_crosscap_cancellation :
    ∃ (F : Base → ProjectionTarget 3) (K : Set Base),
      ContDiff ℝ ∞ F ∧ (∀ x, Function.Injective (fderiv ℝ F x)) ∧
      IsCompact K ∧ ∀ x ∉ K, F x = crosscapPair 3 x := by
  obtain ⟨χ,R,hχ,hcompact,hR,hχ0,hpositive⟩ := exists_crosscap_cutoff_scale
  let F := triangularSurface (cancellationHeight χ R)
  let scale : ℝ × ℝ → Base := fun z => ![z.1,R*z.2]
  let K := scale '' ((tsupport χ) ×ˢ (tsupport χ))
  have hscale : Continuous scale := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_const.mul continuous_snd
  refine ⟨F,K,triangularSurface_smooth (cancellationHeight_smooth hχ R),?_,
    (hcompact.prod hcompact).image hscale,?_⟩
  · intro x
    apply triangularSurface_immersion (cancellationHeight_smooth hχ R)
    intro y hy
    rw [cancellationHeight_vertical hχ hχ0 R hy]
    exact hpositive (y 1)
  · intro x hx
    have hzero : χ (x 0)*χ (x 1/R) = 0 := by
      by_contra hn
      obtain ⟨h0,h1⟩ := mul_ne_zero_iff.mp hn
      apply hx
      refine ⟨(x 0,x 1/R),⟨subset_tsupport χ h0,subset_tsupport χ h1⟩,?_⟩
      ext i
      fin_cases i
      · rfl
      · change R*(x 1/R) = x 1
        field_simp [ne_of_gt hR]
    apply congrArg (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ext i
    fin_cases i
    · rfl
    · rfl
    · change (x 1)^3-3*x 1+4*χ (x 0)*χ (x 1/R)*x 1 = (x 1)^3-3*x 1
      have hz : 4*χ (x 0)*χ (x 1/R)*x 1 = 0 := by
        calc
          _ = 4*(χ (x 0)*χ (x 1/R))*x 1 := by ring
          _ = 0 := by rw [hzero]; ring
      rw [hz,add_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
