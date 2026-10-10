import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalRealSpan
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteSymmetryDecay
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.SymmetryRangeGenerator

namespace OAI

/-! # The real contour range is the real physical symmetry space -/

open scoped NNReal

namespace DefocusingNLS

theorem homogeneous_projection_real_frame_range (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    (hP : IsIdempotentElem P)
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 hk m q t) P)
    [FiniteDimensional ℂ P.range]
    (hgen : HasSymmetryRangeGenerator (homogeneousComplexLinearizedStep a b k ha ha1 hk m q) P hcomm)
    (D δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ t : ℝ≥0, ∀ z, P z = 0 →
      ‖homogeneousComplexLinearizedStep a b k ha ha1 hk m q t z‖ ≤
        D * Real.exp (-δ * (t : ℝ)) * ‖z‖)
    (F : ProfileSymmetryParameters →L[ℝ] HomogeneousY a k)
    (hspan : Submodule.span ℂ (Set.range (fun p => homogeneousComplexEmbed a k ha ha1 hk (F p))) = P.range)
    (u : HomogeneousY a k) :
    ∃ p, P (homogeneousComplexEmbed a k ha ha1 hk u) = homogeneousComplexEmbed a k ha ha1 hk (F p) := by
  let ι := homogeneousComplexEmbed a k ha ha1 hk
  let X := homogeneousComplexReal a k ha ha1 hk
  let Y := homogeneousComplexImag a k ha ha1 hk
  let S := homogeneousComplexLinearizedStep a b k ha ha1 hk m q
  let B := homogeneousLinearizedStep a b k ha ha1 hk m q
  let z := P (ι u)
  let w := ι u - z
  have hz : z ∈ P.range := ⟨ι u, rfl⟩
  have hzspan : z ∈ Submodule.span ℂ (Set.range (fun p => ι (F p))) := hspan ▸ hz
  obtain ⟨hp, hr⟩ := homogeneous_frame_real_coordinates a k ha ha1 hk F z hzspan
  obtain ⟨r, hr⟩ := hr
  have hYr : ι (Y z) ∈ P.range := by
    rw [← hspan, ← hr]
    exact Submodule.subset_span ⟨r, rfl⟩
  let v : P.range := ⟨ι (Y z), hYr⟩
  have hPw : P w = 0 := by
    have hi := congrArg (fun A => (A : _ →L[ℂ] _) (ι u)) hP
    change P (P (ι u)) = P (ι u) at hi
    simp only [w, z, map_sub, hi, sub_self]
  have hi (t : ℝ≥0) : Y (S t w) = -B t (Y z) := by
    dsimp only [w]
    rw [map_sub, map_sub]
    change Y (homogeneousComplexification a k ha ha1 hk (B t) (ι u)) -
      Y (homogeneousComplexification a k ha ha1 hk (B t) z) = _
    rw [homogeneousComplexification_embed, homogeneousComplexImag_embed,
      homogeneousComplexification_imag, zero_sub]
  have hn (t : ℝ≥0) : ‖S t (v : _)‖ ≤ D * Real.exp (-δ * (t : ℝ)) * ‖w‖ := by
    have he : ‖S t (v : _)‖ = ‖Y (S t w)‖ := by
      change ‖homogeneousComplexification a k ha ha1 hk (B t) (ι (Y z))‖ = _
      rw [homogeneousComplexification_embed, homogeneousComplexEmbed_norm, hi, norm_neg]
    rw [he]
    exact (homogeneousComplexImag_norm_le a k ha ha1 hk (S t w)).trans (hdecay t w hPw)
  obtain ⟨G, hG, hspec, hGspan⟩ := hgen
  have hv : v = 0 := by
    apply finite_symmetry_exp_decay_eq_zero G hGspan hspec v (D * ‖w‖) δ hδ
    intro t
    rw [← hG]
    change ‖S t (v : _)‖ ≤ _
    exact (hn t).trans_eq (by ring)
  have hY : Y z = 0 := by
    have he := congrArg (fun v : P.range => (v : HomogeneousY a k × HomogeneousY a k).1) hv
    exact he
  obtain ⟨p, hp⟩ := hp
  refine ⟨p, ?_⟩
  have he := homogeneousComplexEmbed_coordinates a k ha ha1 hk z
  change ι (X z) + Complex.I • ι (Y z) = z at he
  rw [hY, map_zero, smul_zero, add_zero] at he
  exact he.symm.trans (congrArg ι hp.symm)

end DefocusingNLS

end OAI
