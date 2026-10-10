import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicSeparation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolynomialMoment

namespace OAI

/-! # The angular dimension bound from a single radial mode line -/

open Set MeasureTheory
open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_contour_eigenspace_dimension (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (N : ℕ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < (N : ℝ))
    (q : HomogeneousY (radialShootingA n) N)
    (hq : ∀ x : E, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk q x =
      radialMatchedCartesian n z x)
    (P : (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) →L[ℂ]
      (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
      (n + radialInnerShootingThreshold) q t) P)
    (hfin : FiniteDimensional ℂ P.range) (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
        (n + radialInnerShootingThreshold) q) P hcomm t = NormedSpace.exp ((t : ℝ) • G))
    (lam : ℂ) (ell₀ : ℕ)
    (hclass : ∀ (ell : ℕ), Nonempty (RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
      (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) lam) → ell = ell₀)
    (hline : RadialModeLine n z ell₀ 9 lam)
    {J : Type*} [Fintype J] (p : J → PhysicalRealPolynomial)
    (hspan : ∀ L : PhysicalRealPolynomial →ₗ[ℝ] ℂ, (∀ j, L (p j) = 0) →
      ∀ q : PhysicalRealPolynomial, q.IsHomogeneous ell₀ → L q = 0) :
    Module.finrank ℂ (Module.End.eigenspace G.toLinearMap lam) ≤ Fintype.card J := by
  classical
  let S := Module.End.eigenspace G.toLinearMap lam
  by_cases hs : S = ⊥
  · change Module.finrank ℂ S ≤ _
    rw [hs]
    simp
  obtain ⟨w, hws, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  have he : G w = lam • w := Module.End.mem_eigenspace_iff.mp hws
  obtain ⟨ell, ⟨u₀⟩⟩ := homogeneous_matched_contour_radialMode_fixed n z hX hz N ha ha1 hk
    q hq P hcomm hfin G hG lam w hw he
  have hel := hclass ell ⟨u₀⟩
  subst ell
  obtain ⟨first, r₀, hr₀, hu₀⟩ := radialModeTrace_exists u₀
  let L : S →ₗ[ℂ] (J → ℂ) := LinearMap.pi fun j =>
    (homogeneousPairHarmonicMoment (radialShootingA n) N ha ha1 hk
      (physicalHarmonicExtension (p j) ell₀)
      (continuous_harmonicSphere _ (physicalHarmonicExtension_contDiffAt (p j) ell₀)) first r₀).comp
      (P.range.subtype.comp S.subtype)
  have hker : ∀ v : S, L v = 0 → v = 0 := by
    intro v hv
    apply Subtype.ext
    apply homogeneous_contour_harmonic_trace_separates n z hX hz N ha ha1 hk q hq P hcomm
      hfin G hG lam v.val (Module.End.mem_eigenspace_iff.mp v.property)
      ell₀ hclass hline u₀ first r₀ hr₀ hu₀
    intro q hq _
    exact homogeneousPairPolynomialMoment_complete (radialShootingA n) N ha ha1 hk ell₀
      p hspan first r₀ v.val (fun j => congrFun hv j) q hq
  have hinj : Function.Injective L := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, huv, sub_self]
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] using L.finrank_le_finrank_of_injective hinj

end DefocusingNLS

end OAI
