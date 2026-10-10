import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateFlowProfileIdentity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.GoodProfileFlow

namespace OAI

/-! # Physical height bounds on the actual profile legs -/

noncomputable section

namespace PolycyclicRecognition

open Module Set

/-- Good profile values on the actual polynomial horizontal flow control
precisely the physical one-parameter leg at scale `exp s`. -/
theorem rescaled_profile_leg_bound
    {L D N G W : Type*} [LieRing L] [LieAlgebra ℝ L]
    [Group D] [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n c : ℕ} (ExpD : L → D) (b : Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpD (finiteDynkinPolynomial a ![x, y]) = ExpD x * ExpD y)
    (ι : N → G) (κ : D →* G) (J : G → W) (x : G) (s : ℝ)
    (v : L) (z : Fin n → ℝ) (T : ℝ) (A : Set N)
    (flow : (Fin n → ℝ) × ℝ → Fin n → ℝ) (f : (Fin n → ℝ) → W) (ε : ℝ)
    (hgood : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) T,
      ‖rescaledMapProfile J x (ι u) s (fun y => κ (ExpD (b.equivFun.symm y)))
          (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp s • v)) (z, t)) -
        f (flow (z, t))‖ ≤ ε) :
    ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) T,
      ‖J ((x * ι u * κ (ExpD (b.equivFun.symm z))) *
          κ (ExpD ((Real.exp s * t) • v))) - J x -
        Real.exp s • f (flow (z, t))‖ ≤ Real.exp s * ε := by
  intro u hu t ht
  have hh := height_bound_of_rescaled_profile J x (ι u) s
    (fun y => κ (ExpD (b.equivFun.symm y)))
    (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp s • v)) (z, t))
    (f (flow (z, t))) (hgood u hu t ht)
  rw [exp_basis_horizontal_flow ExpD b a hm, map_mul] at hh
  simpa only [mul_assoc] using hh

/-- The preceding bound describes the image of the whole leg by the fixed
limiting segment image, including every time used in the support visits. -/
theorem rescaled_profile_leg_image
    {L D N G W : Type*} [LieRing L] [LieAlgebra ℝ L]
    [Group D] [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n c : ℕ} (ExpD : L → D) (b : Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpD (finiteDynkinPolynomial a ![x, y]) = ExpD x * ExpD y)
    (ι : N → G) (κ : D →* G) (J : G → W) (x : G) (s : ℝ)
    (v : L) (z : Fin n → ℝ) (T : ℝ) (A : Set N)
    (flow : (Fin n → ℝ) × ℝ → Fin n → ℝ) (f : (Fin n → ℝ) → W) (ε : ℝ)
    (hgood : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) T,
      ‖rescaledMapProfile J x (ι u) s (fun y => κ (ExpD (b.equivFun.symm y)))
          (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp s • v)) (z, t)) -
        f (flow (z, t))‖ ≤ ε) :
    ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) T,
      ∃ w ∈ (fun t => f (flow (z, t))) '' Icc (0 : ℝ) T,
        ‖J ((x * ι u * κ (ExpD (b.equivFun.symm z))) *
            κ (ExpD ((Real.exp s * t) • v))) - J x - Real.exp s • w‖ ≤ Real.exp s * ε := by
  intro u hu t ht
  exact ⟨f (flow (z, t)), ⟨t, ht, rfl⟩,
    rescaled_profile_leg_bound ExpD b a hm ι κ J x s v z T A flow f ε hgood u hu t ht⟩

end PolycyclicRecognition

end

end OAI
