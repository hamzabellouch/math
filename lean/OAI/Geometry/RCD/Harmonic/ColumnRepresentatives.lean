import OAI.Geometry.RCD.Harmonic.CenteredColumns

namespace OAI

/-! # Pointwise representatives of the actual affine coordinate changes -/

open Set MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A Sobolev linear combination represents the corresponding scalar
pairing with the pointwise coordinate vector. -/
theorem sobolevColumnMap_representative {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (v : X → Euclidean n)
    (hu : ∀ i, SobolevSpace.toLp μ hQ (u i) =ᵐ[μ.restrict s] fun x => v x i)
    (a : Euclidean n) :
    SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u a) =ᵐ[μ.restrict s]
      fun x => ⟪v x, a⟫_ℝ := by
  classical
  change (SobolevSpace.toLpCLM μ hQ (sobolevColumnMap μ hQ u a)) =ᵐ[μ.restrict s] _
  rw [sobolevColumnMap_apply, map_sum]
  simp_rw [map_smul]
  change (∑ i, a i • SobolevSpace.toLp μ hQ (u i)) =ᵐ[μ.restrict s] _
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_finsetSum Finset.univ
    (fun i => a i • SobolevSpace.toLp μ hQ (u i))),
    ae_all_iff.2 (fun i => ae_restrict_of_ae (Lp.coeFn_smul (a i) (SobolevSpace.toLp μ hQ (u i)))),
    ae_all_iff.2 hu] with x hsum hsmul hrep
  rw [hsum]
  simp only [Finset.sum_apply]
  calc
    _ = ∑ i, a i * v x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsmul i]
      simp only [Pi.smul_apply, smul_eq_mul, hrep i]
    _ = ⟪v x, a⟫_ℝ := by simp only [PiLp.inner_apply, real_inner_comm, Real.inner_apply]

/-- Adding a compact local constant to transformed Sobolev columns gives
exactly the affine change of their pointwise vector representative. -/
theorem affineChangedColumn_representative {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (v : X → Euclidean n)
    (hu : ∀ i, SobolevSpace.toLp μ hQ (u i) =ᵐ[μ.restrict s] fun x => v x i)
    (B : Euclidean n →L[ℝ] Euclidean n) (b : Euclidean n →L[ℝ] ℝ)
    (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) (i : Fin n) :
    SobolevSpace.toLp μ hQ (affineChangedColumn μ hQ u B b η i) =ᵐ[μ.restrict s]
      fun x => (B.adjoint (v x)) i + b (EuclideanSpace.single i 1) := by
  change SobolevSpace.toLpCLM μ hQ
    (sobolevColumnMap μ hQ u (B (EuclideanSpace.single i 1)) + b (EuclideanSpace.single i 1) • η)
      =ᵐ[μ.restrict s] _
  rw [map_add, map_smul]
  change (SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u (B (EuclideanSpace.single i 1))) +
    b (EuclideanSpace.single i 1) • SobolevSpace.toLp μ hQ η) =ᵐ[μ.restrict s] _
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_add
    (SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u (B (EuclideanSpace.single i 1))))
    (b (EuclideanSpace.single i 1) • SobolevSpace.toLp μ hQ η)),
    ae_restrict_of_ae (Lp.coeFn_smul (b (EuclideanSpace.single i 1)) (SobolevSpace.toLp μ hQ η)),
    sobolevColumnMap_representative μ hQ u s v hu (B (EuclideanSpace.single i 1)), hη]
    with x hadd hsmul hcol hconst
  rw [hadd]
  simp only [Pi.add_apply, hcol, hsmul, Pi.smul_apply, smul_eq_mul, hconst, mul_one]
  congr 1
  have hh := ContinuousLinearMap.adjoint_inner_left B (EuclideanSpace.single i 1) (v x)
  simpa only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]
    using hh.symm

end RegularPointCoordinates

end

end OAI
