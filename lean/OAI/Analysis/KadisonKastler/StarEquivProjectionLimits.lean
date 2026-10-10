import OAI.Analysis.KadisonKastler.SemifiniteIsomorphism
import OAI.Analysis.FactorGeneration.NormalDimension

namespace OAI

/-! # Projection suprema and normality of an algebraic star isomorphism

The order isomorphism preserves directed projection suprema. Their concrete
vector limits therefore also hold in the target faithful representation.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

def algebraProjectionOrderIso (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    AlgebraProjection M ≃o AlgebraProjection N where
  toFun := mapAlgebraProjection e
  invFun := mapAlgebraProjection e.symm
  left_inv p := by apply Subtype.ext; exact e.symm_apply_apply p.val
  right_inv p := by apply Subtype.ext; exact e.apply_symm_apply p.val
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      apply e.injective
      change e (q.val * p.val) = e p.val
      rw [map_mul]
      exact h
    · exact mapAlgebraProjection_mono e

theorem starEquiv_projection_isLUB (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    {ι : Type*} (a : ι → AlgebraProjection M) (p : AlgebraProjection M)
    (hp : IsLUB (Set.range a) p) :
    IsLUB (Set.range (fun i => mapAlgebraProjection e (a i))) (mapAlgebraProjection e p) := by
  have h := (algebraProjectionOrderIso e).isLUB_image'.mpr hp
  rw [← Set.range_comp] at h
  change IsLUB (Set.range (fun i => mapAlgebraProjection e (a i)))
    (mapAlgebraProjection e p) at h
  exact h

theorem starEquiv_projection_vector_tendsto (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range a) p) (ξ : K) :
    Tendsto (fun i => AlgebraProjection.vectorValue ξ (mapAlgebraProjection e (a i))) atTop
      (𝓝 (AlgebraProjection.vectorValue ξ (mapAlgebraProjection e p))) :=
  AlgebraProjection.vectorValue_tendsto_monotone _
    (fun _ _ h => mapAlgebraProjection_mono e (ha h)) _
    (starEquiv_projection_isLUB e a p hp) ξ

theorem starEquiv_projection_strong_tendsto (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range a) p) (ξ : K) :
    Tendsto (fun i => (e (a i).val).val ξ) atTop (𝓝 ((e p.val).val ξ)) := by
  let b := fun i => mapAlgebraProjection e (a i)
  let q := mapAlgebraProjection e p
  have hb (i : ι) : b i ≤ q := mapAlgebraProjection_mono e (hp.1 ⟨i, rfl⟩)
  have hn (i : ι) : ‖(b i).val.val ξ - q.val.val ξ‖ =
      Real.sqrt (AlgebraProjection.vectorValue ξ q - AlgebraProjection.vectorValue ξ (b i)) := by
    have he := AlgebraProjection.vectorValue_remainder ξ (b i) q (hb i)
    rw [AlgebraProjection.vectorValue_eq_norm_sq] at he
    change ‖q.val.val ξ - (b i).val.val ξ‖ ^ 2 = _ at he
    rw [← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  have hv := starEquiv_projection_vector_tendsto e a ha p hp ξ
  change Tendsto (fun i => AlgebraProjection.vectorValue ξ (b i)) atTop
    (𝓝 (AlgebraProjection.vectorValue ξ q)) at hv
  have hd : Tendsto (fun i => AlgebraProjection.vectorValue ξ q -
      AlgebraProjection.vectorValue ξ (b i)) atTop (𝓝 0) := by
    simpa only [sub_self] using hv.const_sub (AlgebraProjection.vectorValue ξ q)
  have hs := (Real.continuous_sqrt.tendsto 0).comp hd
  change Tendsto (fun i => ‖(b i).val.val ξ - q.val.val ξ‖) atTop (𝓝 0)
  change Tendsto (fun i => Real.sqrt (AlgebraProjection.vectorValue ξ q -
    AlgebraProjection.vectorValue ξ (b i))) atTop (𝓝 (Real.sqrt 0)) at hs
  simpa only [hn, Real.sqrt_zero] using hs

end

end KadisonKastler

end OAI
