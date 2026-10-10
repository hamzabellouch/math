import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HarmonicSeminormBound

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] in

lemma harmonicAnti_dual_bound (f : L2 A J α hs ht true) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ v : antiEnergy A J α hs ht,
      |⟪f,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) :
    ‖(harmonicAnti A J α hs ht).starProjection f‖ ≤ M := by
  let K := harmonicAnti A J α hs ht
  obtain ⟨v,hv,hd⟩ := (mem_harmonicAnti A J α hs ht (K.starProjection f)).mp
    (K.starProjection_apply_mem f)
  have hn : ‖v‖ = ‖K.starProjection f‖ := by
    have hg := WithLp.prod_norm_sq_eq_of_L2 v.val
    change ‖v‖^2 = ‖energyInclusion A J α hs ht v‖^2 + ‖weakDelta A J α hs ht v‖^2 at hg
    rw [hv,hd,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero] at hg
    nlinarith [norm_nonneg v,norm_nonneg (K.starProjection f)]
  have hp : K.starProjection (K.starProjection f) = K.starProjection f :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem f)
  have hi : ⟪f,K.starProjection f⟫ = ‖K.starProjection f‖^2 := by
    have h := K.inner_starProjection_left_eq_right f (K.starProjection f)
    rw [hp,real_inner_self_eq_norm_sq] at h
    exact h.symm
  have h := hb v
  rw [hv,hn,hi,abs_of_nonneg (sq_nonneg _)] at h
  change ‖K.starProjection f‖ ≤ M
  by_cases hz : ‖K.starProjection f‖ = 0
  · rw [hz]; exact hM
  · have hp : 0 < ‖K.starProjection f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

variable (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

include hD in

lemma harmonic_schwartz_dual_derivative_bound
    (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      ∀ n ≤ N, ∀ v : Fin n → E, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (F₀ h)) x‖ ≤ C*M := by
  obtain ⟨C,hC,hbound⟩ := harmonic_schwartz_derivative_bound A J α hs ht D hD F₀ N
  refine ⟨C,hC,fun f h hh M hM hb n hn v hv x => ?_⟩
  have hself : smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
      (smoothL2 A J α hs ht true h.val) := by
    rw [hh,(harmonicAnti A J α hs ht).starProjection_eq_self_iff.mpr
      ((harmonicAnti A J α hs ht).starProjection_apply_mem _)]
  have hp := harmonicAnti_dual_bound A J α hs ht _ M hM hb
  rw [← hh] at hp
  exact (hbound h h hself n hn v hv x).trans (mul_le_mul_of_nonneg_left hp hC)
end TamingCompatibility.GeometricHilbert

end

end OAI
