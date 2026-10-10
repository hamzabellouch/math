import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricFredholm

namespace OAI


noncomputable section
namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma energy_inverse_dual_bound (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (K : Submodule ℝ H) [CompleteSpace K] (G : H →L[ℝ] V)
    (hgraph : ∀ u, ‖u‖^2 = ‖i u‖^2 + ‖D u‖^2)
    (hweak : ∀ f v, ⟪D (G f),D v⟫ = ⟪f-K.starProjection f,i v⟫)
    (horth : ∀ f, i (G f) ∈ Kᗮ) (f : H) (M : ℝ) (hM : 0 ≤ M)
    (hdual : ∀ v, |⟪f,i v⟫| ≤ M * ‖v‖) :
    ‖G f‖ ≤ (1 + (‖D‖ * ‖G‖)^2) * M := by
  let u := G f
  let q := ‖D‖ * ‖G‖
  have hq : 0 ≤ q := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hproj (a : H) : ⟪K.starProjection a,i u⟫ = 0 :=
    K.inner_right_of_mem_orthogonal (K.starProjection_apply_mem a) (horth f)
  have hw := hweak (i u) u
  rw [inner_sub_left,hproj,sub_zero,real_inner_self_eq_norm_sq] at hw
  have hDG : ‖D (G (i u))‖ ≤ q * ‖i u‖ := calc
    ‖D (G (i u))‖ ≤ ‖D‖ * ‖G (i u)‖ := D.le_opNorm _
    _ ≤ ‖D‖ * (‖G‖ * ‖i u‖) := mul_le_mul_of_nonneg_left (G.le_opNorm _) (norm_nonneg _)
    _ = _ := by dsimp only [q]; ring
  have hsq : ‖i u‖^2 ≤ q * ‖i u‖ * ‖D u‖ := calc
    ‖i u‖^2 = ⟪D (G (i u)),D u⟫ := hw.symm
    _ ≤ ‖D (G (i u))‖ * ‖D u‖ := real_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hDG (norm_nonneg _)
  have hi : ‖i u‖ ≤ q * ‖D u‖ := by
    by_cases hz : ‖i u‖ = 0
    · rw [hz]; positivity
    · have hp : 0 < ‖i u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  have heg : ‖u‖^2 ≤ (1+q^2) * ‖D u‖^2 := by
    rw [hgraph]
    have h := sq_le_sq₀ (norm_nonneg (i u)) (mul_nonneg hq (norm_nonneg (D u)))
    have hh := h.mpr hi
    nlinarith
  have heq := hweak f u
  change ⟪D u,D u⟫ = _ at heq
  rw [inner_sub_left,hproj,sub_zero,real_inner_self_eq_norm_sq] at heq
  have hd : ‖D u‖^2 ≤ M * ‖u‖ := by
    rw [heq]
    exact (le_abs_self _).trans (hdual u)
  have hc : 0 ≤ 1+q^2 := by positivity
  have hb := heg.trans (mul_le_mul_of_nonneg_left hd hc)
  change ‖u‖ ≤ (1+q^2)*M
  by_cases hz : ‖u‖ = 0
  · rw [hz]; exact mul_nonneg hc hM
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith
end TamingCompatibility.Variational

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

theorem geometric_dual_energy_inverse
    (D : ∀ p : A.centers, Data J α ht p.val)
    (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source) :
    ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
      ∃ C : ℝ, 0 < C ∧
      (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
        ⟪f-(harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
      (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
      (∀ f M, 0 ≤ M →
        (∀ v, |⟪f,energyInclusion A J α hs ht v⟫| ≤ M * ‖v‖) → ‖G f‖ ≤ C*M) := by
  obtain ⟨-,G,hw,ho,-⟩ := geometric_weak_inverse A J α hs ht D hD
  refine ⟨G,1+(‖weakDelta A J α hs ht‖*‖G‖)^2,by positivity,hw,ho,?_⟩
  intro f M hM hb
  apply Variational.energy_inverse_dual_bound (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (harmonicAnti A J α hs ht) G _ hw ho f M hM hb
  intro u
  exact WithLp.prod_norm_sq_eq_of_L2 u.val
end TamingCompatibility.GeometricHilbert

end

end OAI
