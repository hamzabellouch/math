import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothGeometricInverse

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma harmonic_seminorm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : antiPre A J α hs ht →ₗ[ℝ] E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ‖F h‖ ≤ C * ‖smoothL2 A J α hs ht true f.val‖ := by
  classical
  obtain ⟨hfin,-⟩ := geometric_smooth_inverse A J α hs ht D hD
  let := hfin
  let i : antiPre A J α hs ht →ₗ[ℝ] L2 A J α hs ht true :=
    (smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype
  have hi : Function.Injective i := (smoothL2 A J α hs ht true).injective.comp Subtype.val_injective
  have hl : ∀ k : harmonicAnti A J α hs ht, ∃ a : antiPre A J α hs ht, i a = k.val := by
    intro k
    obtain ⟨a,ha,-⟩ := harmonicAnti_smooth A J α hs ht D hD k.val k.property
    exact ⟨a,ha⟩
  let L := InjectiveLinearLift.lift i hi (harmonicAnti A J α hs ht).subtype hl
  let T : harmonicAnti A J α hs ht →L[ℝ] E := LinearMap.toContinuousLinearMap (F.comp L)
  refine ⟨‖T‖,norm_nonneg T,fun f h hh => ?_⟩
  let k : harmonicAnti A J α hs ht := ⟨(harmonicAnti A J α hs ht).starProjection (i f),
    (harmonicAnti A J α hs ht).starProjection_apply_mem (i f)⟩
  have he : L k = h := hi ((InjectiveLinearLift.lift_spec i hi _ hl k).trans hh.symm)
  have hn : ‖k‖ ≤ ‖i f‖ := (harmonicAnti A J α hs ht).norm_starProjection_apply_le (i f)
  calc
    ‖F h‖ = ‖T k‖ := by change ‖F h‖ = ‖F (L k)‖; rw [he]
    _ ≤ ‖T‖ * ‖k‖ := T.le_opNorm k
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (norm_nonneg T)

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

include hD in

lemma harmonic_schwartz_seminorm_bound
    (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      SchwartzMap.seminorm ℝ k n (F₀ h) ≤ C * ‖smoothL2 A J α hs ht true f.val‖ := by
  classical
  obtain ⟨hfin,-⟩ := geometric_smooth_inverse A J α hs ht D hD
  let := hfin
  let i : antiPre A J α hs ht →ₗ[ℝ] L2 A J α hs ht true :=
    (smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype
  have hi : Function.Injective i := (smoothL2 A J α hs ht true).injective.comp Subtype.val_injective
  have hl : ∀ v : harmonicAnti A J α hs ht, ∃ a : antiPre A J α hs ht, i a = v.val := by
    intro v
    obtain ⟨a,ha,-⟩ := harmonicAnti_smooth A J α hs ht D hD v.val v.property
    exact ⟨a,ha⟩
  let L := InjectiveLinearLift.lift i hi (harmonicAnti A J α hs ht).subtype hl
  let T := F₀.comp L
  let s := (SchwartzMap.seminorm ℝ k n (E := E) (F := F)).comp T
  have hsc : Continuous s :=
    ((schwartz_withSeminorms ℝ E F).continuous_seminorm (k,n)).comp T.continuous_of_finiteDimensional
  obtain ⟨C,hC,hbound⟩ := s.bound_of_continuous_normedSpace hsc
  refine ⟨C,hC.le,fun f h hh => ?_⟩
  let v : harmonicAnti A J α hs ht := ⟨(harmonicAnti A J α hs ht).starProjection (i f),
    (harmonicAnti A J α hs ht).starProjection_apply_mem (i f)⟩
  have he : L v = h := hi ((InjectiveLinearLift.lift_spec i hi _ hl v).trans hh.symm)
  have hn : ‖v‖ ≤ ‖i f‖ := (harmonicAnti A J α hs ht).norm_starProjection_apply_le (i f)
  calc
    SchwartzMap.seminorm ℝ k n (F₀ h) = s v := by change _ = SchwartzMap.seminorm ℝ k n (F₀ (L v)); rw [he]
    _ ≤ C*‖v‖ := hbound v
    _ ≤ _ := mul_le_mul_of_nonneg_left hn hC.le

include hD in
lemma harmonic_schwartz_derivative_bound
    (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ n ≤ N, ∀ v : Fin n → E, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (F₀ h)) x‖ ≤ C * ‖smoothL2 A J α hs ht true f.val‖ := by
  classical
  choose C hC hb using fun n => harmonic_schwartz_seminorm_bound A J α hs ht D hD F₀ 0 n
  refine ⟨∑ n ∈ Finset.range (N+1), C n,Finset.sum_nonneg (fun n _ => hC n),fun f h hh n hn v hv x => ?_⟩
  have hN : C n ≤ ∑ n ∈ Finset.range (N+1), C n :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (by omega))
  have hd : ‖(∂^{v} (F₀ h)) x‖ ≤ SchwartzMap.seminorm ℝ 0 n (F₀ h) := by
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    calc
      _ ≤ ‖iteratedFDeriv ℝ n (F₀ h) x‖ * ∏ i, ‖v i‖ := (iteratedFDeriv ℝ n (F₀ h) x).le_opNorm v
      _ ≤ ‖iteratedFDeriv ℝ n (F₀ h) x‖ * 1 := by
        apply mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ n (F₀ h) x‖ := mul_one _
      _ ≤ _ := (F₀ h).norm_iteratedFDeriv_le_seminorm ℝ n x
  exact hd.trans ((hb n f h hh).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg _)))
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
